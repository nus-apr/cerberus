import json
import os
import random

import docker

from app.core import values, emitter, utilities


def is_image_exist(image_name, tag_name="latest"):
    client = docker.from_env()
    image_list = client.images.list()
    for image in image_list:
        tag_list = image.tags
        if not tag_list:
            continue
        if image_name != tag_list[0].split(":")[0]:
            continue
        for tag in tag_list:
            _, tag_id = tag.split(":")
            if tag_name == tag_id:
                return True
    return False


def pull_image(image_name, tag_name):
    client = docker.from_env()
    emitter.normal("pulling docker image")
    image = None
    try:
        for line in client.api.pull(
            repository=image_name, tag=tag_name, stream=True, decode=True
        ):
            for sub_line in line["status"].split("\n"):
                emitter.build("[docker-api] {}".format(sub_line))
        image = client.images.pull(repository=image_name, tag=tag_name)
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[error] Unable to pull image: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[error] Unable to pull image: unhandled exception")
    return image


def build_image(dockerfile_path, image_name):
    client = docker.from_env()
    emitter.normal("\t\t[benchmark] building docker image")
    context_dir = os.path.abspath(os.path.dirname(dockerfile_path))
    if os.path.isfile(dockerfile_path):
        dockerfilename = dockerfile_path.split("/")[-1]
        try:
            logs = client.api.build(
                path=context_dir, tag=image_name, dockerfile=dockerfilename
            )
            id = None
            for line in logs:
                data = json.loads(line.strip())
                if "stream" in data:
                    for line_stream in data["stream"].split("\n"):
                        emitter.build("\t\t[docker-api] {}".format(line_stream))
                    if "Successfully built" in data["stream"]:
                        id = data["stream"].split(" ")[-1]
            return id
        except docker.errors.BuildError as ex:
            emitter.error(ex)
            utilities.error_exit("[error] Unable to build image: build failed")
        except docker.errors.APIError as exp:
            emitter.error(exp)
            utilities.error_exit("[error] Unable to build image: docker daemon error")
        except Exception as ex:
            print(ex)
            utilities.error_exit("[error] Unable to build image: unhandled exception")
    else:
        utilities.error_exit("[error] Unable to build image: Dockerfile not found")


def build_benchmark_image(image_name):
    benchmark_name = image_name.split("-")[0]
    dockerfile_path = "{}/{}/Dockerfile".format(
        values.dir_benchmark, str(benchmark_name).lower()
    )
    tool_image_id = build_image(dockerfile_path, image_name)
    return tool_image_id


def build_tool_image(tool_name):
    image_name = "{}-tool".format(tool_name)
    dockerfile_path = "{}/Dockerfile.{}".format(
        values.dir_infra, str(tool_name).lower()
    )
    tool_image_id = build_image(dockerfile_path, image_name)
    return tool_image_id


def get_container(container_id):
    client = docker.from_env()
    container = None
    try:
        container = client.containers.get(container_id)
    except docker.errors.NotFound as ex:
        # emitter.error(ex)
        emitter.warning("\t\t[warning] Unable to find container")
    except docker.errors.APIError as exp:
        emitter.error(exp)
        utilities.error_exit("[error] Unable to find container: docker daemon error")
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to find container: unhandled exception")
    return container


def get_container_id(container_name):
    client = docker.from_env()
    container_id = None
    try:
        container_id = client.containers.get(container_name).id[:12]
    except docker.errors.NotFound as ex:
        # emitter.error(ex)
        emitter.warning("\t\t[warning] Unable to find container")
    except docker.errors.APIError as exp:
        emitter.error(exp)
        utilities.error_exit("[error] Unable to find container: docker daemon error")
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to find container: unhandled exception")
    return container_id


def build_container(container_name, volume_list, image_name):
    client = docker.from_env()
    emitter.normal("\t\t\t[benchmark] building docker container")
    container_id = None
    try:
        for local_dir_path in volume_list:
            if local_dir_path == "/var/run/docker.sock":
                continue
            if not os.path.isdir(local_dir_path):
                os.makedirs(local_dir_path)
        emitter.debug(
            "Container runtime is {}".format("nvidia" if values.use_gpu else "runc")
        )
        container = client.containers.run(
            image_name,
            detach=True,
            name=container_name,
            volumes=volume_list,
            privileged=True,
            mem_limit="30g",
            tty=True,
            runtime="nvidia" if values.use_gpu else "runc",
        )
        container_id = container.id
    except docker.errors.ContainerError as ex:
        emitter.error(ex)
        utilities.error_exit(
            "[error] Unable to build container: container exited with a non-zero exit code"
        )
    except docker.errors.ImageNotFound as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to build container: image not found")
    except docker.errors.APIError as exp:
        emitter.error(exp)
        utilities.error_exit("[error] Unable to build container: docker daemon error")
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to build container: unhandled exception")
    return container_id[:12]


def exec_command(container_id, command, workdir="/experiment", env=dict()):
    client = docker.from_env()
    exit_code = -1
    output = ""
    try:
        container = client.containers.get(container_id)
        command = command.encode().decode("ascii", "ignore")
        print_command = "[{}] {}".format(workdir, command)
        emitter.docker_command(print_command)
        exit_code, output = container.exec_run(
            command,
            privileged=True,
            demux=True,
            workdir=workdir,
            tty=True,
            environment=env,
        )
        if output is not None:
            for stream in output:
                if stream is None:
                    continue
                for line in stream.decode("ascii", "ignore").split("\n"):
                    if line != "":
                        emitter.debug(line)
    except docker.errors.NotFound as ex:
        emitter.error(ex)
        utilities.error_exit(
            "[error] Unable to find container: container not found: {}".format(
                container_id
            )
        )
    except docker.errors.APIError as exp:
        emitter.error(exp)
        utilities.error_exit("[error] Unable to find container: docker daemon error")
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to find container: unhandled exception")
    return exit_code, output


def remove_container(container_id):
    client = docker.from_env()
    emitter.normal("\t\t\tremoving docker container")
    try:
        container = client.containers.get(container_id)
        container.remove(force=True)
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[warning] Unable to remove container: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[warning] Unable to remove container: unhandled exception")


def start_container(container_id):
    client = docker.from_env()
    emitter.normal("\t\t\tstarting docker container {}".format(container_id))
    try:
        container = client.containers.get(container_id)
        container.start()
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[warning] Unable to stop container: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[warning] Unable to stop container: unhandled exception")


def stop_container(container_id):
    client = docker.from_env()
    emitter.normal("\t\t\tstopping docker container")
    try:
        container = client.containers.get(container_id)
        container.stop(timeout=20)
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[warning] Unable to stop container: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[warning] Unable to stop container: unhandled exception")


def is_file(container_id, file_path):
    exist_command = "test -f {}".format(file_path)
    return exec_command(container_id, exist_command)[0] == 0


def is_dir(container_id, dir_path):
    exist_command = "test -d {}".format(dir_path)
    return exec_command(container_id, exist_command)[0] == 0


def is_file_empty(container_id, file_path):
    exist_command = "[ -s {} ]".format(file_path)
    return exec_command(container_id, exist_command)[0] != 0


def fix_permissions(container_id, dir_path):
    permission_command = "chmod -R g+w  {}".format(dir_path)
    return exec_command(container_id, permission_command)


def list_dir(container_id, dir_path):
    exist_command = "ls {}".format(dir_path)
    _, output = exec_command(container_id, exist_command)
    stdout, stderr = output
    file_list = []
    if stdout:
        dir_list = stdout.decode("utf-8").split()
        for o in dir_list:
            file_list.append(o.strip().replace("\n", ""))
    return file_list


def copy_file_from_container(container_id, from_path, to_path):
    copy_command = "docker cp {}:{} {}".format(container_id, from_path, to_path)
    utilities.execute_command(copy_command)


def copy_file_to_container(container_id, from_path, to_path):
    copy_command = "docker cp {} {}:{}".format(from_path, container_id, to_path)
    utilities.execute_command(copy_command)


def write_file(container_id, file_path, content):
    tmp_file_path = os.path.join(
        "/tmp", "write-file-{}".format(random.randint(0, 1000000))
    )
    with open(tmp_file_path, "w") as f:
        for line in content:
            f.write(line)
    copy_command = "docker cp {} {}:{}".format(tmp_file_path, container_id, file_path)
    utilities.execute_command(copy_command)
    os.remove(tmp_file_path)


def read_file(container_id, file_path, encoding="utf-8"):
    tmp_file_path = os.path.join(
        "/tmp", "container-file-{}".format(random.randint(0, 1000000))
    )
    copy_command = "docker cp {}:{} {}".format(container_id, file_path, tmp_file_path)
    utilities.execute_command(copy_command)
    with open(tmp_file_path, "r", encoding=encoding) as f:
        file_content = f.readlines()
    os.remove(tmp_file_path)
    return file_content


def append_file(container_id, file_path, content):
    tmp_file_path = os.path.join(
        "/tmp", "append-file-{}".format(random.randint(0, 1000000))
    )
    copy_command = "docker cp {}:{} {}".format(container_id, file_path, tmp_file_path)
    utilities.execute_command(copy_command)
    with open(tmp_file_path, "a") as f:
        for line in content:
            f.write(line)
    copy_command = "docker cp {} {}:{}".format(tmp_file_path, container_id, file_path)
    utilities.execute_command(copy_command)
    os.remove(tmp_file_path)
