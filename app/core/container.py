import json
import os
import random
import traceback
from typing import Any
from typing import cast
from typing import Dict
from typing import List
from typing import Optional
from typing import Sequence
from typing import Set
from typing import Tuple
from typing import Union

import docker  # type: ignore
import semver

from app.core import definitions
from app.core import emitter
from app.core import utilities
from app.core import values

cached_client = None
image_map = {}


def get_client() -> docker.DockerClient:
    """
    Utility method to track all client usages.
    Pulls the images at the current state to allow for less network calls.
    """
    global cached_client
    global image_map
    if not cached_client:
        cached_client = docker.DockerClient(
            base_url=values.docker_host,
            version="1.41",
            timeout=900,
            # user_agent="Cerberus Agent",
            # use_ssh_client=True,
        )
        try:
            image_cache = cached_client.images.list()
        except IOError as ex:
            emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection was unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        for image in image_cache:
            tag_list = image.tags  # type: ignore
            if not tag_list:
                continue
            for image_tag in tag_list:
                image_map[image_tag] = image
        emitter.debug("Image map: {}".format(image_map))
    return cached_client


def image_exists(image_name: str, tag_name: str = "latest") -> bool:
    _ = get_client()
    emitter.debug("Checking for image {} with tag {}".format(image_name, tag_name))
    if f"{image_name}:{tag_name}" not in image_map:
        return False
    return True


def get_image(image_name: str, tag_name: str = "latest") -> Any:
    _ = get_client()
    if f"{image_name}:{tag_name}" not in image_map:
        return None
    return image_map[f"{image_name}:{tag_name}"]


def pull_image(image_name: str, tag_name: str) -> Any:
    client = get_client()
    emitter.normal(
        "\t\t[framework] pulling docker image {}:{}".format(image_name, tag_name)
    )
    image = None
    try:
        for line in client.api.pull(
            repository=image_name, tag=tag_name, stream=True, decode=True
        ):
            for sub_line in line["status"].split("\n"):
                emitter.build("[docker-api] {}".format(sub_line))
        image = client.images.pull(repository=image_name, tag=tag_name)
        image_map[image_name] = (image.tags[1:], image)
    except docker.errors.APIError as exp:  # type: ignore
        emitter.warning(
            "\t[docker-api][warning] unable to pull image: docker daemon error"
        )
        emitter.debug(exp)
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "\t[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[error] unable to pull image: unhandled exception")
    return image


def build_image(dockerfile_path: str, image_name: str) -> str:
    client = get_client()
    emitter.normal("\t\t[framework] building docker image {}".format(image_name))
    context_dir = os.path.abspath(os.path.dirname(dockerfile_path))
    if os.path.isfile(dockerfile_path):
        dockerfilename = os.path.relpath(dockerfile_path, context_dir)
        emitter.debug(
            f"Context directory is {context_dir} with image file {dockerfilename}"
        )
        try:
            logs = client.api.build(
                path=context_dir,
                tag=image_name,
                dockerfile=dockerfilename,
                decode=True,
                rm=not values.debug,
            )
            id: str = "NONE"
            for line in logs:
                # emitter.debug(line)
                if "stream" in line:
                    for line_stream in line["stream"].split("\n"):
                        emitter.build("\t\t[docker-api] {}".format(line_stream))
                    if "Successfully built" in line["stream"]:
                        id = line["stream"].split(" ")[-1]
            if id == "NONE":
                utilities.error_exit(
                    "[error] Image was not build successfully. Please check whether the file builds outside of Cerberus"
                )
            image = client.images.get(image_name)
            if ":" not in image_name:
                image_name += ":latest"
            image_map[image_name] = image
            return id
        except docker.errors.BuildError as ex:  # type: ignore
            emitter.error(ex)
            utilities.error_exit("[error] unable to build image: build failed")
        except docker.errors.APIError as exp:  # type: ignore
            emitter.error(exp)
            utilities.error_exit("[error] unable to build image: docker daemon error")
        except IOError as ex:
            emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            emitter.error(ex)
            utilities.error_exit("[error] unable to build image: unhandled exception")
    else:
        utilities.error_exit("[error] unable to build image: Dockerfile not found")


def build_benchmark_image(image_name: str) -> Optional[str]:
    benchmark_name = image_name.split("-")[0]
    dockerfile_path = os.path.join(
        values.dir_benchmark, benchmark_name.lower(), "Dockerfile"
    )
    tool_image_id = build_image(dockerfile_path, image_name)
    return tool_image_id


def build_tool_image(tool_name: str) -> Optional[str]:
    image_name = "{}-tool".format(tool_name)
    dockerfile_path = "{}/Dockerfile.{}".format(
        values.dir_infra, str(tool_name).lower()
    )
    tool_image_id = build_image(dockerfile_path, image_name)
    return tool_image_id


def get_container(container_id: str) -> Any:
    client = get_client()
    container = None
    try:
        container = client.containers.get(container_id)
    except docker.errors.NotFound as ex:  # type: ignore
        if values.debug:
            emitter.error(f"\t{ex}")
        emitter.warning("\t[warning] Unable to find container")
    except docker.errors.APIError as exp:  # type: ignore
        emitter.error(f"\t{exp}")
        utilities.error_exit("[error] unable to find container: docker daemon error")
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.error(f"\t{ex}")
        utilities.error_exit("[error] unable to find container: unhandled exception")
    return container


def get_container_id(container_name: str, ignore_not_found: bool) -> Optional[str]:
    client = get_client()
    container_id = None
    try:
        container_id = client.containers.get(container_name).id[:12]  # type: ignore
    except docker.errors.NotFound as ex:  # type: ignore
        if not ignore_not_found:
            if values.debug:
                emitter.error(f"\t\t[debug] {ex}")
            emitter.warning("\t\t[warning] unable to find container")
    except docker.errors.APIError as exp:  # type: ignore
        emitter.error(exp)
        utilities.error_exit("[error] unable to find container: docker daemon error")
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit("[error] unable to find container: unhandled exception")
    return container_id


def get_container_stats(
    container_id: str,
) -> Optional[Dict[str, Any]]:
    container = get_container(container_id)
    try:
        container_stats = container.stats(stream=False)
        return cast(Dict[str, Any], container_stats)
    except docker.errors.NotFound as ex:  # type: ignore
        emitter.error(ex)
        utilities.error_exit(
            "\t\t\t[error] unable to find container: container not found: {}".format(
                container_id
            )
        )
    except docker.errors.APIError as exp:  # type: ignore
        emitter.error(exp)
        utilities.error_exit(
            "\t\t\t[error] unable to get stats of the container with id: {0}: docker daemon error".format(
                container_id
            )
        )
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit(
            "\t\t\t[error] unable to get stats of the container with id: {0}: unhandled exception".format(
                container_id
            )
        )

    return None


def build_container(
    container_name: str,
    volume_list: Dict[str, Dict[str, str]],
    image_name: str,
    cpu: List[str],
    gpu: List[str],
    container_config_dict: Optional[Dict[Any, Any]] = None,
    disable_network: bool = False,
) -> Optional[str]:
    client = get_client()
    emitter.normal("\t\t[framework] building docker container: ")
    emitter.normal("\t\t\t container image: {}".format(image_name))
    emitter.normal("\t\t\t container name: {}".format(container_name))
    try:
        for local_dir_path in volume_list:
            if local_dir_path == "/var/run/docker.sock":
                continue
            os.makedirs(local_dir_path, exist_ok=True)

        container_run_args: Dict[str, Any] = {
            "detach": True,
            "entrypoint": "/bin/bash",
            "name": container_name,
            "volumes": volume_list,
            "privileged": True,
            "cpuset_cpus": ",".join(cpu),
            "tty": True,
            "environment": {
                "EXPERIMENT_DIR": values.container_base_experiment,
                "METADATA_FILE": os.path.join(
                    values.container_base_experiment, "meta-data.json"
                ),
            },
        }

        if disable_network:
            container_run_args["network_mode"] = None
            container_run_args["network_disabled"] = True

        if values.use_gpu and len(gpu) > 0:
            # Check that the docker version has DeviceRequests
            if docker.__version__ and semver.compare(docker.__version__, "4.3.0") >= 0:
                container_run_args["device_requests"] = [
                    docker.types.DeviceRequest(  # type: ignore
                        device_ids=gpu,
                        capabilities=[["gpu"]],
                    )
                ]
            else:
                container_run_args["runtime"] = "nvidia"

            # Ensures that pytorch and tf will see only the required GPUs
            # nvidia-smi does not visualize this change
            # therefore other methods are needed
            # For example
            # python -c 'import torch; print(torch.cuda.device_count())'
            container_run_args["environment"]["NVIDIA_VISIBLE_DEVICES"] = ",".join(gpu)
            container_run_args["environment"]["CUDA_VISIBLE_DEVICES"] = ",".join(gpu)

        default_mem_limit = "32g"
        if container_config_dict:
            container_run_args["mem_limit"] = container_config_dict.get(
                definitions.KEY_CONTAINER_MEM_LIMIT, default_mem_limit
            )

        else:
            container_run_args["mem_limit"] = default_mem_limit

        emitter.debug(
            "\t\t\t[framework] container {} is built with the following args {}".format(
                container_name, container_run_args
            )
        )
        container = client.containers.run(image_name, **container_run_args)
        container_id = container.id  # type: ignore
        shortened_id: str = container_id[:12]  # type: ignore
        container_list.add(shortened_id)
        return shortened_id
    except docker.errors.ContainerError as ex:  # type: ignore
        emitter.error(ex)
        utilities.error_exit(
            "\t\t\t[error] unable to build container: container exited with a non-zero exit code"
        )
    except docker.errors.ImageNotFound as ex:  # type: ignore
        emitter.error(ex)
        utilities.error_exit("\t\t\t[error] unable to build container: image not found")
    except docker.errors.APIError as exp:  # type: ignore
        emitter.error(exp)
        utilities.error_exit(
            "\t\t\t[error] unable to build container: docker daemon error"
        )
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit(
            "\t\t\t[error] unable to build container: unhandled exception"
        )
    return None


def exec_command(
    container_id: str,
    command: str,
    workdir: str = values.container_base_experiment,
    env: Dict[str, str] = dict(),
) -> Tuple[int, Optional[Tuple[Optional[bytes], Optional[bytes]]]]:
    client = get_client()
    exit_code: int
    output: Optional[Tuple[Optional[bytes], Optional[bytes]]]
    exit_code = -1
    output = None
    try:
        container = client.containers.get(container_id)
        command = command.encode().decode("ascii", "ignore")
        print_command = "({}) {}".format(workdir, command)
        if env:
            print_command += f""" ({' '.join(f"{k}={v}" for k, v in env.items())})"""
        emitter.docker_command(print_command)
        exit_code, output = container.exec_run(  # type: ignore
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
                if values.debug:
                    for line in stream.decode("ascii", "ignore").split("\n"):
                        if line != "":
                            emitter.debug(line)
    except docker.errors.NotFound as ex:  # type: ignore
        emitter.error(ex)
        utilities.error_exit(
            "(error) Unable to find container: container not found: {}".format(
                container_id
            )
        )
    except docker.errors.APIError as exp:  # type: ignore
        emitter.error(exp)
        utilities.error_exit(
            "\t\t\t[error] unable to find container: docker daemon error"
        )
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )

    except Exception as ex:
        emitter.error(ex)
        utilities.error_exit(
            "\t\t\t[error] unable to find container: unhandled exception"
        )
    return exit_code, output


def remove_container(container_id: str) -> None:
    client = get_client()
    emitter.normal("\t\t\t[framework] removing docker container")
    try:
        container = client.containers.get(container_id)
        container.remove(force=True)  # type: ignore
    except docker.errors.APIError as exp:  # type: ignore
        emitter.warning(exp)
        emitter.warning("[warning] unable to remove container: docker daemon error")
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[warning] unable to remove container: unhandled exception")


container_list: Set[str] = set()


def clean_containers() -> None:
    pass
    # emitter.debug("Removing containers")
    # emitter.debug(container_list)
    # client = get_client()
    # for container_id in list(container_list):
    #     try:
    #         container = client.containers.get(container_id)
    #         container.stop(timeout=5)  # type: ignore
    #     except Exception as e:  # type: ignore
    #         emitter.debug(e)
    #         emitter.debug(traceback.format_tb(e.__traceback__))
    #         pass


def start_container(container_id: str) -> None:
    client = get_client()
    emitter.normal(
        "\t\t\t[framework] starting docker container {}".format(container_id)
    )
    try:
        container = client.containers.get(container_id)
        container.start()  # type: ignore
        container_list.add(container_id)
    except docker.errors.APIError as exp:  # type: ignore
        emitter.warning(exp)
        emitter.warning(
            "\t\t\t[framework] unable to stop container: docker daemon error"
        )
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning(
            "\t\t\t[framework] unable to stop container: unhandled exception"
        )


def stop_container(container_id: str, timeout: int = 120) -> None:
    client = get_client()
    emitter.normal(
        "\t\t\t[framework] stopping docker container {}".format(container_id)
    )
    try:
        container = client.containers.get(container_id)
        container.stop(timeout=timeout)  # type: ignore
        if container_id in container_list:
            container_list.remove(container_id)
    except docker.errors.APIError as exp:  # type: ignore
        emitter.warning(exp)
        emitter.warning(
            "\t\t\t[framework] unable to stop container: docker daemon error"
        )
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning(
            "\t\t\t[framework] unable to stop container: unhandled exception"
        )


def kill_container(container_id: str, ignore_errors: bool = False) -> None:
    client = get_client()
    emitter.normal("\t\t\t[framework] killing docker container {}".format(container_id))
    try:
        container = client.containers.get(container_id)
        container.kill()  # type: ignore
        if container_id in container_list:
            container_list.remove(container_id)
    except docker.errors.APIError as exp:  # type: ignore
        if not ignore_errors:
            emitter.warning(exp)
            emitter.warning(
                "\t\t\t[framework] unable to kill container: docker daemon error"
            )
    except IOError as ex:
        emitter.error(ex)
        raise RuntimeError(
            "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
        )
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning(
            "\t\t\t[framework] unable to kill container: unhandled exception"
        )


def create_running_container(
    volume_list: Dict[str, Dict[str, str]],
    image_name: str,
    container_name: str,
    cpu: List[str],
    gpu: List[str],
    container_config_info: Dict[str, Any],
    source_logs: str,
    target_logs: str,
) -> str:
    image_name = image_name.lower()
    emitter.information(
        "\t\t[framework] Creating running container with image {}".format(image_name)
    )
    container_id = get_container_id(container_name, ignore_not_found=True)
    if container_id:
        kill_container(container_id, ignore_errors=True)
        remove_container(container_id)

    if not image_exists(image_name):
        utilities.error_exit("Image should be constructed by now!")

    extract_experiment_logs(
        image_name,
        container_name,
        cpu,
        gpu,
        container_config_info,
        source_logs,
        target_logs,
    )

    emitter.information("\t\t[framework] building main container for experiment")
    is_network_enabled = True
    if container_config_info:
        is_network_enabled = container_config_info.get(
            definitions.KEY_CONTAINER_ENABLE_NETWORK, True
        )

    container_id = build_container(
        container_name,
        volume_list,
        image_name,
        cpu,
        gpu,
        container_config_info,
        not is_network_enabled,
    )
    if not container_id:
        utilities.error_exit("Container was not created successfully")
    return container_id


def extract_experiment_logs(
    image_name: str,
    container_name: str,
    cpu: List[str],
    gpu: List[str],
    container_config_info: Dict[str, Any],
    source_logs: str,
    target_logs: str,
) -> None:
    # Need to copy the logs from benchmark setup before instantiating the running container
    emitter.information(
        "\t\t[framework] building temporary container for log extraction"
    )

    tmp_container_id = get_container_id(container_name, ignore_not_found=True)

    if not tmp_container_id:
        tmp_container_id = build_container(
            container_name, dict(), image_name, cpu, gpu, container_config_info
        )

    if not tmp_container_id:
        utilities.error_exit("Could not create temporary container")
    else:
        copy_file_from_container(tmp_container_id, source_logs, target_logs)
        if values.runs:
            stop_container(tmp_container_id, 5)
            remove_container(tmp_container_id)


def is_file(container_id: str, file_path: str) -> bool:
    exist_command = "test -f {}".format(file_path)
    return exec_command(container_id, exist_command)[0] == 0


def is_dir(container_id: str, dir_path: str) -> bool:
    exist_command = "test -d {}".format(dir_path)
    return exec_command(container_id, exist_command)[0] == 0


def is_file_empty(container_id: str, file_path: str) -> bool:
    exist_command = "[ -s {} ]".format(file_path)
    return exec_command(container_id, exist_command)[0] != 0


def fix_permissions(
    container_id: str, dir_path: str
) -> Tuple[int, Optional[Tuple[Optional[bytes], Optional[bytes]]]]:
    permission_command = "chmod -R g+w  {}".format(dir_path)
    return exec_command(container_id, permission_command)


def list_dir(
    container_id: str, dir_path: str, regex: Optional[str] = None
) -> List[str]:
    if not regex:
        regex = "*"
    exist_command = 'find {} -name "{}"'.format(dir_path, regex)
    _, output = exec_command(container_id, exist_command)
    file_list = []
    if output:
        stdout, stderr = output
        if stdout:
            dir_list = stdout.decode("utf-8").split()
            for o in dir_list:
                file_list.append(o.strip().replace("\n", ""))
    return file_list


def copy_file_from_container(container_id: str, from_path: str, to_path: str) -> int:
    copy_command = "docker -H {} cp {}:{} {}".format(
        values.docker_host, container_id, from_path, to_path
    )
    return utilities.execute_command(copy_command)


def copy_file_to_container(container_id: str, from_path: str, to_path: str) -> int:
    copy_command = "docker -H {} cp {} {}:{}".format(
        values.docker_host, from_path, container_id, to_path
    )
    return utilities.execute_command(copy_command)


def write_file(container_id: str, file_path: str, content: Sequence[str]) -> None:
    tmp_file_path = os.path.join(
        "/tmp", "write-file-{}".format(random.randint(0, 1000000))
    )
    with open(tmp_file_path, "w") as f:
        for line in content:
            f.write(line)
    copy_command = "docker -H {} cp {} {}:{}".format(
        values.docker_host, tmp_file_path, container_id, file_path
    )
    utilities.execute_command(copy_command)
    os.remove(tmp_file_path)


def get_file_object(container_id: str, file_path: str, encoding: str = "utf-8") -> Any:
    tmp_file_path = os.path.join(
        "/tmp", "container-file-{}".format(random.randint(0, 1000000))
    )
    copy_command = "docker -H {} cp {}:{} {}".format(
        values.docker_host, container_id, file_path, tmp_file_path
    )
    utilities.execute_command(copy_command)
    f_obj = open(tmp_file_path, "r", encoding=encoding)
    return f_obj


def read_file(container_id: str, file_path: str, encoding: str = "utf-8") -> List[str]:
    tmp_file_path = os.path.join(
        "/tmp", "container-file-{}".format(random.randint(0, 1000000))
    )
    copy_command = "docker -H {} cp {}:{} {}".format(
        values.docker_host, container_id, file_path, tmp_file_path
    )
    utilities.execute_command(copy_command)
    with open(tmp_file_path, "r", encoding=encoding) as f:
        file_content = f.readlines()
    os.remove(tmp_file_path)
    return file_content


def append_file(container_id: str, file_path: str, content: Sequence[str]) -> None:
    tmp_file_path = os.path.join(
        "/tmp", "append-file-{}".format(random.randint(0, 1000000))
    )
    copy_command = "docker -H {} cp {}:{} {}".format(
        values.docker_host, container_id, file_path, tmp_file_path
    )
    utilities.execute_command(copy_command)
    with open(tmp_file_path, "a") as f:
        for line in content:
            f.write(line)
    copy_command = "docker -H {} cp {} {}:{}".format(
        values.docker_host, tmp_file_path, container_id, file_path
    )
    utilities.execute_command(copy_command)
    os.remove(tmp_file_path)
