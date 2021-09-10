import docker
import os
from app import definitions, utilities, emitter

IMAGE_NAME = "rshariffdeen/cerberus"


def check_image_exist(tool_name):
    client = docker.from_env()
    image_list = client.images.list()
    for image in image_list:
        tag_list = image.tags
        if not tag_list:
            continue
        if IMAGE_NAME not in tag_list[0]:
            continue
        for tag in tag_list:
            if tool_name in tag:
                return True
    return False


def get_tool_image(tool_name):
    client = docker.from_env()
    image_name = IMAGE_NAME + ":" + tool_name
    image = None
    try:
        image = client.images.get(image_name)
    except Exception as ex:
        image = None
    return image


def pull_image(tool_name):
    client = docker.from_env()
    emitter.normal("pulling docker image")
    image = None
    try:
        image, _ = client.images.pull(repository=IMAGE_NAME, tag=tool_name)
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[error] Unable to pull image: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[error] Unable to pull image: unhandled exception")
    return image


def build_tool_image(tool_name):
    client = docker.from_env()
    emitter.normal("building docker image")
    image_name = IMAGE_NAME + ":" + tool_name
    image = None
    dockerfile_path = definitions.DIR_INFRA + "/Dockerfile." + str(tool_name).lower()
    if os.path.isfile(dockerfile_path):
        image = None
        try:
            image, _ = client.images.build(path=definitions.DIR_INFRA, fileobj=dockerfile_path, tag=image_name)
        except docker.errors.BuildError as ex:
            emitter.error(ex)
            utilities.error_exit("[error] Unable to build image: build failed")
        except docker.errors.APIError as exp:
            emitter.error(exp)
            utilities.error_exit("[error] Unable to build image: docker daemon error")
        except Exception as ex:
            emitter.error(ex)
            utilities.error_exit("[error] Unable to build image: unhandled exception")
    else:
        utilities.error_exit("[error] Unable to build image: Dockerfile not found")
    return image


def get_container(tool, benchmark, subject, bug_id, config_id='default'):
    client = docker.from_env()
    image_name = IMAGE_NAME + ":" + tool
    container_name = tool + "-" + benchmark + "-" + subject + "-" + bug_id + "-" + config_id
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


def build_container(tool, benchmark, subject, bug_id, volume_list, config_id='default'):
    client = docker.from_env()
    emitter.normal("\t\t\tbuilding docker container")
    image_name = IMAGE_NAME + ":" + tool
    container_name = tool + "-" + benchmark + "-" + subject + "-" + bug_id + "-" + config_id
    container_id = None
    try:
        container_id = client.containers.run(image_name, detach=True, name=container_name, volumes=volume_list,
                                             tty=True).id
    except docker.errors.ContainerError as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to build container: container exited with a non-zero exit code")
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


def exec_command(container_id, command, workdir="/experiments"):
    client = docker.from_env()
    exit_code = -1
    output = ""
    try:
        container = client.containers.get(container_id)
        exit_code, output = container.exec_run(command, demux=True, workdir=workdir)
    except docker.errors.NotFound as ex:
        emitter.error(ex)
        utilities.error_exit("[error] Unable to find container: container not found: " + str(container_id))
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


def stop_container(container_id):
    client = docker.from_env()
    emitter.normal("\t\t\tstopping docker container")
    try:
        container = client.containers.get(container_id)
        container.stop(timeout=20)
    except docker.errors.APIError as exp:
        emitter.warning(exp)
        emitter.warning("[warning] Unable to remove container: docker daemon error")
    except Exception as ex:
        emitter.warning(ex)
        emitter.warning("[warning] Unable to remove container: unhandled exception")


