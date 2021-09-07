import docker
import os
from app import definitions, utilities, emitter

IMAGE_PREFIX = "rshariffdeen/cerberus:"


def check_image_exist(tool_name):
    client = docker.from_env()
    image_list = client.images.list()
    for image in image_list:
        tag_list = image.tags
        for tag in tag_list:
            if tool_name in tag:
                return True
    return False


def get_tool_image(tool_name):
    client = docker.from_env()
    image_name = IMAGE_PREFIX + ":" + tool_name
    image = None
    try:
        image = client.images.get(image_name)
    except Exception as ex:
        image = None
    return image


def build_tool_image(tool_name):
    client = docker.from_env()
    image_name = IMAGE_PREFIX + ":" + tool_name
    image = None
    dockerfile_path = definitions.DIR_INFRA + "/Dockerfile." + str(tool_name).lower()
    if os.path.isfile(dockerfile_path):
        image = None
        try:
            image, _ = client.images.build(path=definitions.DIR_INFRA, fileobj=dockerfile_path, tag=image_name)
        except docker.errors.BuildError as ex:
            utilities.error_exit("[error] Unable to build image: build failed")
        except docker.errors.APIError as exp:
            utilities.error_exit("[error] Unable to build container: docker daemon error")
        except Exception as ex:
            utilities.error_exit("[error] Unable to build image: unhandled exception")
    else:
        utilities.error_exit("[error] Unable to build image: Dockerfile not found")
    return image


def build_container(tool, benchmark, subject, bug_id, config_id='default'):
    client = docker.from_env()
    image_name = IMAGE_PREFIX + ":" + tool
    container_name = tool + "-" + benchmark + "-" + subject + "-" + bug_id + "-" + config_id
    container_id = None
    try:
        container_id = client.containers.run(image_name, detach=True, name=container_name).id
    except docker.errors.ContainerError as ex:
        utilities.error_exit("[error] Unable to build container: container exited with a non-zero exit code")
    except docker.errors.ImageNotFound as ex:
        utilities.error_exit("[error] Unable to build container: image not found")
    except docker.errors.APIError as exp:
        utilities.error_exit("[error] Unable to build container: docker daemon error")
    except Exception as ex:
        utilities.error_exit("[error] Unable to build container: unhandled exception")
    return container_id


def exec_command(container_id, command):
    client = docker.from_env()
    try:
        container = client.containers.get(container_id)
        container.exec_run(command, stdout=False, stderr=False)
    except docker.errors.NotFound as ex:
        utilities.error_exit("[error] Unable to find container: container not found: " + str(container_id))
    except docker.errors.APIError as exp:
        utilities.error_exit("[error] Unable to find container: docker daemon error")
    except Exception as ex:
        utilities.error_exit("[error] Unable to find container: unhandled exception")
    return container


def remove_container(container_id):
    client = docker.from_env()
    try:
        container = client.containers.get(container_id)
        container.remove(force=True)
    except docker.errors.APIError as exp:
        emitter.warning("[warning] Unable to remove container: docker daemon error")
    except Exception as ex:
        emitter.warning("[warning] Unable to remove container: unhandled exception")


def stop_container(container_id):
    client = docker.from_env()
    try:
        container = client.containers.get(container_id)
        container.stop(timeout=20)
    except docker.errors.APIError as exp:
        emitter.warning("[warning] Unable to remove container: docker daemon error")
    except Exception as ex:
        emitter.warning("[warning] Unable to remove container: unhandled exception")


