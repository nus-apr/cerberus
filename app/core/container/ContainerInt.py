import json
import os
from typing import Optional, Dict, Any, Tuple

import docker


class ContainerInt:

    def __init__(self, docker_host):
        self.docker_host = docker_host
        self.client = docker.DockerClient(
            base_url=self.docker_host,
            version="1.41",
            timeout=300
            # user_agent="Cerberus Agent",
            # use_ssh_client=True,
        )

    # image
    def pull_image(self, image_name: str, tag_name: str):
        # emitter.normal(
        #     "\t\t[framework] pulling docker image {}:{}".format(image_name, tag_name)
        # )
        image = None
        try:
            # for line in self.client.api.pull(repository=image_name, tag=tag_name, stream=True, decode=True):
            # for sub_line in line["status"].split("\n"):
            # emitter.build("[docker-api] {}".format(sub_line))
            image = self.client.images.pull(repository=image_name, tag=tag_name)
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.warning(exp)
            # emitter.warning("[error] unable to pull image: docker daemon error")
            pass
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            # emitter.warning(ex)
            # emitter.warning("[error] unable to pull image: unhandled exception")
            pass
        return image

    def build_image(self, dockerfile_path: str, image_name: str):
        # emitter.normal("\t\t[framework] building docker image {}".format(image_name))
        context_dir = os.path.abspath(os.path.dirname(dockerfile_path))
        if os.path.isfile(dockerfile_path):
            dockerfilename = dockerfile_path.split("/")[-1]
            try:
                logs = self.client.api.build(
                    path=context_dir,
                    tag=image_name,
                    dockerfile=dockerfilename,
                    rm=True,
                )
                id = None
                for line in logs:
                    # emitter.debug(line)
                    data = json.loads(line.strip())
                    if "stream" in data:
                        # for line_stream in data["stream"].split("\n"):
                        #     emitter.build("\t\t[docker-api] {}".format(line_stream))
                        if "Successfully built" in data["stream"]:
                            id = data["stream"].split(" ")[-1]
                return id
            except docker.errors.BuildError as ex:  # type: ignore
                pass
                # emitter.error(ex)
                # utilities.error_exit("[error] unable to build image: build failed")
            except docker.errors.APIError as exp:  # type: ignore
                pass
                # emitter.error(exp)
                # utilities.error_exit("[error] unable to build image: docker daemon error")
            except IOError as ex:
                # emitter.error(ex)
                raise RuntimeError(
                    "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
                )
            except Exception as ex:
                pass
                # emitter.error(ex)
                # utilities.error_exit("[error] unable to build image: unhandled exception")
        else:
            pass
            # utilities.error_exit("[error] unable to build image: Dockerfile not found")

    def image_exists(self, image_name: str, tag_name="latest"):
        try:
            image_list = self.client.images.list()
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        for image in image_list:
            tag_list = image.tags  # type: ignore
            if not tag_list:
                continue
            if image_name != tag_list[0].split(":")[0]:
                continue
            for tag in tag_list:
                _, tag_id = tag.split(":")
                if tag_name == tag_id:
                    return True
        return False

    def get_image(self, image_name: str, tag_name="latest"):
        try:
            image_list = self.client.images.list()
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )

        for image in image_list:
            tag_list = image.tags  # type: ignore
            if not tag_list:
                continue
            if image_name != tag_list[0].split(":")[0]:
                continue
            for tag in tag_list:
                _, tag_id = tag.split(":")
                if tag_name == tag_id:
                    return image
        return None


    # def build_benchmark_image(self, image_name: str) -> Optional[str]:
    #     benchmark_name = image_name.split("-")[0]
    #     dockerfile_path = "{}/{}/Dockerfile".format(
    #         values.dir_benchmark, benchmark_name.lower()
    #     )
    #     tool_image_id = self.build_image(dockerfile_path, image_name)
    #     return tool_image_id

    # def build_tool_image(tool_name: str) -> Optional[str]:
    #     image_name = "{}-tool".format(tool_name)
    #     dockerfile_path = "{}/Dockerfile.{}".format(
    #         values.dir_infra, str(tool_name).lower()
    #     )
    #     tool_image_id = build_image(dockerfile_path, image_name)
    #     return tool_image_id

    # container
    def build_container(
            self,
            container_name: str,
            volume_list,
            image_name: str,
            cpu: str,
            container_config_dict: Optional[Dict[Any, Any]] = None,
    ) -> Optional[str]:
        # emitter.normal(
        #     "\t\t[framework] building docker container based on image {} with name {}".format(
        #         image_name, container_name
        #     )
        # )
        try:
            for local_dir_path in volume_list:
                if local_dir_path == "/var/run/docker.sock":
                    continue
                os.makedirs(local_dir_path, exist_ok=True)

            container_run_args = {
                "detach": True,
                "name": container_name,
                "volumes": volume_list,
                "privileged": True,
                "cpuset_cpus": cpu,
                "tty": True,
                "runtime": "nvidia" if values.use_gpu else "runc",
            }

            default_mem_limit = "32g"
            if container_config_dict:
                container_run_args["mem_limit"] = container_config_dict.get(
                    definitions.KEY_CONTAINER_MEM_LIMIT, default_mem_limit
                )

                if not container_config_dict.get(
                        definitions.KEY_CONTAINER_ENABLE_NETWORK, True
                ):
                    container_run_args["network_mode"] = None
                    container_run_args["network_disabled"] = False
            else:
                container_run_args["mem_limit"] = default_mem_limit

            # emitter.debug(
            #     "\t\t\t[framework] container {} is build with the following args {}".format(
            #         container_name, container_run_args
            #     )
            # )
            container = self.client.containers.run(image_name, **container_run_args)
            container_id = container.id  # type: ignore
            return container_id[:12]  # type: ignore
        except docker.errors.ContainerError as ex:  # type: ignore
            # emitter.error(ex)
            # utilities.error_exit(
            #     "\t\t\t[error] unable to build container: container exited with a non-zero exit code"
            # )
            pass
        except docker.errors.ImageNotFound as ex:  # type: ignore
            # emitter.error(ex)
            # utilities.error_exit("\t\t\t[error] unable to build container: image not found")
            pass
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.error(exp)
            # utilities.error_exit(
            #     "\t\t\t[error] unable to build container: docker daemon error"
            # )
            pass
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            # emitter.error(ex)
            # utilities.error_exit(
            #     "\t\t\t[error] unable to build container: unhandled exception"
            # )
            pass
        return None

    def get_container(self, container_id: str):
        container = None
        try:
            container = self.client.containers.get(container_id)
        except docker.errors.NotFound as ex:  # type: ignore
            pass
            # if values.debug:
            #     emitter.error(f"\t{ex}")
            # emitter.warning("\t[warning] Unable to find container")
        except docker.errors.APIError as exp:  # type: ignore
            pass
            # emitter.error(f"\t{exp}")
            # utilities.error_exit("[error] unable to find container: docker daemon error")
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            pass
        #     emitter.error(f"\t{ex}")
        #     utilities.error_exit("[error] unable to find container: unhandled exception")
        return container

    def get_container_id(self, container_name: str) -> Optional[str]:
        container_id = None
        try:
            container_id = self.client.containers.get(container_name).id[:12]  # type: ignore
        except docker.errors.NotFound as ex:  # type: ignore
            pass
            # if values.debug:
            #     emitter.error(f"\t\t{ex}")
            # emitter.warning("\t\t[warning] unable to find container")
        except docker.errors.APIError as exp:  # type: ignore
            pass
            # emitter.error(exp)
            # utilities.error_exit("[error] unable to find container: docker daemon error")
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            pass
            # emitter.error(ex)
            # utilities.error_exit("[error] unable to find container: unhandled exception")
        return container_id

    def get_container_stats(self, container_id: str):
        container = self.get_container(container_id)
        try:
            container_stats = container.stats(stream=False)
            return container_stats
        except docker.errors.NotFound as ex:  # type: ignore
            pass
            # emitter.error(ex)
            # utilities.error_exit("\t\t\t[error] unable to find container: container not found: {}".format(container_id))
        except docker.errors.APIError as exp:  # type: ignore
            pass
            # emitter.error(exp)
            # utilities.error_exit("\t\t\t[error] unable to get stats of the container with id: {0}: docker daemon error".format(container_id))
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            pass
            # emitter.error(ex)
            # utilities.error_exit("\t\t\t[error] unable to get stats of the container with id: {0}: unhandled exception".format(container_id))

        return None

    def exec_command(
            self,
            container_id: str,
            command: str,
            workdir="/experiment",
            env: Dict[str, str] = dict()
    ) -> Tuple[int, Optional[Tuple[Optional[bytes], Optional[bytes]]]]:
        exit_code: int
        output: Optional[Tuple[Optional[bytes], Optional[bytes]]]
        exit_code = -1
        output = None
        try:
            container = self.client.containers.get(container_id)
            command = command.encode().decode("ascii", "ignore")
            print_command = "({}) {}".format(workdir, command)
            # emitter.docker_command(print_command)
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
            # emitter.error(ex)
            # utilities.error_exit(
            #     "(error) Unable to find container: container not found: {}".format(
            #         container_id
            #     )
            # )
            pass
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.error(exp)
            # utilities.error_exit(
            #     "\t\t\t[error] unable to find container: docker daemon error"
            # )
            pass
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )

        except Exception as ex:
            # emitter.error(ex)
            # utilities.error_exit(
            #     "\t\t\t[error] unable to find container: unhandled exception"
            # )
            pass
        return exit_code, output

    def remove_container(self, container_id: str):
        # emitter.normal("\t\t\t[framework] removing docker container")
        try:
            container = self.client.containers.get(container_id)
            container.remove(force=True)  # type: ignore
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.warning(exp)
            # emitter.warning("[warning] unable to remove container: docker daemon error")
            pass
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            pass
            # emitter.warning(ex)
            # emitter.warning("[warning] unable to remove container: unhandled exception")

    def start_container(self, container_id: str):
        # emitter.normal(
        #     "\t\t\t[framework] starting docker container {}".format(container_id)
        # )
        try:
            container = self.client.containers.get(container_id)
            container.start()  # type: ignore
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.warning(exp)
            # emitter.warning(
            #     "\t\t\t[framework] unable to stop container: docker daemon error"
            # )
            pass
        except Exception as ex:
            # emitter.warning(ex)
            # emitter.warning(
            #     "\t\t\t[framework] unable to stop container: unhandled exception"
            # )
            pass

    def stop_container(self, container_id: str):
        # emitter.normal("\t\t\t[framework] stopping docker container")
        try:
            container = self.client.containers.get(container_id)
            container.stop(timeout=20)  # type: ignore
        except docker.errors.APIError as exp:  # type: ignore
            # emitter.warning(exp)
            # emitter.warning(
            #     "\t\t\t[framework] unable to stop container: docker daemon error"
            # )
            pass
        except IOError as ex:
            # emitter.error(ex)
            raise RuntimeError(
                "[error] docker connection unsuccessful. Check if Docker is running or there is a connection to the specified host."
            )
        except Exception as ex:
            # emitter.warning(ex)
            # emitter.warning(
            #     "\t\t\t[framework] unable to stop container: unhandled exception"
            # )
            pass














    def is_file(container_id: str, file_path: str):
        exist_command = "test -f {}".format(file_path)
        return exec_command(container_id, exist_command)[0] == 0

    def is_dir(container_id: str, dir_path: str):
        exist_command = "test -d {}".format(dir_path)
        return exec_command(container_id, exist_command)[0] == 0

    def is_file_empty(container_id: str, file_path: str):
        exist_command = "[ -s {} ]".format(file_path)
        return exec_command(container_id, exist_command)[0] != 0

    def fix_permissions(container_id: str, dir_path: str):
        permission_command = "chmod -R g+w  {}".format(dir_path)
        return exec_command(container_id, permission_command)

    def list_dir(container_id: str, dir_path: str, regex=None):
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

    def copy_file_from_container(container_id: str, from_path: str, to_path: str):
        copy_command = "docker -H {} cp {}:{} {}".format(
            values.docker_host, container_id, from_path, to_path
        )
        utilities.execute_command(copy_command)

    def copy_file_to_container(container_id: str, from_path: str, to_path: str):
        copy_command = "docker -H {} cp {} {}:{}".format(
            values.docker_host, from_path, container_id, to_path
        )
        utilities.execute_command(copy_command)

    def write_file(container_id: str, file_path: str, content: List[str]):
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

    def read_file(container_id: str, file_path: str, encoding="utf-8"):
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

    def append_file(container_id: str, file_path: str, content: List[str]):
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
