from typing import Any
from typing import Dict
from typing import Optional

from app.core import definitions
from app.drivers.benchmarks.AbstractBenchmark import AbstractBenchmark
from app.drivers.tools.AbstractTool import AbstractTool


def create_bug_image_identifier(
    benchmark: AbstractBenchmark, experiment_item: Dict[str, Any]
) -> str:
    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
    return "-".join(
        map(lambda x: x.replace("-", "_"), [benchmark.name, subject_name, bug_name])
    ).lower()


def create_task_identifier(
    benchmark: AbstractBenchmark,
    task_profile: Dict[str, Any],
    container_profile: Dict[str, Any],
    experiment_item: Dict[str, Any],
    tool: AbstractTool,
    run_index: str,
    tool_tag: str,
) -> str:
    return "-".join(
        [
            benchmark.name,
            tool.name if tool_tag == "" else f"{tool.name}-{tool_tag}",
            experiment_item[definitions.KEY_SUBJECT],
            experiment_item[definitions.KEY_BUG_ID],
            task_profile[definitions.KEY_ID],
            container_profile[definitions.KEY_ID],
            run_index,
        ]
    )


def create_task_image_identifier(
    benchmark: AbstractBenchmark,
    tool: AbstractTool,
    experiment_item: Dict[str, Any],
    tag: Optional[str] = None,
) -> str:
    bug_name = str(experiment_item[definitions.KEY_BUG_ID])
    subject_name = str(experiment_item[definitions.KEY_SUBJECT])
    image_args = [tool.name, benchmark.name, subject_name, bug_name]

    # if tag and tag != "":
    #    image_args.append(tag)

    image_name = "-".join(map(lambda x: x.replace("-", "_"), image_args))
    return image_name.lower()
