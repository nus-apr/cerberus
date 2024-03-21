import math
from typing import cast

from discord import SyncWebhook

from app.core import values

max_length = (
    2000  # Currently Discord supports only 2000 character messages so they are split
)


def send_message(message: str) -> None:
    webhook = SyncWebhook.from_url(cast(str, values.discord_configuration["hook_url"]))

    chunks = len(message) / max_length

    for chunk in range(math.ceil(chunks)):
        webhook.send(
            message[chunk * max_length : min(len(message), (chunk + 1) * max_length)],
            username="Cerberus Notification System",
        )
