from typing import Any
from typing import Dict
from typing import Optional
from typing import Sequence
from typing import Union

from slack_sdk import WebClient
from slack_sdk.errors import SlackApiError
from slack_sdk.webhook import WebhookClient

from app.core import utilities
from app.core import values


def send_message(
    message: str, additional_data: Optional[Union[Sequence[Dict[str, Any]], Any]] = None
) -> None:
    url = str(values.slack_configuration["hook_url"])
    token = str(values.slack_configuration["oauth_token"])
    channel = str(values.slack_configuration["channel"])
    if token:
        send_using_oauth(token, channel, message, additional_data)
    if url:
        send_using_webhook(url, message, additional_data)


def send_using_webhook(
    url: str,
    message: str,
    additional_data: Optional[Union[Sequence[Dict[str, Any]], Any]],
) -> None:
    webhook = WebhookClient(url)
    response = webhook.send(text=message, blocks=additional_data)
    assert response.status_code == 200
    assert response.body == "ok"


def send_using_oauth(
    token: Optional[str],
    channel: str,
    message: str,
    additional_data: Optional[Union[Sequence[Dict[str, Any]], Any]],
) -> None:
    client = WebClient(token=token)
    client.chat_postMessage(channel="#" + channel, text=message, blocks=additional_data)
