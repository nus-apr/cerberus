from slack_sdk import WebClient
from slack_sdk.errors import SlackApiError
from slack_sdk.webhook import WebhookClient

from app.core import utilities
from app.core import values


def send_message(message_str, additional_data=None):
    url = values.slack_configuration["hook_url"]
    token = values.slack_configuration["oauth_token"]
    channel = values.slack_configuration["channel"]
    if token:
        send_using_oauth(token, channel, message_str, additional_data)
    if url:
        send_using_webhook(url, message_str, additional_data)


def send_using_webhook(url, message_str, additional_data):
    webhook = WebhookClient(url)
    response = webhook.send(text=message_str, blocks=additional_data)
    assert response.status_code == 200
    assert response.body == "ok"


def send_using_oauth(token, channel, message_str, additional_data):
    client = WebClient(token=token)
    client.chat_postMessage(
        channel="#" + channel, text=message_str, blocks=additional_data
    )
