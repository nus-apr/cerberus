from app.core import definitions
from app.core import utilities
from app.core import values
from app.notification import email


def notify(message, data=None):
    if values.email_configuration.get(definitions.KEY_ENABLED, False):
        email.send_message(message)

    if values.slack_configuration.get(definitions.KEY_ENABLED, False):
        from app.notification import slack

        slack.send_message(message, data)

    if values.discord_configuration.get(definitions.KEY_ENABLED, False):
        from app.notification import discord

        discord.send_message(message)


def error_exit():
    error_message = "Cerberus Exited Abruptly"
    notify(error_message)


def end(time_total, is_error=False):
    if values.arg_pass and not is_error:
        end_message = (
            f"{values.tool_name} finished successfully after " f"{time_total}  minutes"
        )
        notify(end_message)
