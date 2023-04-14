from app.core import utilities
from app.core import values
from app.notification import email


def notify(message, data=None):
    print("Sending", message)
    if values.is_email_set:
        email.send_message(message)

    if values.is_slack_set:
        from app.notification import slack

        slack.send_message(message, data)


def error_exit():
    error_message = "Cerberus Exited Abruptly"
    notify(error_message)


def end(time_total, is_error=False):
    print(values.arg_pass, is_error)
    if values.arg_pass and not is_error:
        end_message = (
            f"{values.tool_name} finished successfully after " f"{time_total}  minutes"
        )
        notify(end_message)
