
class BugInfo:

    def __init__(self, **kwargs):

        # mandatory fields
        self.id = kwargs["id"]
        self.bug_id = kwargs["bug_id"]
        self.subject = kwargs["subject"]

        # optional fields
        for key, value in kwargs.items():
            setattr(self, key, value)

    def get_id(self):
        return self.id

    def get_bug_id(self):
        return self.bug_id

    def get_subject(self):
        return self.subject
