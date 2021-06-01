#!/usr/bin/env python
# -*- encoding: utf-8 -*-

import re

from . import Request, ValidationError

# Src: http://code.djangoproject.com/svn/django/trunk/django/core/validators.py
email_re = re.compile(
    r"(^[-!#$%&'*+/=?^_`{}|~0-9A-Z]+(\.[-!#$%&'*+/=?^_`{}|~0-9A-Z]+)*"  # dot-atom
    # quoted-string, see also http://tools.ietf.org/html/rfc2822#section-3.2.5
    r'|^"([\001-\010\013\014\016-\037!#-\[\]-\177]|\\[\001-\011\013\014\016-\177])*"'
    r')@((?:[A-Z0-9](?:[A-Z0-9-]{0,61}[A-Z0-9])?\.)+[A-Z]{2,6}\.?$)'  # domain
    r'|\[(25[0-5]|2[0-4]\d|[0-1]?\d?\d)(\.(25[0-5]|2[0-4]\d|[0-1]?\d?\d)){3}\]$', re.IGNORECASE)  # literal form, ipv4 address (SMTP 4.1.3)


class List(Request):

    uri = 'user/emails'


class Add(Request):

    uri = 'user/emails'

    def clean_body(self):
        def is_email(email):
            return bool(email_re.match(email))
        if not self.body:
            raise ValidationError("'%s' request needs emails"
                                  % (self.__class__.__name__))

        return filter(is_email, self.body)


class Delete(Request):

    uri = 'user/emails'

    def clean_body(self):
        if not self.body:
            raise ValidationError("'%s' request needs emails"
                                  % (self.__class__.__name__))
        return self.body
