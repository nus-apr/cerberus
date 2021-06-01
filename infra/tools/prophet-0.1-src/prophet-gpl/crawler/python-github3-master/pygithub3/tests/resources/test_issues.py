#!/usr/bin/env python
# -*- encoding: utf-8 -*-

from unittest import TestCase

from pygithub3.resources.issues import Label


class TestLabel(TestCase):
    def test_is_valid_color(self):
        valid_colors = ['BADa55', 'FF42FF', '45DFCA']
        for color in valid_colors:
            self.assertTrue(Label.is_valid_color(color))

        invalid_colors = ['BDA55', '#FFAABB', 'FFf']
        for color in invalid_colors:
            self.assertFalse(Label.is_valid_color(color))
