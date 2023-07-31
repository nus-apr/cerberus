#!/usr/bin/python
#Title			: improver.py
#Usage			: python improver.py -h
#Author			: pmorvalho
#Date			: July 31, 2023
#Description		: Placeholder
#Notes			: 
#Python Version: 3.8.5
# (C) Copyright 2023 Pedro Orvalho.
#==============================================================================

import argparse
from sys import argv

def parser():
    parser = argparse.ArgumentParser(prog='Improver.py', formatter_class=argparse.RawTextHelpFormatter)
    args = parser.parse_args(argv[1:])
    return args

if __name__ == '__main__':
    args = parser()
