#!/usr/bin/env python3

"""
 Script for automated testing.
 @title testcheck.py
 @author Vojtech Havlena, May 2018
"""

import sys
import subprocess
import string
import re
import os
import os.path
import resource

from termcolor import colored

VALIDLINE = -3
TIMELINE = -1
TIMEOUT=50 #in seconds
COLOR=True

def main():
    if len(sys.argv) != 3:
        sys.stderr.write("Bad input arguments. \nFormat: ./testcheck [program] [formula folder]\n")
        sys.exit()

    program = sys.argv[1]
    formulafolder = sys.argv[2]

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]

    success = True

    for monafile in files:
        filename = os.path.join(formulafolder, monafile)
        try:
            program_output = subprocess.check_output([program, filename], timeout=TIMEOUT).decode("utf-8")
            #time = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
        except subprocess.TimeoutExpired:
            print("Timeout expired: {0}; Time: {1}s".format(monafile, TIMEOUT))
            continue
        lines = program_output.split('\n')
        lines = list(filter(None, lines)) #Remove empty lines
        valid = file_formula_valid(filename)
        if (lines[VALIDLINE] == "valid" and valid) or (lines[VALIDLINE] == "unsatisfiable" and not valid):
            correct = colored("Correct:", "green") if COLOR else "Correct:"
            print(correct, " {0: <25} {1}".format(monafile, lines[TIMELINE]))
        else:
            fail = colored("Fail:", "red") if COLOR else "Fail:"
            print(fail, " {0: <25} {1}".format(monafile, lines[TIMELINE]))
            success = False

    if success:
        sys.exit(0)
    else:
        sys.exit(1)


def parse_validity(content):
    p = re.compile(r'^#\s*Validity:\s*(?P<valid>\w*)')
    lines = content.split('\n')
    for line in lines:
        mobject = p.match(line)
        if mobject is not None:
            if mobject.group("valid").startswith("valid"):
                return True
            return False


def file_formula_valid(filename):
    try:
        handler = open(filename, "r")
    except IOError:
        sys.stderr("Could not open MONA formula file.")
        return False

    content = handler.read()
    handler.close()
    return parse_validity(content)


if __name__ == "__main__":
    main()
