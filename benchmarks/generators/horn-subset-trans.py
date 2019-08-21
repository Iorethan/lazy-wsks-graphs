#!/usr/bin/env python3

"""
 Script for generating parametric WS2S formulae.
 @title horn-subset-trans.py
 @author Vojtech Havlena, June 2018
"""

import sys

def main():
    if len(sys.argv) != 2:
        sys.stderr.write("Bad input arguments. \nFormat: ./horn-sub-trans [num]\n")
        sys.exit()

    num = int(sys.argv[1])

    sys.stdout.write("ws2s;\n\nex2 ")
    for i in range(num):
        delim = ","
        if i == num-1:
            delim = ":"
        sys.stdout.write("X{0}{1} ".format(i, delim))

    for i in range(num-1):
        delim = "&"
        if i == num-2:
            delim = ";"
        sys.stdout.write("X{0} sub X{1} {2} ".format(i, i+1, delim))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
