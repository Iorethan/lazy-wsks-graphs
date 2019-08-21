#!/usr/bin/env python3

"""
 Script for generating parametric WS2S formulae.
 @title horn-subset-trans.py
 @author Vojtech Havlena, January 2019
"""

import sys

STR = "0.1"
N = 4

def main():
    if len(sys.argv) != 2:
        sys.stderr.write("Bad input arguments. \nFormat: ./horn-sub-trans [num]\n")
        sys.exit()

    num = int(sys.argv[1])

    sys.stdout.write("ws2s;\n\nex1 z: z=root.{0}{1} & z=root.".format((STR+".")*(N-1), STR))
    for i in range(num):
        delim = "."
        if i == num-1:
            delim = ";"
        sys.stdout.write("{0}{1}".format(STR, delim))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
