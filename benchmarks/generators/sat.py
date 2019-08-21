#!/usr/bin/env python3

"""
 Script for generating parametric WS2S formulae.
 @title sat.py
 @author Vojtech Havlena, November 2018
"""

import sys

def main():
    if len(sys.argv) != 2:
        sys.stderr.write("Bad input arguments. \nFormat: ./sat [num]\n")
        sys.exit()

    num = int(sys.argv[1])

    sys.stdout.write("ws2s;\n\nex2 ")
    for i in range(num):
        delim = ","
        if i == num-1:
            delim = ":"
        sys.stdout.write("X{0}{1} ".format(i, delim))
    sys.stdout.write("all2 Y1, Y2: ")

    for i in range(num):
        delim = "&"
        if i == num-1:
            delim = ";"
        sys.stdout.write("((X{0} = Y1.0 & X{1} sub Y2) => Y1 = Y2) {3}".format(i, i, i, delim))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
