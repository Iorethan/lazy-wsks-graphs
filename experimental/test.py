#!/usr/bin/env python3

"""
 Script for predicting automata sizes in formula construction.
 @title predict.py
 @author Ondřej Valeš, 2019
"""

import sys
import socket

SOCKET_NR = 50889


def main():
    global SOCKET_NR

    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect(('localhost', SOCKET_NR))
    s.sendall(sys.argv[1].encode())

    if sys.argv[1] == "stop":
        sys.exit(0)
    
    response = s.recv(1024).decode()
    s.close()
    print(response)


if __name__ == "__main__":
    main()
