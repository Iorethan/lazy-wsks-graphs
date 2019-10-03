#!/usr/bin/env python3

"""
 Wrapper for automated collecting statistics from mona benchmarks.
 @title gather-stat.py
 @author Ondřej Valeš, 2019
"""

import sys
import os
import subprocess


SUPPORTED_INPUT = ["[ws1s]", "[wsks]"]


def main():
    if len(sys.argv) != 5:
        help_err()
        sys.exit()

    monabin = sys.argv[1]
    stat_py = sys.argv[2]
    benchmark_folder = sys.argv[3]
    output_folder = sys.argv[4]

    cnt = 0
    with os.scandir(benchmark_folder) as folder:
        for item in folder:
            cnt += 1

    folder = os.scandir(benchmark_folder)
    i = 0
    for item in folder:
        i += 1
        print(str(i) + "/" + str(cnt) + "\t" + item.name)
        if item.is_dir():
            run_mona_stat(monabin, stat_py, benchmark_folder, item.name, output_folder)


def run_mona_stat(monabin, stat_py, benchmark_folder, folder, output_folder):
    if any([folder.startswith(inp) for inp in SUPPORTED_INPUT]):
        input_folder = os.path.join(benchmark_folder, folder)
        output_folder = os.path.join(output_folder, folder)
        subprocess.call(["python3", stat_py, monabin, input_folder, output_folder], stdout=subprocess.DEVNULL)



def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./mona-stat.py [mona-bin] [benchmark folder] [output folder]\n")


if __name__ == "__main__":
    main()