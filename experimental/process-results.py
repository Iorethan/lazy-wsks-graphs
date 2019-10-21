#!/usr/bin/env python3

"""
 Script for automated collecting statistics about the formula construction.
 @title process_results.py
 @author Ondřej Valeš, 2019
"""

import sys
import os

BIN_OPERATIONS = {
    '&': 'and',
    '|': 'or',
    '=>': 'impl'
}

UN_OPERATIONS = {
    'proj': 'proj',
}


def main():
    if len(sys.argv) != 2:
        help_err()
        sys.exit()

    files = get_files(sys.argv[1])
    process_files(files)


def get_files(folder):
    files = [os.path.join(folder, f) for f in os.listdir(folder) \
        if os.path.isfile(os.path.join(folder, f)) and \
            f.endswith(".csv")]
    return sorted(files)


def process_files(files):
    results = dict()
    for csv in files:
        with open(csv, 'r') as handle:
            process_file([line[:-1].split(';') for line in handle.readlines()], results)
    save_results(results)
    


def process_file(lines, results):
    global BIN_OPERATIONS
    global UN_OPERATIONS
    for operation in BIN_OPERATIONS:
        data = [line for line in lines if line[0].startswith(operation)]
        results[operation] = results.get(operation, default_bin()) +\
            [format_bin_operation(line[1:]) for line in data]
    return results


def format_bin_operation(line):
    fv1 = set(line[2].split(','))
    fv2 = set(line[5].split(','))
    fv1.discard('')
    fv2.discard('')
    common = fv1.intersection(fv2)
    return [line[1], str(len(fv1)), line[4], str(len(fv2)), str(len(common)), line[7], line[10]]


def default_bin():
    return [['size1', 'fvcnt1', 'size2', 'fvcnt2', 'cmnfvcnt', 'size', 'minsize']]


def save_results(results):
    global BIN_OPERATIONS
    global UN_OPERATIONS
    for operation in BIN_OPERATIONS:
        with open(BIN_OPERATIONS[operation] + '.csv', 'w') as handle:
            text = '\n'.join([';'.join(result) for result in results[operation]])
            handle.write(text)


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./process-results.py [results folder]\n")


if __name__ == "__main__":
    main()
