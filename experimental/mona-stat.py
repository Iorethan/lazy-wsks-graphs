#!/usr/bin/env python3

"""
 Script for automated collecting statistics about the formula construction.
 @title mona-stat.py
 @author Vojtech Havlena, July 2019
"""

import sys
import getopt
import subprocess
import string
import re
import os
import os.path
import resource
from graphviz import Digraph

TIMEOUT = 300 #in seconds
FORMULAS = 20
SHOW_MINIMIZED = True
USE_HUMAN_READABLE_NAMES = False


def main():
    if len(sys.argv) < 3:
        help_err()
        sys.exit()

    monabin = sys.argv[1]
    formulafolder = sys.argv[2]

    try:
        opts, _ = getopt.getopt(sys.argv[3:], "f:", ["formulas="])
    except getopt.GetoptError as _:
        help_err()
        sys.exit()
    FORMULAS = 20

    for o, a in opts:
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)

    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    files = files[:FORMULAS]

    print_config()

    for monafile in files:
        known_addresses = []
        filename = os.path.join(formulafolder, monafile)
        try:
            mona_output = subprocess.check_output([monabin, "-i", filename], timeout=TIMEOUT).decode("utf-8")
            mona_parse = parse_mona(mona_output, known_addresses)
        except subprocess.TimeoutExpired:
            mona_parse = "TO"
        except subprocess.CalledProcessError as _:
            mona_parse = "None"
        print_graph(filename, "", mona_parse)
        print_output(filename, "", mona_parse)


def format_op(op, params):
    res = op
    for par in params:
        res = res + ";{0}".format(par)
    return res


def parse_mona(output, known_addresses):
    res = ""
    lines = output.split('\n')
    for i in range(len(lines)):
        line = lines[i]
        if line.startswith("Product &"):
            parse = proc_product(lines, i, known_addresses)
            res = res + "{0}\n".format(format_op("&", parse))
        if line.startswith("Product |"):
            parse = proc_product(lines, i, known_addresses)
            res = res + "{0}\n".format(format_op("|", parse))
        if line.startswith("Projecting"):
            parse = parse_mona_projection(lines[i+3:i+5], known_addresses)
            logic = "ws1s" if lines[i+5] == "Resulting DFA:" else "ws2s"
            fv = get_fv(lines[i+6:], logic)
            parse.append(','.join(fv))
            res = res + "{0}\n".format(format_op("proj", parse))
    return res


def proc_product(lines, i, known_addresses):
    parse = parse_mona_product(lines[i+3:i+5], known_addresses)
    logic = "ws1s" if lines[i+5] == "Resulting DFA:" else "ws2s"
    j = i+6
    if parse is None:
        parse = parse_mona_product(lines[i+1:i+3], known_addresses)
        logic = "ws1s" if lines[i+3] == "Resulting DFA:" else "ws2s"
        j = i+4
    fv = get_fv(lines[j:], logic)
    parse.append(','.join(fv))
    return parse


def parse_mona_product(lines, known_addresses):
    res = [None]*8
    match = re.search("\\(([0-9]+),[0-9]+,([0-9a-f]+)\\)x\\(([0-9]+),[0-9]+,([0-9a-f]+)\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[0])
    if match is None:
        return None
    res[0], res[1], res[2] = address_to_name(match.group(2), known_addresses), int(match.group(1)), address_to_name(match.group(4), known_addresses)
    res[3], res[4], res[5] = int(match.group(3)), address_to_name(match.group(6), known_addresses), int(match.group(5)) 
    match = re.search("Minimizing \\([0-9]+,[0-9]+,[0-9a-f]+\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[1])
    if match is None:
        return None
    res[6], res[7] = address_to_name(match.group(2), known_addresses), int(match.group(1))
    return res


def parse_mona_projection(lines, known_addresses):
    res = [None]*8
    match = re.search("\\(([0-9]+),[0-9]+,([0-9a-f]+)\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[0])
    res[0], res[1], res[2] = address_to_name(match.group(2), known_addresses), int(match.group(1)), "0x0"
    res[3], res[4], res[5] = -1, address_to_name(match.group(4), known_addresses), int(match.group(3)) 
    match = re.search("Minimizing \\([0-9]+,[0-9]+,[0-9a-f]+\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[1])
    res[6], res[7] = address_to_name(match.group(2), known_addresses), int(match.group(1))
    return res


def get_fv(lines, parser):
    fv = set()
    if parser == "ws1s":
        for line in lines[5:]:
            ret = parse_dfa_trans(line)
            if ret is None:
                break
            _, sym, _ = ret
            fv = fv.union(symbols_free_vars(sym))
    else:
        for line in lines[3:]:
            if line == "" or re.match("(State space.*)|(Initial state:.*)|(Transitions:)", line) is not None:
                continue
            ret = parse_gta_trans(line)
            if ret is None:
                break
            _, sym, _ = ret
            fv = fv.union(symbols_free_vars(sym))
    return fv


def parse_dfa_trans(line):
    match = re.search("^State ([0-9]+): ([^->]*) -> state ([0-9]+)$", line)
    if match is None:
        return None
    fr, label, to = int(match.group(1)), match.group(2), match.group(3)
    if label.strip() == "":
        syms = []
    else:
        syms = label.split(", ")
    return fr, syms, to


def parse_gta_trans(line):
    match = re.search(r"^\(([0-9]+,[0-9]+,)([^->]*)\) -> ([0-9]+)$", line)
    if match is None:
        return None
    fr, label, to = match.group(1), match.group(2), match.group(3)
    if label.strip() == "":
        syms = []
    else:
        syms = label.split(", ")
    return fr, syms, to


def symbols_free_vars(syms):
    fv = set()
    for sym in syms:
        fv.add(sym.split("=")[0])
    return fv


def address_to_name(address, known_addresses):
    if address not in known_addresses:
        known_addresses.append(address)
    if USE_HUMAN_READABLE_NAMES:
        name = make_human_readable(known_addresses.index(address))
    else:
        name = address
    return name


def make_human_readable(id):
    names = [
        "Alpha",
        "Bravo",
        "Charlie",
        "Delta",
        "Echo",
        "Foxtrot",
        "Golf",
        "Hotel",
        "India",
        "Juliett",
        "Kilo",
        "Lima",
        "Mike",
        "November",
        "Oscar",
        "Papa",
        "Quebec",
        "Romeo",
        "Sierra",
        "Tango",
        "Uniform",
        "Victor",
        "Whiskey",
        "Xray",
        "Yankee",
        "Zulu"
    ]
    return names[id % len(names)] + (str(int(id / len(names))) if id >= len(names) else "")


def make_graph(name, data):
    data = list(map(lambda x: x.split(';'), data.split('\n')[:-1]))
    graph = Digraph(name)
    names = {"0x0"}
    for item in data:
        check_children(graph, names, item[1:5])
        if item[0] == 'proj':
            process_projection(graph, names, item[1:])
        else:
            process_product(graph, names, item[1:], item[0])
    return graph


def check_children(graph, names, node):
    items = [(node[0], node[1]), (node[2], node[3])]
    for name, size in items:
        if not name in names:
            create_leaf_node(graph, name, size)
            names.add(name)


def process_projection(graph, names, node):
    if SHOW_MINIMIZED:
        create_unary_node(graph, node[4], node[5], node[8], node[0], "proj")
        names.add(node[4])
        create_unary_node(graph, node[6], node[7], node[8], node[4], "min")
        names.add(node[6])
    else:
        create_unary_node(graph, node[6], node[7], node[8], node[0], "proj")
        names.add(node[6])

    
def process_product(graph, names, node, operation):
    if SHOW_MINIMIZED:
        create_binary_node(graph, node[4], node[5], node[8], node[0], node[2], operation)
        names.add(node[4])
        create_unary_node(graph, node[6], node[7], node[8], node[4], "min")
        names.add(node[6])
    else:
        create_binary_node(graph, node[6], node[7], node[8], node[0], node[2], operation)
        names.add(node[6])


def create_leaf_node(graph, name, size):
    graph.node(name, label=name + "\\nsize: " + size)


def create_unary_node(graph, name, size, free_vars, child, operation):
    graph.node(name, label=name + "\\nsize: " + size + "\\nfree: " + free_vars)
    graph.edge(name, child, label=operation)


def create_binary_node(graph, name, size, free_vars, lchild, rchild, operation):
    graph.node(name, label=name + "\\nsize: " + size + "\\nfree: " + free_vars)
    graph.edge(name, lchild, label=operation)
    graph.edge(name, rchild, label=operation)


def print_config():
    print("Timeout: {0}".format(TIMEOUT))
    print("Number of formulas: {0}".format(FORMULAS))


def print_graph(filename, suf, data):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    graph = make_graph(name, data)
    graph.save()
    

def print_output(filename, suf, output):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    output = "operation;operand1;size1;operand2;size2;result;resultsize;minresult;minsize;fv\n" + output
    f = open(name + suf + ".csv", "w")
    f.write(output)
    f.close()


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./mona-stat.py [mona-bin] [formula folder]\n")


if __name__ == "__main__":
    main()
