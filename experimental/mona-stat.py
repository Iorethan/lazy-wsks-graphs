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
SHOW_NAMES = True


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
        filename = os.path.join(formulafolder, monafile)
        try:
            mona_output = subprocess.check_output([monabin, "-i", filename], timeout=TIMEOUT).decode("utf-8")
            mona_parse, names, _ = parse_mona(mona_output)
        except subprocess.TimeoutExpired:
            mona_parse = "TO"
        except subprocess.CalledProcessError as _:
            mona_parse = "None"
        print_graph(filename, "", mona_parse, names)
        print_output(filename, "", mona_parse, names)


def format_op(op, params):
    res = op
    for par in params:
        res = res + ";{0}".format(par)
    return res

def format_init(names):
    res = ""
    for id in names:
        res = res + "init;0x0;-1;0x0;-1;0x0;-1;" + id + ";" + names[id][1] + ";" + ','.join(names[id][2]) + ";\n"
    return res


def parse_mona(output):
    res = ""
    lines = output.split('\n')
    variables = parse_variables(lines)
    lines = lines[lines.index("AUTOMATON CONSTRUCTION"):]
    names = dict()
    j = 0
    for i in range(len(lines)):
        if j > 0:
            j -= 1
            continue
        line = lines[i]
        if is_initial_automaton(line):
            proc_init(lines, i, names, variables)
        if line.startswith("Copying"):
            proc_copy(lines, i, names)
        if line.startswith("Replacing indices"):
            proc_replace(lines, i, names)
        if line.startswith("  Minimizing"):
            parse = proc_minim(lines, i, names, variables)
            res = res + "{0}\n".format(format_op("min", parse))
        if line.startswith("Product &"):
            parse = proc_product(lines, i, names, variables, "&")
            res = res + "{0}\n".format(format_op("&", parse))
            j = 6
        if line.startswith("Product |"):
            parse = proc_product(lines, i, names, variables, "|")
            res = res + "{0}\n".format(format_op("|", parse))
            j = 6
        if line.startswith("Product <=>"):
            parse = proc_product(lines, i, names, variables, "<=>")
            res = res + "{0}\n".format(format_op("<=>", parse))
            j = 6
        if line.startswith("Product =>"):
            parse = proc_product(lines, i, names, variables, "=>")
            res = res + "{0}\n".format(format_op("=>", parse))
            j = 6
        if line.startswith("Projecting"):
            var = re.match("Projecting (#[0-9+])", line).group(1)
            parse = parse_mona_projection(lines, i, names, variables, var)
            res = res + "{0}\n".format(format_op("proj " + var, parse))
            j = 6
    res = format_init(names) + res
    return res, names, variables


def parse_variables(lines):
    variables = dict()
    for i in range(len(lines)):
        line = lines[i]
        if line.startswith("Symbol table:"):
            variables = parse_var_table(lines[i+3:])
    return variables


def parse_var_table(lines):
    variables = dict()
    for line in lines:
        if line == "":
            break
        line = line.split()
        variables[line[1]] = line[0]
    return variables
        

def is_initial_automaton(line):
    initial_automata = ["True", "False", "Empty", "FirstOrder", "Const",
                        "Singleton", "BoolVar", "In(", "Eq1", "Eq2", "Sub2",
                        "Less1", "LessEq1", "EqPlus2", "EqMinus2", "EqMin",
                        "EqMax", "EqPlus1", "EqMinus1", "Union", "Inter",
                        "SetMinus", "EqPlusModulo", "EqMinusModulo", "PresbConst"]
    return any([line.startswith(automaton) for automaton in initial_automata])


def proc_init(lines, i, names, variables):
    name = lines[i]
    match = re.match(r"Automaton \(([0-9]+),([0-9]+),([0-9]+)\)", lines[i+1])
    size, id = match.group(1), match.group(3)
    logic = "ws1s" if lines[i+2] == "Resulting DFA:" else "ws2s"
    fv = get_fv(lines[i+3:], logic)
    fv = replace_names(fv, variables)
    names[id] = [name, size, fv]


def replace_names(fv, variables):
    return set([variables[x] for x in fv])


def proc_copy(lines, i, names):
    match = re.match(r".*\(([0-9]+),([0-9]+),([0-9]+)\).*\(([0-9]+),([0-9]+),([0-9]+)\)", lines[i])
    orig, copy = match.group(3), match.group(6)
    names[copy] = names[orig][:]
    names[copy][2] = names[copy][2].copy()


def proc_replace(lines, i, names):
    match = re.match(r".*\(([0-9]+),([0-9]+),([0-9]+)\)", lines[i])
    id = match.group(3)
    replacements = list()
    for line in lines[i+1:]:
        match = re.match(r"\[(#[0-9]+)->(#[0-9]+)\]", line)
        if match is None:
            break
        replacements.append([match.group(1), match.group(2)])
    replacements.reverse()
    for item in replacements:
        names[id][0] = names[id][0].replace(item[0], item[1])
        names[id][2].remove(item[0])
        names[id][2].add(item[1])


def proc_minim(lines, i, names, variables):
    parse = parse_mona_minim(lines[i])
    logic = "ws1s" if lines[i+1] == "Resulting DFA:" else "ws2s"
    j = i+2
    fv = get_fv(lines[j:], logic)
    fv = replace_names(fv, variables)
    parse.append(','.join(fv))
    name = "min(" + names[parse[0]][0] + ")"
    names[parse[6]] = [name, parse[7], fv]
    return parse


def parse_mona_minim(line):
    res = [None]*8
    match = re.match("  Minimizing \\(([0-9]+),[0-9]+,([0-9a-f]+)\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", line)
    if match is None:
        return None
    res[0], res[1], res[2] = match.group(2), match.group(1), "0x0"
    res[3], res[4], res[5] = -1, "0x0", -1
    res[6], res[7] = match.group(4), match.group(3)
    return res


def proc_product(lines, i, names, variables, operation):
    parse = parse_mona_product(lines[i+3:i+5])
    logic = "ws1s" if lines[i+5] == "Resulting DFA:" else "ws2s"
    j = i+6
    if parse is None:
        parse = parse_mona_product(lines[i+1:i+3])
        logic = "ws1s" if lines[i+3] == "Resulting DFA:" else "ws2s"
        j = i+4
    fv = get_fv(lines[j:], logic)
    fv = replace_names(fv, variables)
    parse.append(','.join(fv))
    name = names[parse[0]][0] + " " + operation + " " + names[parse[2]][0]
    min_name = "min(" + name + ")"
    names[parse[4]] = [name, parse[5], fv]
    names[parse[6]] = [min_name, parse[7], fv]
    return parse


def parse_mona_product(lines):
    res = [None]*8
    match = re.search("\\(([0-9]+),[0-9]+,([0-9a-f]+)\\)x\\(([0-9]+),[0-9]+,([0-9a-f]+)\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[0])
    if match is None:
        return None
    res[0], res[1], res[2] = match.group(2), match.group(1), match.group(4)
    res[3], res[4], res[5] = match.group(3), match.group(6), match.group(5)
    match = re.search("Minimizing \\([0-9]+,[0-9]+,[0-9a-f]+\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[1])
    if match is None:
        return None
    res[6], res[7] = match.group(2), match.group(1)
    return res


def parse_mona_projection(lines, i, names, variables, var):
    res = [None]*8
    match = re.search("\\(([0-9]+),[0-9]+,([0-9a-f]+)\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[i+3])
    res[0], res[1], res[2] = match.group(2), match.group(1), "0x0"
    res[3], res[4], res[5] = -1, match.group(4), match.group(3)
    match = re.search("Minimizing \\([0-9]+,[0-9]+,[0-9a-f]+\\) -> \\(([0-9]+),[0-9]+,([0-9a-f]+)\\)", lines[i+4])
    res[6], res[7] = match.group(2), match.group(1)
    logic = "ws1s" if lines[i+5] == "Resulting DFA:" else "ws2s"
    fv = get_fv(lines[i+6:], logic)
    fv = replace_names(fv, variables)
    res.append(','.join(fv))
    name = "proj " + var + "(" + names[res[0]][0] + ")"
    min_name = "min(" + name + ")"
    names[res[4]] = [name, res[5], fv]
    names[res[6]] = [min_name, res[7], fv]
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


def make_graph(name, data, names):
    data = list(map(lambda x: x.split(';'), data.split('\n')[:-1]))
    graph = Digraph(name)
    for item in data:
        if item[0] == 'init':
            process_initial(graph, names, item[1:])
        elif item[0].startswith('min'):
            process_minimization(graph, names, item[1:], item[0])
        elif item[0].startswith('proj'):
            process_projection(graph, names, item[1:], item[0])
        else:
            process_product(graph, names, item[1:], item[0])
    return graph


def process_initial(graph, names, node):
    create_leaf_node(graph, node[6], names[node[6]][0], node[7], node[8])


def process_minimization(graph, names, node, operation):
    create_unary_node(graph, node[6], names[node[6]][0], node[7], node[8], node[0], "min")


def process_projection(graph, names, node, operation):
    name = names[node[4]][0]
    min_name = names[node[6]][0]
    if SHOW_MINIMIZED:
        create_unary_node(graph, node[4], name, node[5], node[8], node[0], operation)
        create_unary_node(graph, node[6], min_name, node[7], node[8], node[4], "min")
    else:
        create_unary_node(graph, node[6], min_name, node[7], node[8], node[0], "min + " + operation)

    
def process_product(graph, names, node, operation):
    name = names[node[4]][0]
    min_name = names[node[6]][0]
    if SHOW_MINIMIZED:
        create_binary_node(graph, node[4], name, node[5], node[8], node[0], node[2], operation)
        create_unary_node(graph, node[6], min_name, node[7], node[8], node[4], "min")
    else:
        create_binary_node(graph, node[6], min_name, node[7], node[8], node[0], node[2], operation)


def create_leaf_node(graph, name, label, size, free_vars):
    graph.node(name, label=label + "\\nsize: " + size + "\\nfree: " + free_vars)


def create_unary_node(graph, name, label, size, free_vars, child, operation):
    graph.node(name, label="size: " + size + "\\nfree: " + free_vars)
    graph.edge(name, child, label=operation)


def create_binary_node(graph, name, label, size, free_vars, lchild, rchild, operation):
    graph.node(name, label="size: " + size + "\\nfree: " + free_vars)
    graph.edge(name, lchild, label="\"" + operation + "\"")
    graph.edge(name, rchild, label="\"" + operation + "\"")


def print_config():
    print("Timeout: {0}".format(TIMEOUT))
    print("Number of formulas: {0}".format(FORMULAS))


def print_graph(filename, suf, data, names):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    graph = make_graph(name, data, names)
    graph.save()
    

def print_output(filename, suf, output, names):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    output = "operation;operand1;size1;operand2;size2;result;resultsize;minresult;minsize;fv\n" + output
    if SHOW_NAMES:
        res = ""
        for id, item in names.items():
            res = res + id + ";" + item[0] + ";\n"
        output = output + "\nAutomata\nid;name;\n" + res
    f = open(name + suf + ".csv", "w")
    f.write(output)
    f.close()


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./mona-stat.py [mona-bin] [formula folder]\n")


if __name__ == "__main__":
    main()
