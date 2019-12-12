#!/usr/bin/env python3

"""
 Script for predicting automata sizes in formula construction.
 @title predict.py
 @author Ondřej Valeš, 2019
"""

import sys
import getopt
import subprocess
import os
import graphviz
import math

FORMULAS = 400
MAX_LABEL = 2000
CREATE_FILES = True

PRED_CALL = "PredCall"
SKIP_OP = ["Negate", "Restrict", PRED_CALL]
NULLARY_OP = [
    "True", "False", "Empty", "FirstOrder", "Const",
    "Singleton", "BoolVar", "In", "Eq1", "Eq2", "Sub2",
    "Less1", "LessEq1", "EqPlus2", "EqMinus2", "EqMin",
    "EqMax", "EqPlus1", "EqMinus1", "Union", "Inter",
    "SetMinus", "EqPlusModulo", "EqMinusModulo", "PresbConst"
]
UNARY_OP = ["Project"]

CONST_SIZES = {
    "True" : 2,
    "False" : 2,
    "Empty" : 3,
    "FirstOrder" : 3,
    "Singleton" : 4,
    "BoolVar" : 3,
    "In" : 4,
    "Eq1" : 4,
    "Eq2" : 3,
    "Sub2" : 3,
    "Less1" : 5,
    "LessEq1" : 5,
    "EqPlus2" : 4,
    "EqMinus2" : 6,
    "EqMin" : 6,
    "EqMax" : 5,
    "EqMinus1" : 6,
    "Union" : 3,
    "Inter" : 3,
    "SetMinus" : 3,
    "EqPlusModulo" : 13,
    "EqMinusModulo" : 12,
}

CALC_SIZES = {
    "Const" : lambda x : x + 4,
    "EqPlus1" : lambda x : x + 4,
    "PresbConst" : lambda x : 3 if x < 1 else 4 + int(math.log2(x))
}

PREDICT = {
    "And" : [
        lambda x : 1.02 * x - 0.20,
        lambda x : 0.99 * x - 0.36,
        lambda x : 0.91 * x - 0.25,
        lambda x : 0.90 * x - 0.30,
        lambda x : 0.87 * x - 0.51,
        lambda x : 0.87 * x - 1.00,
        lambda x : 0.86 * x - 1.28,
        lambda x : 1.00 * x - 2.18,
        lambda x : 1.00 * x - 2.23,
        lambda x : 1.00 * x - 2.75,
        lambda x : 1.00 * x - 3.03,
        lambda x : 1.00 * x - 3.32,
    ],
    "Or" : [
        lambda x : 1.07 * x - 0.32,
        lambda x : 1.06 * x - 0.31,
        lambda x : 0.93 * x - 0.28,
        lambda x : 0.36 * x + 0.49,
        lambda x : 0.05 * x + 1.29,
    ],
    "Impl" : [
        lambda x : 1.00 * x + 0.00,
        lambda x : 0.89 * x - 0.21,
        lambda x : 0.51 * x - 0.30,
        lambda x : 0.95 * x - 1.13,
    ],
    "Biimpl" : [
        lambda x : 1.08 * x - 0.32,
        lambda x : 1.26 * x - 0.74,
        lambda x : 0.13 * x + 0.73,
    ]
}

MAX_SHARED = {k : len(PREDICT[k]) for k in PREDICT}

class Formula:
    _counter = 1
    @staticmethod
    def _skip_unused(formula):
        while True:
            if formula[-1] == ']':
                formula, repls = formula[:-1].rsplit('[', 1)
                repls
                for repl in reversed(repls.split(',')):
                    old, new = repl.split('->')
                    formula = formula.replace(old, new)
            oper, formula = formula[:-1].split('(', 1)
            if oper == PRED_CALL:
                formula = formula.split(',', 1)[1]
                formula
            if oper not in SKIP_OP:
                return oper, formula
    

    @staticmethod
    def _split_index(formula):
        ind = 0
        cnt = 0
        while True:
            if formula[ind] == ',' and cnt == 0:
                break
            if formula[ind] in ['(', '[']:
                cnt += 1
            if formula[ind] in [')', ']']:
                cnt -= 1
            ind += 1
        return ind


    def __init__(self, formula):
        self.id = str(Formula._counter)
        Formula._counter += 1
        oper, formula = Formula._skip_unused(formula)

        self.name = oper + "(" + formula + ")"
        self.oper = oper

        if self.oper in NULLARY_OP:
            self.__init_nullary__(formula)
        elif self.oper in UNARY_OP:
            self.__init_unary__(formula)
        else:
            ind = Formula._split_index(formula)
            self.__init_binary__(formula[:ind], formula[ind + 1:])
  

    def __init_nullary__(self, formula):
        self.right = None
        self.left = None
        if self.oper in CONST_SIZES:
            self.size = CONST_SIZES[self.oper]
            self.fv = set(formula.split(','))
        else:
            n = int(formula.split(',')[-1])
            self.fv = set(formula.split(',')[:-1])
            self.size = CALC_SIZES[self.oper](n)
        self.total_size = self.size


    def __init_unary__(self, formula):
        self.var, formula = formula.split(',', 1)
        self.left = Formula(formula)
        self.right = None
        self.fv = self.left._get_fv()
        self.fv.discard(self.var)
        self.size = max(1, int(self.left.size * 0.83))
        self.total_size = self.size + self.left.total_size
    

    def __init_binary__(self, lformula, rformula):
        self.left = Formula(lformula)
        self.right = Formula(rformula)
        self.fv = self.left._get_fv().union(self.right._get_fv())
        shared_vars = len(self.left.fv) + len(self.right.fv) - len(self.fv)
        shared_vars = min(shared_vars, MAX_SHARED[self.oper])
        self.size = PREDICT[self.oper][shared_vars](self.left.size * self.right.size)
        self.size = max(1, int(self.size * 0.66))
        self.total_size = self.size + self.left.total_size + self.right.total_size


    def _get_fv(self):
        return self.fv.copy()


    def to_graph(self, name):
        graph = graphviz.Digraph(name)
        self._to_graph(graph)
        return graph


    def _to_graph(self, graph):
        if self.left is None:
            create_leaf_node(graph, self.id, self.name, str(self.size), self.fv)
        elif self.right is None:
            self.left._to_graph(graph)
            create_unary_node(graph, self.id, self.name, str(self.size), self.fv,
                              self.left.id, self.oper)
        else:
            self.left._to_graph(graph)
            self.right._to_graph(graph)
            create_binary_node(graph, self.id, self.name, str(self.size), self.fv,
                               self.left.id, self.right.id, self.oper)


def main():
    global FORMULAS
    monabin, formulafolder, resultfolder = parse_args(sys.argv)
    print_config()

    files = get_files(formulafolder)
    for monafile in files:
        try:
            filename = os.path.join(formulafolder, monafile)
            mona_output = process_file(filename, monabin)      
            formula = Formula(mona_output.split('\n')[-3])
            if CREATE_FILES:
                print_graph(filename, resultfolder, "", formula)
                print("\tDONE")
            else: print("\t{0}".format(formula.total_size))
        except subprocess.CalledProcessError as _:
            print("\tERROR")
            continue


def parse_args(args):
    global FORMULAS
    if len(sys.argv) < 4:
        help_err()
        sys.exit()

    try:
        opts, _ = getopt.getopt(sys.argv[4:], "f:", ["formulas="])
    except getopt.GetoptError as _:
        help_err()
        sys.exit()

    for o, a in opts:
        if o in ("-f", "--formulas"):
            FORMULAS = int(a)

    return args[1:4]


def get_files(formulafolder):
    global FORMULAS
    files = [f for f in os.listdir(formulafolder) \
        if os.path.isfile(os.path.join(formulafolder, f)) and \
            f.endswith(".mona")]
    files.sort()
    return files[:FORMULAS]


def process_file(filename, monabin):
    print(filename, end="")
    sys.stdout.flush()
    return subprocess.check_output([monabin, "-a", filename]).decode("utf-8")


def print_graph(filename, folder, suf, formula):
    base = os.path.basename(filename)
    name = os.path.splitext(base)[0]
    name = os.path.join(folder, name)
    graph = formula.to_graph(name)
    graph.render(filename=name, format="svg", cleanup=True)
    graph.save(filename=name + ".dot")


def create_leaf_node(graph, name, label, size, free_vars):
    graph.node(name, label=label + "\\n" + format_node(name, size, free_vars), tooltip=label)


def create_unary_node(graph, name, label, size, free_vars, child, operation):
    global MAX_LABEL
    label = label[:MAX_LABEL]
    graph.node(name, label=format_node(name, size, free_vars), tooltip=label)
    graph.edge(name, child, label=operation, arrowhead="none")


def create_binary_node(graph, name, label, size, free_vars, lchild, rchild, operation):
    global MAX_LABEL
    label = label[:MAX_LABEL]
    graph.node(name, label=format_node(name, size, free_vars), tooltip=label)
    graph.edge(name, lchild, label=graphviz.nohtml(operation), arrowhead="none")
    graph.edge(name, rchild, label=graphviz.nohtml(operation), arrowhead="none")


def format_node(name, size, free_vars):
    return size + " states\\n" + ','.join(free_vars) + "\\n" + name


def print_config():
    print("Number of formulas: {0}".format(FORMULAS))


def help_err():
    sys.stderr.write("Bad input arguments. \nFormat: ./predict.py " +
                     "[mona-bin] [formula folder] [output folder]\n")


if __name__ == "__main__":
    main()
