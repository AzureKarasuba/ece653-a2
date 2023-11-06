# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys

import io 
from functools import reduce
import z3

from . import ast, int


class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()

def add_all_constraints(solver,pcList):
    for c in pcList:
        solver.add(c)

class SymExec(ast.AstVisitor):
    def __init__(self):
        # initialize with empty list of SymState()
        self.while_count = 0
        self.statesList = list()

    def run(self, ast, state):
        self.statesList.append(state)
        self.visit (ast, state=state)
        return self.statesList

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)

        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs

        assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])

        fn = None
        base = None
        if node.op == "and":
            fn = lambda x, y: z3.And(x,y)
            base = True
        elif node.op == "or":
            fn = lambda x, y: z3.Or(x,y)
            base = False

        assert fn is not None
        return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)
    
    def visit_SkipStmt(self, node, *args, **kwargs):
        for st in self.statesList:
            return self.statesList

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        for st in self.statesList:
            print(st)
        return self.statesList

    def visit_AsgnStmt(self, node, *args, **kwargs):
        for st in self.statesList:
            st.env[node.lhs.name] = self.visit(node.rhs,*args, **kwargs)
        return self.statesList

    def visit_IfStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        newList = []
        for st in self.statesList:
            solver = z3.Solver()
            add_all_constraints(solver,st.path)
            solver.add(cond)

            # if sat, take then_branch
            if solver.check() == z3.sat:
                thenState = st.fork()
                thenState.add_pc(cond)

                thenState = self.visit(node.then_stmt, state=thenState, *args, **kwargs)
                newList.extend(thenState)
                
            #else branch
            if(node.has_else()):
                solver = z3.Solver()
                add_all_constraints(solver,st.path)
                solver.add(z3.Not(cond))

                if solver.check() == z3.sat:
                    elseState = st.fork()
                    elseState.add_pc(z3.Not(cond))
                    
                    elseState = self.visit(node.else_stmt, state=elseState, *args, **kwargs)
                    newList.extend(elseState)
        self.statesList = newList
        return self.statesList
                

    def visit_WhileStmt(self, node, *args, **kwargs):
        # exit when loop executed for more than 10 times
        newList = []
        for st in self.statesList:
            # current condition
            cond = self.visit(node.cond, *args, **kwargs)

            solver = z3.Solver()
            add_all_constraints(solver,st.path)
            solver.add(z3.Not(cond))
            # if not cond is feasible, add a new state that not cond is added to the pc
            if solver.check() == z3.sat:
                breakState = st.fork()
                breakState.add_pc(z3.Not(cond))
                newList.append(breakState)

            solver.reset()
            add_all_constraints(solver,st.path)
            solver.add(cond)
    
            # if cond is feasible, execute the body
            if solver.check() == z3.sat:
                if self.while_count < 10:
                    body = self.visit(node.body,state=st *args, **kwargs)
                    if(isinstance(body,list)):
                        for b in body:
                            b.add_pc(cond)
                    else:
                        body.add_pc(cond)
                    newList.extend(body)
                    self.while_count += 1
                    return self.visit(node, *args, **kwargs)
            else:
                # cond is not feasible, exit the loop and proceed to next state
                newList.append(st)
                self.while_count = 0
                continue
 
        #update the self statesList with new List after finishing processing one state
        self.statesList = newList
        return self.statesList

    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        cond = self.visit(node.cond, *args, **kwargs)
        for st in self.statesList:
            # all path constraints by the point
            solver = z3.Solver()
            add_all_constraints(solver,st.path)
            solver.add(cond)

            # if unsat, print error message
            if solver.check() == z3.unsat:
                assert False, "Assertion error: " + str(node)
            else:
                st.path.append(cond)
        return self.statesList


    def visit_AssumeStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        for st in self.statesList:
            st.path.append(cond)
        return self.statesList


    def visit_HavocStmt(self, node, *args, **kwargs):
        for st in self.statesList:
            for v in node.vars:
                st.env[v.name] = z3.FreshInt(v.name)
        return self.statesList

    def visit_StmtList(self, node, *args, **kwargs):
        for stmt in node.stmts:
            self.statesList = self.visit(stmt, *args, **kwargs)
        return self.statesList


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
