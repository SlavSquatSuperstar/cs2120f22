"""
Z3 Practice Exercise 1
Tue 9/6/22
"""

from z3 import *

def isValid(P) :
    s = Solver()
    s.add(Not(P)) # << changes here
    return (s.check()==unsat) # iff !P is unsat (all false), then P is valid (all true)

X = Bool('X')
print(isValid(Or(X, Not(X)))) # X || !X == true for all X
print(isValid(And(X, Not(X)))) # X && !X == false for all X