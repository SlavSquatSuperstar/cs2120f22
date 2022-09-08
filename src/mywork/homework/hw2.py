"""
Eric Weng (qgt7zm)
CS 2120 - HW 2
<Due Date>

Proving Inferrences
"""

from z3 import *

##########
# SAT Methods
##########

# Prove that a proposition if valid (true for all interpretations)
def isValid(*P) -> bool:
    s = Solver()
    s.add(Not(And(P)))
    return s.check() == unsat

# Return a solution of a proposition of satisfiable
def getModel(*P) -> ModelRef:
    s = Solver()
    s.add(P)
    if s.check() == sat:
        return s.model()
    return None

# Returns a counterexample of a proposition
# Shows the negation of a proposition is satisfiable
def getCounterExample(*P) -> ModelRef:
    return getModel(Not(And(P)))

##########
# Print Methods
##########

def printValid(*P):
    if isValid(*P):
        print('Valid')
    else:
        print('Not Valid')

def printModel(*P):
    m = getModel(*P)
    if m:
        print('Model:', m) 
    else:
        print('No model')

def printCounterExample(*P):
    c = getCounterExample(*P)
    if c:
        print('Counter example:', c) 
    else:
        print('No counter example')

def runTest(test: int, *P):
    if isValid(*P):
        print(f"Test {test} is valid")
        printModel(*P)
    else:
        print(f"Test {test} is not valid")
        printCounterExample(*P)

########

def main():
    # Declare variables
    X, Y, Z = Bools('X, Y, Z')
    
    # 1. Affirming the disjunct: X ∨ Y, X ⊢ ¬Y
    # If X or Y is true, then X being true means Y is false
    # Not valid because X and Y can both be true
    # The preposition is actually the XOR operator
    C1 = Or(X, Y)
    C2 = Implies(X, Not(Y))
    runTest(1, C1, C2)


if __name__ == "__main__":
    main()