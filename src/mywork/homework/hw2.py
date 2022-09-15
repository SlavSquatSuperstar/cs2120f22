"""
Eric Weng (qgt7zm)
CS 2120 - HW 2
Thur 9/15/22

Proving Inferrence Rules
"""

from z3 import *

################
# Test Methods #
################

# Prove that a proposition if valid (true for all interpretations)
def isValid(P) -> bool:
    s = Solver()
    s.add(Not(And(P)))
    return s.check() == unsat

# Return a solution of a proposition of satisfiable
def getModel(P) -> ModelRef:
    s = Solver()
    s.add(P)
    if s.check() == sat:
        return s.model()
    return None

# Returns a counterexample of a proposition
# Shows the negation of a proposition is satisfiable
def getCounterExample(P) -> ModelRef:
    return getModel(Not(And(P)))

def runTest(test: int, P):
    if isValid(P):
        print(f"Rule {test} is valid")
        # Print model 
        # Breaks if no variables are plugged directly into the method for some reason
        # i.e. getModel(C1) returns 'None' but getModel(And(X, Y)) returns something
        # m = getModel(P)
        # if m:
        #     print('Model:', m) 
        # else:
        #     print('No model')
    else:
        print(f"Rule {test} is not valid")
        # Print counterexample
        c = getCounterExample(P)
        if c:
            print('Counter example:', c) 
        else:
            print('No counter example')
    print('-' * 20)

########

if __name__ == "__main__":
    # Declare variables
    X, Y, Z = Bools(['X', 'Y', 'Z'])
    
    # 1. Affirming the Disjunct: X ∨ Y, X ⊢ ¬Y
    # If (X or Y) is true and X is true, then Y is false
    # Not valid because if both X and Y are true, (X or Y) will still be true
    # This is the difference between inclusive or and exclusive or
    C1 = Or(X, Y)
    C2 = And(Or(X, Y), X)
    runTest(1, Implies(C2, Not(Y)))
    
    # 2. And Introduction: X, Y ⊢ X ∧ Y
    # If X is true and Y is true, then (X and Y) is true
    C1 = And(X, Y)
    C2 = And(X, Y)
    runTest(2, Implies(C1,C2))
    
    # 3. And Elimination Left: X ∧ Y ⊢ X   
    # If (X and Y) is true, then X is true
    runTest(3, Implies(And(X, Y), X))
    
    # 4. And Elimination Right: X ∧ Y ⊢ Y
    # If (X and Y) is true, then Y is true
    runTest(4, Implies(And(X, Y), Y))
    
    # 5. Negation Elimination: ¬¬X ⊢ X
    # If not not X is true, then X is true
    runTest(5, Implies(Not(Not(X)), X))
    
    # 6. No Contradiction: ¬(X ∧ ¬X)
    # (X and not X) is not true (X cannot be both true and false)
    runTest(6, Not(And(X, Not(X))))
    
    # 7. Or Introduction Left: X ⊢ X ∨ Y
    # If X is true, then (X or Y) is true
    runTest(7, Implies(X, Or(X, Y)))
    
    # 8. Or Introduction Right: Y ⊢ X ∨ Y
    # If Y is true, then (X or Y) is true
    runTest(8, Implies(Y, Or(X, Y)))
    
    # 9. Denying the Antecedent: X → Y, ¬X ⊢ ¬Y
    # If X implies Y and X is false, then Y is false
    # Not valid because under a false premise, any conclusion can be drawn (false implies true)
    C1 = Implies(X, Y)
    C2 = And(C1, Not(X))
    runTest(9, Implies(C2, Not(Y)))
    
    # 10. Iff Introduction: X → Y, Y → X ⊢ X ↔ Y
    # If X implies Y and Y implies X, then X and Y imply each other (are equivalent)
    C1 = Implies(X, Y)
    C2 = Implies(Y, X)
    C3 = (X == Y)
    runTest(10, Implies(And(C1, C2), C3))
    
    # 11. Iff Elimination Left: X ↔ Y ⊢ X → Y
    # If X and Y are equivalent (imply each other), then X implies Y
    C1 = (X == Y)
    C2 = Implies(X, Y)
    runTest(11, Implies(C1, C2))
    
    # 12. Iff Elimination Right: X ↔ Y ⊢ X → Y
    # If X and Y are equivalent (imply each other), then Y implies X
    C1 = (X == Y)
    C2 = Implies(Y, X)
    runTest(12, Implies(C1, C2))
    
    # 13. Or Elimination: X ∨ Y, X → Z, Y → Z ⊢ Z
    # If (X or Y) is true, X implies Z, and Y implies Z, then Z is true
    C1 = Or(X, Y)
    C2 = Implies(X, Z)
    C3 = Implies(Y, Z)
    C4 = And(C1, C2, C3)
    runTest(13, Implies(C4, Z))
    
    # 14. Affirming the Conclusion, X → Y, Y ⊢ X
    # If X implies Y and Y is true, then X is true
    C1 = And(Implies(X, Y), Y)
    runTest(15, Implies(C1, X))
    
    # 15. Arrow Elimination: X → Y, X ⊢ Y
    # If X implies Y and X is true, then Y is true
    C1 = And(Implies(X, Y), X)
    runTest(15, Implies(C1, Y))
    
    # 16. Transitivity of Implies: X → Y, Y → Z ⊢ X → Z
    # If X implies Y, and Y implies Z, then X implies Z
    C1 = Implies(X, Y)
    C2 = Implies(Y, Z)
    C3 = And(C1, C2)
    C4 = Implies(X, Z)
    runTest(16, Implies(C3, C4))
    
    # 17. Converse: X → Y ⊢ Y → X
    # If X implies Y, then Y implies X
    # Not valid because false can imply true, but when the values are flipped, true cannot imply false
    C1 = Implies(X, Y)
    C2 = Implies(Y, X)
    runTest(17, Implies(C1, C2))
    
    # 18. Contrapositive: X → Y ⊢ ¬Y → ¬X
    # If X implies Y, then not Y implies X
    C1 = Implies(X, Y)
    C2 = Implies(Not(Y), Not(X))
    runTest(18, Implies(C1, C2))
    
    # 19. DeMorgan #1 (¬ distributes over ∨): ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
    # If (X or Y) is false, then X is false and Y is false
    C1 = Not(Or(X, Y))
    C2 = And(Not(X), Not(Y))
    runTest(19, Implies(C1, C2))
    
    # 20. DeMorgan #2 (¬ distributes over ∧): ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
    # If (X and Y) is false, then X is false or Y is false
    C1 = Not(And(X, Y))
    C2 = Or(Not(X), Not(Y))
    runTest(20, Implies(C1, C2))