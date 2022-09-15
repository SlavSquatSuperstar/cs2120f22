"""
Eric Weng (qgt7zm)
CS 2120 - HW 2
Thur 9/15/22

Proving Inference Rules
"""

from z3 import *

test_count = 1

################
# Test Methods #
################

# Prove that a proposition if valid (true for all interpretations)
def is_valid(P) -> bool:
    s = Solver()
    s.add(Not(P))
    return s.check() == unsat

# Return a solution of a proposition of satisfiable
def get_model(P) -> ModelRef:
    s = Solver()
    s.add(P)
    if s.check() == sat:
        return s.model()
    return None

# Returns a counterexample of a proposition
# Shows the negation of a proposition is satisfiable
def get_counter_example(P) -> ModelRef:
    return get_model(Not(P))

def run_test(P):
    global test_count
    if test_count == 1:
        print('+' + ('-' * 36) + '+')
    
    if is_valid(P):
        print(f"Rule {test_count} is valid")
        # Print model 
        # For some reason, breaks if no variables are plugged directly into the method
        # i.e. get_model(C1) returns 'None' but get_model(And(X, Y)) returns something
        # m = get_model(P)
        # if m:
        #     print('Model:', m) 
        # else:
        #     print('No model')
    else:
        print(f"Rule {test_count} is not valid")
        # Print counterexample
        c = get_counter_example(P)
        if c:
            print('Counter example:', c) 
        else:
            print('No counter example')
    
    print('+' + ('-' * 36) + '+')
    test_count += 1

###############
# Main Method #
###############

if __name__ == "__main__":
    # Declare variables
    X, Y, Z = Bools(['X', 'Y', 'Z'])
    
    # 1. Affirming the Disjunct: X ∨ Y, X ⊢ ¬Y
    # If (X or Y) is true and X is true, then Y is false
    # Not valid, because if both X and Y are true, (X or Y) will still be true
    # For example, if is is raining or I am in Virginia, knowing that it is raining
    # does not tell whether or not I am in Virginia.
    C1A = And(Or(X, Y), X)
    C1 = Implies(C1A, Not(Y))
    run_test(C1)
    
    # 2. And Introduction: X, Y ⊢ X ∧ Y
    # If X is true and Y is true, then (X and Y) is true
    # Valid
    C2 = Implies(And(X, Y), And(X, Y))
    run_test(C2)
    
    # 3. And Elimination Left: X ∧ Y ⊢ X   
    # If (X and Y) is true, then X is true
    # Valid
    C3 = Implies(And(X, Y), X)
    run_test(C3)
    
    # 4. And Elimination Right: X ∧ Y ⊢ Y
    # If (X and Y) is true, then Y is true
    # Valid
    C4 = Implies(And(X, Y), Y)
    run_test(Implies(And(X, Y), Y))
    
    # 5. Negation Elimination: ¬¬X ⊢ X
    # If not not X is true, then X is true
    # Valid
    C5 = Implies(Not(Not(X)), X)
    run_test(C5)
    
    # 6. No Contradiction: ¬(X ∧ ¬X)
    # (X and not X) is not true (X cannot be both true and false)
    # Valid
    C6 = Not(And(X, Not(X)))
    run_test(C6)
    
    # 7. Or Introduction Left: X ⊢ X ∨ Y
    # If X is true, then (X or Y) is true
    # Valid
    C7 = Implies(X, Or(X, Y))
    run_test(C7)
    
    # 8. Or Introduction Right: Y ⊢ X ∨ Y
    # If Y is true, then (X or Y) is true
    # Valid
    C8 = Implies(Y, Or(X, Y))
    run_test(C8)
    
    # 9. Denying the Antecedent: X → Y, ¬X ⊢ ¬Y
    # If X implies Y and X is false, then Y is false
    # Not valid, because false may imply false or true.
    # For example, under a false premise (I am on Mars), I can draw a true conclusion
    # (the Empire State Building is in New York), and we would have no way of proving or disproving it.
    C9A = And(Implies(X, Y), Not(X))
    C9 = Implies(C9A, Not(Y))
    run_test(C9)
    
    # 10. Iff Introduction: X → Y, Y → X ⊢ X ↔ Y
    # If X implies Y and Y implies X, then X and Y imply each other (are equivalent)
    # Valid
    C10A = Implies(X, Y)
    C10B = Implies(Y, X)
    C10 = Implies(And(C10A, C10B), (X == Y))
    # C10 = Implies(And(C10A, C10B), And(C10A, C10B)) # this is the same
    run_test(C10)
    
    # 11. Iff Elimination Left: X ↔ Y ⊢ X → Y
    # If X and Y are equivalent (imply each other), then X implies Y
    # ValiD
    C11 = Implies((X == Y), Implies(X, Y))
    run_test(C11)
    
    # 12. Iff Elimination Right: X ↔ Y ⊢ X → Y
    # If X and Y are equivalent (imply each other), then Y implies X
    # Valid
    C12 = Implies((X == Y), Implies(Y, X))
    run_test(C12)
    
    # 13. Or Elimination: X ∨ Y, X → Z, Y → Z ⊢ Z
    # If (X or Y) is true, X implies Z, and Y implies Z, then Z is true
    # Valid
    C13A = Or(X, Y)
    C13B = Implies(X, Z)
    C13C = Implies(Y, Z)
    C13 = Implies(And(C13A, C13B, C13C), Z)
    run_test(C13)
    
    # 14. Affirming the Conclusion, X → Y, Y ⊢ X
    # If X implies Y and Y is true, then X is true
    # Not valid, because true or false also imply true
    # For example, I can say "If I am on Earth, then the sky is blue" and
    # "If I am on Mars, then the sky is blue". Knowing the sky is blue does not help us
    # judge the truthfullness of the premise.
    C14 = Implies(And(Implies(X, Y), Y), X)
    run_test(C14)
    
    # 15. Arrow Elimination: X → Y, X ⊢ Y
    # If X implies Y and X is true, then Y is true
    # Valid
    C15 = Implies(And(Implies(X, Y), X), Y)
    run_test(C15)
    
    # 16. Transitivity of Implies: X → Y, Y → Z ⊢ X → Z
    # If X implies Y, and Y implies Z, then X implies Z
    # Valid
    C16A = And(Implies(X, Y), Implies(Y, Z))
    C16 = Implies(C16A, Implies(X, Z))
    run_test(C16)
    
    # 17. Converse: X → Y ⊢ Y → X
    # If X implies Y, then Y implies X
    # Not valid because false can imply true, but true cannot imply false
    # For example, I can say "If I am on Mars, then the sky is blue", but I cannot say
    # "If the sky is blue, then I am on Mars".
    C17 = Implies(Implies(X, Y), Implies(Y, X))
    run_test(C17)
    
    # 18. Contrapositive: X → Y ⊢ ¬Y → ¬X
    # If X implies Y, then (not Y) implies X
    # Valid
    C18A = Implies(X, Y)
    C18B = Implies(Not(Y), Not(X))
    C18 = Implies(C18A, C18B)
    run_test(C18)
    
    # 19. DeMorgan #1 (¬ distributes over ∨): ¬(X ∨ Y) ↔ ¬X ∧ ¬Y
    # If (X or Y) is false, then X is false and Y is false
    # Valid
    C19A = Not(Or(X, Y))
    C19B = And(Not(X), Not(Y))
    C19 = Implies(C19A, C19B)
    run_test(C19)
    
    # 20. DeMorgan #2 (¬ distributes over ∧): ¬(X ∧ Y) ↔ ¬X ∨ ¬Y
    # If (X and Y) is false, then X is false or Y is false
    # Valid
    C20A = Not(And(X, Y))
    C20B = Or(Not(X), Not(Y))
    C20 = Implies(C20A, C20B)
    run_test(C20)
