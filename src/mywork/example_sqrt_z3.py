"""
Z3 Practice Exercise 2
Tue 9/6/22
"""

from z3 import *

# declarative definition of square root
# not deterministic, may return negative root if found first
def sqrt(n) :
    sqrtn = Real('sqrtn')
    s = Solver()
    s.add(sqrtn ** 2 == n) # << changes here
    if (s.check() == sat) :
        return s.model()[sqrtn]
    return -1

def neg_sqrt(n) :
    sqrtn = Real('sqrtn')
    s = Solver()
    s.add(sqrtn * sqrtn == n) # << changes here
    s.add(sqrtn <= 0)         # << changes here
    if (s.check() == sat) :
        return s.model()[sqrtn]
    return -1


def test_sqrt(n):
    print(f"sqrt({n}) = {sqrt(n)}")
    
def test_neg_sqrt(n):
    print(f"-sqrt({n}) = {neg_sqrt(n)}")

# Perfect square -> int
test_sqrt(9)
test_neg_sqrt(9)

# Imperfect square -> float
test_sqrt(2)
test_neg_sqrt(2)

# Zero -> 0
test_sqrt(0)
test_neg_sqrt(0)

# Negative number -> -1
test_sqrt(-9)
test_neg_sqrt(-9)