"""
Z3 In-Class Exercise 1
Tue 9/8/22
"""

from z3 import *

# T + S + C = 10
# C + S - T = 6
# C + T - R = 4

# Here's a file you can often copy as a starting 
# point on a working program to solve some problem
# of interest. Here the problem is to compute and
# return a non-negative square root of argument, n 
def solve():
    
    t = Int("triangle")
    s = Int("square")
    c = Int("circle")
    
    EQ1 = (t + s + c == 10)
    EQ2 = (c + s - t == 6)
    EQ3 = (c + t - s == 4)
    
    s = Solver()
    s.add(And(EQ1, EQ2, EQ3))
    
    if (s.check() == sat):
        return s.model()
    return None

s = solve()
if (s) :
    print("The solution to the system is", s)
else :
    print("There is no solution to the system")