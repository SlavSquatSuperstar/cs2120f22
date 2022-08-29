"""
Eric Weng (qgt7zm)
CS 2120 — HW 1
Thur 9/1/22

5-Queens Problem
Source: https://youtu.be/GdrI3IESyVY
"""

from z3 import Bool, And, Or, Not, Solver
from itertools import combinations


# Ensure no duplicates contained in a set
def at_most_one(literals) -> And:
    c = []
    for pair in combinations(literals, 2):
        a, b = pair
        # a, b = pair[0], pair[1]
        c += [Or(Not(a), Not(b))]
    return And(c)


def main():
    # Create the 5x5 grid
    grid = [[Bool(f"x_{i}_{j}") for j in range(5)] for i in range(5)]
    
    s = Solver()
    
    # Add constraints
    for row in range(5):
        s.add(Or(grid[row]))  # at least 5 queens in grid (1 per row)
        
    for y in range(5):
        col = []
        for x in range(5):
            col += [grid[x][y]]
        s.add(at_most_one(col))  # one queen per row
        s.add(at_most_one(grid[x]))  # one queen per column
    
    # One queen per diagonal (ignore corners = diagonals with length 1)
    for x in range(4):
        diags = [[], [], [], []]
        
        for y in range(5 - x):
            diags[0] += [grid[x + y][y]]
            diags[1] += [grid[x + y][4 - y]]
            diags[2] += [grid[4 - x - y][y]]
            diags[3] += [grid[4 - x - y][4 - y]]

        for d in diags:
            s.add(at_most_one(d))
    
    print(s.check())

    # Print model
    m = s.model()
    for x in range(5):
        line = ""
        for y in range(5):
            if m.evaluate(grid[x][y]):
                line += "x "
            else:
                line += ". "
        print(line)


if __name__ == "__main__":
    main()