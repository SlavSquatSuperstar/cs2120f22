from z3 import *

s = Solver()

# Source: https://ericpony.github.io/z3py-tutorial/guide-examples.htm

# Solving math equations
x = Int('x')
y = Int('y')
solve(x > 2, y < 10, x + 2*y == 7)

# Simplifying math equations
print(simplify(x + y + 2*x + 3))
print(simplify(x < y + x + 2))
print(simplify(And(x + 1 >= 3, x**2 + x**2 + y**2 + 2 >= 5)))

# Solving boolean equations
x = Bool('x')
y = Bool('y')
z = Bool('z')

f1 = Or([x, y, z])
f2 = Or([Not(x), Not(y)])
f3 = Or([Not(y), Not(z)])

F = And([f1, f2, f3])

s = Solver()
s.add(F)
s.check()

m = s.model()
print(m)

# Puzzle
d = Int('dogs')
c = Int('cats')
m = Int('mice')
solve(d + c + m == 100, 1500*d + 100*c + 25*m == 10000, d >= 1, c >= 1, m >= 1)

# Class example
s = Solver()

X = Bool('x')
Y = Bool('y')
Z = Bool('z')
W = Bool('w')

s.add(Implies(Or(And(And(X, Y), Not(Z)), W), False))
# Implies(Or(And(And(X, Y), Not(Z)), W), False)
# (((X && Y) && (!Z)) || W) -> false

s.check()
m = s.model()
print(m)