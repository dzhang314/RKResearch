#!/usr/bin/env python3
"""Characteristic-zero integer-polynomial check for the final-three cut.

All variables are formal. Neither numerical samples nor field order are used.
"""
from sympy import Matrix, expand, factor, symbols

s, v, P, Q, Z = symbols("s v P Q Z")
delta = 3-2*s
a = 2*s*v-3*s-v
b = 2*s*v*v-6*s-v*v
e0 = P+delta*s*Q-(v-1)
e1 = 2*(P+Q)-v*Z+delta
e2 = 3*(P+s*Q)-v*v*Z+delta
e3 = 4*(P+s*s*Q)-v**3*Z+delta+(s-1)*(v-1)
first = -e2+v*e1+(3-2*v)*e0
second = -e3+v*v*e1+(4-2*v*v)*e0

assert expand(first - (2*(s-1)*a*Q-2*(s-v)*(v-1))) == 0
assert expand(second - (2*(s-1)*b*Q-(s-v)*(v-1)*(2*v+3))) == 0
assert expand(2*b-(2*v+3)*a-3*(v-s)) == 0
assert expand(b*first-a*second-3*(s-v)**2*(v-1)) == 0

augmented = Matrix([
    [1, delta*s, 0, v-1],
    [2, 2, -v, -delta],
    [3, 3*s, -v*v, -delta],
    [4, 4*s*s, -v**3, -delta-(s-1)*(v-1)],
])
det = augmented.det()
assert expand(det-6*v*(s-1)*(s-v)**2*(v-1)) == 0
print("Augmented determinant:", factor(det))
print("Division-free residual:", factor(b*first-a*second))
