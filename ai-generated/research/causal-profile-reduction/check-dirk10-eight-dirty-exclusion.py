#!/usr/bin/env python3
"""Replay the exact r=8 DIRK10 scalar exclusion, with no floating point.

Requires SymPy. The DIRK/order-to-scalar bridge is proved separately in
dirk-order10-eight-dirty-exclusion.md. No tableau is assumed or generated.
"""
from math import factorial
from sympy import Matrix, Rational as Q, div, expand, factorint, rem, symbols

x, y = symbols("x y")
r = y*(1-y)
jacobi = 42*r**2 - 14*r + 1
J = jacobi/42
d = (5+42*r)/120
weight = 7*(1+6*r)/60

def reduced(p):
    return rem(expand(p), jacobi, y)

def I(p):
    a = expand(p).integrate(x)
    return a-a.subs(x,0)

def M(p):
    a = expand(p).integrate(x)
    return a.subs(x,1)-a.subs(x,0)

# Exact fixed diagonal and weight, after clearing the clean indicator.
U = div(J.subs(y,x), x-y, x)[0]
Uy = U.subs(x,y)
assert reduced(I(x*U).subs(x,y) - d*y*Uy) == 0
assert reduced(M(x*(1-x)*U) - weight*y*(1-y)*Uy) == 0
assert Q(42)*(-Q(5,42))**2 - 14*(-Q(5,42)) + 1 == Q(137,42)

F = [x*x*(x-y)*(5*x-3*y), x*x*((4*y-12*d)*x-(3*y-12*d)*y)]
G = [p.subs({x:1-x,y:1-y},simultaneous=True) for p in F]
for i,f in enumerate(F):
    assert expand(I(f).subs(x,y)-d*f.subs(x,y)) == 0
    assert expand(f.subs(x,y)-(0 if i == 0 else y**4)) == 0

def row(p,f,g):
    fg = f*g
    if p == 0:
        return 126000*(M(fg)-weight*fg.subs(x,y))
    if p == 1:
        return 252000*M((x-y)*fg)
    return 15120000*M((I(f)-d*f)*g)

T = Matrix([[reduced(row(p,f,g)) for f in F for g in G] for p in range(3)])
T_expected = Matrix([
    [100*(162*y**2-162*y+41),
     15*(1512*y**3-3032*y**2+1866*y-345),
     -15*(1512*y**3-1504*y**2+338*y-1),
     3*(756*y**2-756*y+187)],
    [-600*(2*y-1)*(39*y**2-39*y+11),
     20*(1812*y**3-3249*y**2+1855*y-332),
     20*(1812*y**3-2187*y**2+793*y-86),
     -3*(2*y-1)*(1454*y**2-1454*y+329)],
    [100*(1524*y**2-1524*y+353),
     15*(7884*y**3-17494*y**2+11688*y-2355),
     -15*(7884*y**3-6158*y**2+352*y+277),
     3*(9870*y**2-9870*y+2239)],
])
assert T == T_expected.applyfunc(expand)
N = [
    3*(95466*y**2-95466*y+21965),
    30*(93100*y**3-93625*y**2+21651*y-166),
    -30*(93100*y**3-185675*y**2+113701*y-20960),
    200*(11235*y**2-11235*y+2641),
]
for i,n in enumerate(N):
    raw = (-1)**i*T[:,[j for j in range(4) if j != i]].det()
    assert reduced(49*raw-75000*n) == 0
assert reduced(N[0]*N[3]-N[1]*N[2]-1250*(2729314*r-646271)) == 0
a,b = 2729314,646271
norm = a*a-14*a*b+42*b*b
assert norm == 296864705802
assert factorint(norm) == {2:1,3:1,7:1,62969:1,112249:1}

# The integer Beta tables used by the native scalar statement.
# The second raises the degree of the left monomial by one.
beta = [
    [[2520*Q(factorial(i+2+k)*factorial(j+2),factorial(i+j+5+k))
      for j in range(3)] for i in range(3)]
    for k in range(2)
]
assert beta == [
    [[84,42,24],[42,18,9],[24,9,4]],
    [[42,18,9],[24,9,4],[15,5,2]],
]
print("r=8: fixed clean data, three moment rows, rank-two null line verified")
print("characteristic guards beyond the paid primes: 137, 62969, 112249")
