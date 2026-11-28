#!/usr/bin/env python3
"""Exact arithmetic receipts for the two fixed width-15 prime densities."""
import ast
from fractions import Fraction
from math import comb, factorial
from pathlib import Path

import sympy as S

here = Path(__file__).resolve().parent
source = here.parent / "erk10-fifteen-two-pair-rational-closure" / "univariate.py"
defs = {}
for node in ast.parse(source.read_text()).body:
    if isinstance(node, ast.Assign) and len(node.targets) == 1:
        name = node.targets[0]
        if isinstance(name, ast.Name) and name.id in ("NONIC", "GRAM", "MN", "NN"):
            defs[name.id] = ast.literal_eval(node.value)
assert len(defs) == 4
x = S.Symbol("x")
N, B, M0, N0 = [S.Poly.from_list(defs[k], x, domain=S.ZZ)
                 for k in ("NONIC", "GRAM", "MN", "NN")]
T = M0**2 - 20*B*N0
assert T.all_coeffs()[::-1] == [21, -714, 10797, -94176, 515616, -1807200,
                               3951680, -4928000, 2688000]
print("Tail discriminant numerator:", T.all_coeffs()[::-1])

def check_frob(p, expected):
    mod = S.Poly(N, x, modulus=p)
    assert mod.degree() == 9 and S.gcd(mod, mod.diff()).degree() == 0
    mod = mod.monic()
    X = S.Poly(x, x, modulus=p)
    h = X
    degs = []
    for _ in range(9):
        h = (h**p) % mod
        degs.append(S.gcd(h-X, mod).degree())
    assert degs == expected
    return mod, degs

mod29, deg29 = check_frob(29, [0,0,0,0,0,0,0,0,9])
mod31, deg31 = check_frob(31, [0,2,0,2,0,2,7,2,0])
assert [int(c) % 31 for c in mod31.all_coeffs()[::-1]] == [11,30,3,24,7,19,5,17,25,1]
assert mod31 == S.Poly(x**2+8*x+4, x, modulus=31) * S.Poly(
    x**7+17*x**6+x**5+22*x**4+25*x**3+29*x**2+2*x+26, x, modulus=31)
print("Frobenius gcd degrees mod 29:", deg29)
print("Frobenius gcd degrees mod 31:", deg31)

resultant = int(N.resultant(T))
disc = int(N.discriminant())
assert resultant == 195940905549539664747294418998325590097920000000
assert resultant == 2**56*3**9*5**7*7**12*13**5*223*1543
assert disc == -18265097881475268102630310354125563743835258880000
assert disc % 13**3 == 0 and disc % 13**4 != 0
assert disc % 223 != 0 and int(N.LC()) % 223 != 0
assert S.isprime(223)
Np, Tp = (S.Poly(q, x, modulus=223) for q in (N, T))
assert S.gcd(Np, Np.diff()).degree() == 0
assert S.gcd(Np, Tp).monic() == S.Poly(x+130, x, modulus=223)
print("Resultant:", resultant)
print("Nonic discriminant:", disc)
print("At 223: resultant valuation 1; one common simple root, with monic gcd x+130")

# A permutation with k fixed positions has 2^(9-k) choices of signs
# making all its fixed positions flip the two members.
n = 9
derangements = [sum((-1)**j*factorial(k)//factorial(j) for j in range(k+1))
                for k in range(n+1)]
none = Fraction(sum(comb(n,k)*derangements[n-k]*2**(n-k) for k in range(n+1)),
                2**n*factorial(n))
assert none == sum(Fraction((-1)**j, 2**j*factorial(j)) for j in range(n+1))
assert none == Fraction(112690097,185794560)
union = 1-none*Fraction(7,8)
assert union == Fraction(99646543,212336640)
print("Signed-pair fixed-point fraction:", 1-none)
print("Union fixed-point fraction:", union)
