#!/usr/bin/env python3
"""Exact QQ resultant/gcd and normalizations for one paired debut."""

import sympy as s

X, S, P = s.symbols("X S P")
F = 42*X**4-84*X**3+56*X**2-14*X+1
J = 3*X**4-4*S*X**3+6*P*X**2  # 12 times the primitive
Q = X**2-S*X+P
f = s.Poly(s.rem(F, Q, X), X)
j = s.Poly(s.rem(J, Q, X), X)
f0, f1 = (f.coeff_monomial(X**i) for i in range(2))
j0, j1 = (j.coeff_monomial(X**i) for i in range(2))
C = s.expand(f1*j0-f0*j1)
assert C == 84*P**3*S-252*P**3+56*P**2*S+42*P**2-14*P*S**2-4*P*S+S**3
D, N = 6*P-S*S, P*S
fU = 42*N**4-84*N**3*D+56*N**2*D**2-14*N*D**3+D**4
jU = 3*N**4-4*S*N**3*D+6*P*N*N*D*D
E = s.cancel((fU*j0-jU*f0)/P)
EE = s.cancel((fU*j1-jU*f1)/S)
for f in [C, E, EE]:
    s.Poly(f, P, S, domain=s.QQ)

G = (2016*S**8+46200*S**7-253204*S**6+530922*S**5-587973*S**4
     +376686*S**3-140670*S**2+28512*S-2430)
Gp = [709443967905,-6582222614817,24916972066389,-48858014778303,
      51867299523606,-27886169534188,5605993175160,240326547552]
den = 7990348842
product = sum(a*S**i for i, a in enumerate(Gp))/den
h1, h2 = S-1, 3*S*S-6*S+2
h4 = 224*S**4-672*S**3+672*S*S-252*S+27
r0 = s.Poly(s.resultant(C, E, P), S)
r1 = s.Poly(s.resultant(C, EE, P), S)
assert r0.gcd(r1).monic() == s.Poly(S**17*h1*h2*h4*G, S).monic()

for f, product0 in [(h1,s.Rational(1,4)), (h2,S/2-s.Rational(1,6)),
                    (h4,2*S*S/9), (G,product)]:
    basis = s.groebner([f,C,E,EE], P,S,domain=s.QQ)
    monic = s.Poly(f,S,domain=s.QQ).monic().as_expr()
    assert list(basis) == [P-product0,monic]
    assert all(basis.reduce(e)[1] == 0 for e in (f,C,E,EE))
    if f in (h1,h2):
        assert basis.reduce(S*S-4*P)[1] == 0
    if f == h4:
        assert basis.reduce(N*N-S*N*D+P*D*D)[1] == 0

print("Exact QQ: same octic sum and its explicit product after three degenerate factors are discarded")
