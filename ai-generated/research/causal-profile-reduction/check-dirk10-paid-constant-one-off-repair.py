#!/usr/bin/env python3
"""Independent exact gcd over F_419. Requires SymPy."""
from itertools import permutations
import sympy as s

q,y=s.symbols('q y')
p=419
I=lambda P,x:s.integrate(s.expand(P),(y,0,x))
roots=tuple(x for x in range(p) if (42*x**4-84*x**3+56*x*x-14*x+1)%p==0)
assert roots==(67,141,279,353)
for a in (*roots,1):
    for x in roots:
        assert (10*a*a-12*a*x+3*x*x)%p

def modpoly(f):
    return s.Poly(sum(int(s.numer(c))*pow(int(s.denom(c)),-1,p)*q**i[0]
                      for i,c in s.Poly(f,q).terms()),q,modulus=p)

cases=0
for tau in roots:
    for x in roots:
        for a,b,u in permutations((1,tau,q)):
            P=y*(y-a)*(y-b)
            S=P*(y-u)
            expr=I(S,x) if x==tau else I(I(P,y),x)*S.subs(y,x)-I(P,x)*I(S,x)
            pair=modpoly(u*(4*a*b-a*a-b*b)-a*b*(a+b))
            assert pair.degree()==(1 if u==q else 2)
            assert s.gcd(pair,modpoly(expr)).degree()==0, (tau,x,a,b,u)
            cases+=1
assert cases==96
print(f'mod {p}: all {cases} orders with guarded leading terms pass common-root separation')
