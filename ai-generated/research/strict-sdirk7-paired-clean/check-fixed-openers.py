#!/usr/bin/env python3
"""Exact paid quadrature and projective exclusions for openers 0, 2, 11."""
import sympy as S
from flint import fmpz_poly,nmod_poly
from math import prod
r,q,X=S.symbols('r q X')
H=35*q**3*r**3+70*q**3*r**2+35*q**3*r+70*q**2*r**4+70*q**2*r**3+5*q**2*r**2+3*q**2-70*q*r**5+95*q*r**3-39*q*r-6*q-3*r**2-6*r-3
a,b,c=S.Rational(1,7),S.Rational(1,5),S.Rational(1,3)
def ff(p):
    p=S.Poly(p,r).clear_denoms()[1].primitive()[1]
    return fmpz_poly([int(v) for v in reversed(p.all_coeffs())])
def report(e):
    f=ff(e)
    co,fac=f.factor()
    assert f==co*prod(p**e for p,e in fac)
    print('factors',[(p.degree(),e,str(p) if p.degree()==1 else None) for p,e in fac])
    rrs=[]
    for p,e in fac:
        if p.degree()==1:
            rrs.append(S.Rational(-int(p[0]),int(p[1])))
        else:
            for k in S.primerange(2,1000):
               P=nmod_poly(p.coeffs(),k)
               if P.degree()==p.degree() and not P.roots():
                   print('modproj',p.degree(),k)
                   break
            else:
               raise AssertionError(('no projective receipt',p.degree()))
    return rrs
R=r*r
for a_open in [0,2,11]:
    print('OPEN',a_open)
    d=a_open*(r+1)-1
    D=d*d
    U=S.cancel((a-(R+D)*b+R*D*c)/(b-(R+D)*c+R*D))
    N,L=[S.cancel(c0+c1*U) for c0,c1 in [(S.Poly(H,q).nth(0),S.Poly(H,q).nth(2)),(S.Poly(H,q).nth(1),S.Poly(H,q).nth(3))]]
    poli=S.cancel(N*N-U*L*L)
    print('U=',S.factor(U))
    for e in (S.denom(U),S.numer(poli)):
        assert set(report(e)) <= {0,-1}
    assert set(report(S.expand(H.subs(q,d)))) <= {0,-1}
print('The openers 0, 2, and 11 have no fully reflection-paired six-site clean grid.')
