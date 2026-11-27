#!/usr/bin/env python3
"""Exact canonical quartic, good reduction and polar-axis receipt."""
import sympy as S
from itertools import product
t,x,A,B,C,l,m,n=S.symbols('t x A B C l m n')
F=(t**3-4*t**2+5*t-2)*x**3+(-9*t**3+27*t**2-21*t+6)*x**2+(18*t**3-36*t**2+12*t)*x-6*t**3+6*t**2
G=S.Poly(sum(v*C**(i+j-2)*A**(3-j)*B**(3-i) for (i,j),v in S.Poly(F,t,x).terms()),A,B,C)
assert G.total_degree()==4
assert S.cancel(G.as_expr().subs({A:t,B:x,C:t*x})-t*x*F)==0
print('Canonical quartic:',G.as_expr(),flush=True)
def smooth(P,p):
    for k,v in enumerate(P.gens):
        patch=[S.Poly(S.diff(P.as_expr(),x).subs(v,1),*[q for q in P.gens if q!=v],modulus=p).as_expr() for x in P.gens]
        if list(S.groebner(patch,*[q for q in P.gens if q!=v],modulus=p))!=[1]:
            return False
    return True
def vecs(p,n):
    for r in range(n):
        for v in product(range(p),repeat=n-r-1):
            yield (0,)*r+(1,)+v
def ev(poly,pt,p):
    from math import prod
    return sum(int(c)*prod(pow(x,i,p) for i,x in zip(js,pt)) for js,c in poly.terms())%p
def involutions(P,p):
    defs=[S.Poly(S.diff(P.as_expr(),q),A,B,C,modulus=p) for q in (A,B,C)]
    pts=list(vecs(p,3))
    out=[]
    for v in pts:
        if not ev(P,v,p):
            continue
        g=[ev(f,v,p) for f in defs]
        # Eliminate a gradient pivot and check the remaining binary
        # cubic identically; no evaluation-as-polynomial ambiguity.
        j=next(i for i in range(3) if g[i])
        comb=sum(vv*f.as_expr() for vv,f in zip(v,defs))
        dd=sum(g[i]*x for i,x in enumerate((A,B,C)) if i!=j)
        inv=pow(g[j],-1,p)
        rem=S.Poly(comb.subs((A,B,C)[j],-inv*dd),*[x for i,x in enumerate((A,B,C)) if i!=j], modulus=p)
        if not rem:
            out.append(v)
    return out
assert smooth(G,5)
assert involutions(G,5)==[]
print('Good mod-5 reduction, and no projective polar center for an involution.')
