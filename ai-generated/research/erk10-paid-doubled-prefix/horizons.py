#!/usr/bin/env python3
"""Complete old-horizon candidates for an integral doubled-prefix pure-high splice."""
from fractions import Fraction as Q
from math import gcd,prod
from collections import Counter
import sympy as S
def smooth(limit):
    M={1}
    for p in (2,3,5,7):
       M={a*p**i for a in M for i in range(limit.bit_length())if a*p**i<=limit}
    return M
def units():
    H=smooth(5000)
    R=[(a,b,a+b)for a in H for b in H if a<=b and a+b in H and gcd(a,b)==1]
    assert len(R)==63
    L={x for a,b,c in R for x in (Q(a,c),Q(b,c),Q(c,a),Q(c,b),Q(-a,b),Q(-b,a))}
    assert len(L)==375
    return L
def paid(a):
    n=Q(a).denominator
    for p in (2,3,5,7):
       while n%p==0:n//=p
    return n==1
def unit(a):
    return bool(a) and paid(a) and paid(1/a)
def poly(xs):
    out=[Q(1)]
    for x in xs:
        r=[Q(0)]*(len(out)+1)
        for i,a in enumerate(out):
            r[i]-=a*x;r[i+1]+=a
        out=r
    return out
def scalar(theta,v):
    pts=(0,1,2,v)
    M=[]
    for x in pts:
        xs=tuple(z for z in pts if z!=x)
        M.append(sum(a*theta**(j+1)/(j+1)for j,a in enumerate(poly(xs)))/prod(x-z for z in xs))
    assert all(sum(a*x**j for x,a in zip(pts,M))==theta**(j+1)/(j+1)for j in range(5))
    return M
def main():
    T=S.Symbol('T')
    H=Counter();L=[]
    for u in sorted(units()):
        v=1+u
        if v in (0,1,2):continue
        assert unit(v-1)and unit(v-2)
        q=S.Poly(12*T**3-45*T*T+40*T-15*v*(T-2)**2,T)
        for theta in map(Q,S.ground_roots(q)):
            if theta in (0,1,2):continue
            H['cubic rational roots']+=1
            N=12*theta**2-45*theta+40
            P=scalar(theta,v)
            print('exact nondegenerate root',theta,v,'N',N,'aggregate masses',list(map(str,P)))
            if not(paid(theta)and unit(theta-2)and unit(N)):continue
            H['paid horizon and separation conditions']+=1
            if not all(paid(x)for x in P):continue
            H['paid old aggregate masses']+=1
            L.append((theta,v))
    print('complete census',dict(H),'surviving theta,v',sorted(L))
    assert sorted(L)==[(Q(5,2),Q(5,3))]
if __name__=='__main__':
    main()
