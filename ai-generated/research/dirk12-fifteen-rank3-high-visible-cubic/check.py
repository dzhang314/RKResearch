#!/usr/bin/env python3
"""Two exact finite-field receipts for the high visible DIRK12 branch."""
from itertools import combinations
from math import isqrt

DERIVATIVE = (-42,840,-5040,12600,-13860,5544)


def replay(p):
    assert all(p % d for d in range(2,isqrt(p)+1))
    def mul(f,g):
        h=[0]*(len(f)+len(g)-1)
        for i,a in enumerate(f):
            for j,b in enumerate(g):
                h[i+j]=(h[i+j]+a*b)%p
        return h
    def hull(xs):
        f=[1]
        for x in xs:
            f=mul(f,[-x%p,1])
        return f
    def ev(f,x):
        return sum(c*pow(x,i,p) for i,c in enumerate(f))%p
    def integral(f,u):
        return sum(a*pow(i+1,-1,p)*pow(u,i+1,p) for i,a in enumerate(f))%p
    def gcd(f,g):
        while g:
            r=list(f)
            inv=pow(g[-1],-1,p)
            while len(r)>=len(g):
                i=len(r)-len(g)
                v=r[-1]*inv%p
                for j,c in enumerate(g):
                    r[i+j]=(r[i+j]-v*c)%p
                while r and not r[-1]:
                    r.pop()
            f,g=g,r
        return [a*pow(f[-1],-1,p)%p for a in f]
    roots=tuple(i for i in range(p) if ev(DERIVATIVE,i)==0)
    assert len(roots)==5 and DERIVATIVE[-1] % p and 0 not in roots and 1 not in roots
    assert set(roots)=={(1-i)%p for i in roots}
    gcds=[]
    for k in (2,3):
        for roots_of_factor in combinations(roots,k):
            h=hull(roots_of_factor)
            a=[c*pow(i+2,-1,p)%p for i,c in enumerate(h)]
            b=[c*pow(i+3,-1,p)%p for i,c in enumerate(h)]
            assert a[-1] and b[-1] and gcd(a,b)==[1]
            gcds.append((k,roots_of_factor))
    determinants=[]
    for chosen in combinations(roots,2):
        h=hull(chosen)
        for u in (*roots,1):
            if u in chosen:
                continue
            a,b,c=[integral([0]*i+h,u) for i in (1,2,3)]
            s=(a*c-b*b)%p
            assert s
            determinants.append(s)
    assert len(gcds)==20 and len(determinants)==40
    print(f"{p}: D roots {roots}; 20 fixed-degree gcds = 1; 40 determinants nonzero")
    print("determinant residues:",*determinants)


if __name__ == '__main__':
    for p in (43,181):
        replay(p)
