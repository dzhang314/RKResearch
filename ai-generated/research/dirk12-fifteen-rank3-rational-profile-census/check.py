#!/usr/bin/env python3
"""Exact fixed Legendre root receipts for the singular rational profile."""
from math import isqrt
D = (-42,840,-5040,12600,-13860,5544)


def replay(p):
    assert all(p % d for d in range(2,isqrt(p)+1))

    def evaluate(f,x):
        return sum(c*pow(x,i,p) for i,c in enumerate(f)) % p

    roots = [x for x in range(p) if evaluate(D,x)==0]
    assert len(roots)==5 and 0 not in roots and 1 not in roots and D[-1] % p

    def mul(f,g):
        r=[0]*(len(f)+len(g)-1)
        for i,c in enumerate(f):
            for j,d in enumerate(g):
                r[i+j]=(r[i+j]+c*d)%p
        return r

    def integral(f,a,b):
        return sum(c*pow(i+1,-1,p)*(pow(b,i+1,p)-pow(a,i+1,p))
                   for i,c in enumerate(f)) % p

    diags = []
    table = []
    for b in roots:
        u = [1]
        for a in roots:
            if a != b:
                u = mul(u,[-a % p,1])
        diags.append(integral([0]+u,0,b))
        table.append([integral(mul([1,p-1],u),a,1) for a in roots if a!=b])

    assert all(diags) and len(diags)==5
    assert len(table)==5 and all(len(row)==4 and all(row) for row in table)
    print(f"p={p}: roots {roots}; 5 diagonal numerators; 20 reverse anomaly gates")
    print("diagonal residues:",*diags)
    for b,row in zip(roots,table):
        print(b,*row)


if __name__ == '__main__':
    for p in (43,181):
        replay(p)
