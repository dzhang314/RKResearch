#!/usr/bin/env python3
"""Independent split-prime replay of the five-ghost fixed-grid gates."""
from itertools import permutations

P=1013
D6=(-42,840,-5040,12600,-13860,5544)
ROOTS=(347,468,507,546,667)
SITES=(*ROOTS,1)

def val(coeff,x):
    r=0
    for a in reversed(coeff):
        r=(r*x+a)%P
    return r

def integ_hull(nodes,x):
    c=[1]
    for a in nodes:
        d=[0]*(len(c)+1)
        for i,b in enumerate(c):
            d[i]-=a*b
            d[i+1]+=b
        c=[z%P for z in d]
    return sum(a*pow(k,-1,P)*pow(x,k,P)
               for k,a in enumerate(c,1))%P

def main():
    assert all(P%d for d in range(2,32)) and P%5544
    assert tuple(x for x in range(P) if val(D6,x)==0)==ROOTS
    counts=[0,0,0]
    for u,v in permutations(SITES,2):
        assert (10*v*v-12*u*v+3*u*u)%P
        counts[0]+=1
    for a,v,u in permutations(SITES,3):
        assert integ_hull((0,a,v,u),a)
        counts[1]+=1
    for a,d,v,u in permutations(SITES,4):
        assert integ_hull((0,d,v,u),a)
        counts[2]+=1
    assert counts==[30,120,360]
    for name,n in zip(("third debut","anchored quartic","unanchored quartic"),counts):
        print(f"mod {P}, {name}: {n}")

if __name__=="__main__":
    main()
