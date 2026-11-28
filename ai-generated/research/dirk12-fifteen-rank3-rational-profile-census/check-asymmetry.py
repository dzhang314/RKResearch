#!/usr/bin/env python3
from itertools import combinations
from math import isqrt
D = (-42,840,-5040,12600,-13860,5544)


def replay(p):
    assert all(p % d for d in range(2,isqrt(p)+1))

    def ev(f,x):
        return sum(c*pow(x,i,p) for i,c in enumerate(f))%p

    roots = [x for x in range(p) if ev(D,x)==0]
    assert len(roots)==5 and D[-1]%p and not ({0,1}&set(roots))

    def mul(f,g):
        r=[0]*(len(f)+len(g)-1)
        for i,c in enumerate(f):
            for j,d in enumerate(g):
                r[i+j]=(r[i+j]+c*d)%p
        return r

    def hull(xs):
        f=[1]
        for x in xs:
            f=mul(f,[-x%p,1])
        return f

    def integ(f,a,b):
        return sum(c*pow(i+1,-1,p)*(pow(b,i+1,p)-pow(a,i+1,p))
                   for i,c in enumerate(f))%p

    weights={}
    for z in roots:
        cardinal=hull(x for x in [0,*roots,1] if x != z)
        weights[z]=integ(cardinal,0,1)*pow(ev(cardinal,z),-1,p)%p
        assert weights[z]

    for a in roots:
        S=[z for z in roots if z!=a]
        U=hull(S)
        Uprime=[i*c%p for i,c in enumerate(U)][1:]
        q=mul([1,p-1],U)
        values=[]
        for z in S:
            f=integ(q,z,1)
            h=z*(z-a)*(z*z-a*z+a*a*pow(5,-1,p))%p
            assert f and h
            c=weights[z]*ev(Uprime,z)*f*h%p
            assert c
            values.append((z,c))
        slopes=[]
        extrap=[]
        for (z,f),(w,g) in combinations(values,2):
            slopes.append((g-f)%p)
            extrap.append(((w-z)*f + (a-z)*(g-f))%p)
        assert len(slopes)==len(extrap)==6 and all(slopes) and all(extrap)
        print(f"p={p}, a={a}: slopes={slopes}, at-a={extrap}")


if __name__ == '__main__':
    for p in (43,181):
        replay(p)
