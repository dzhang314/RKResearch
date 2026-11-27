#!/usr/bin/env python3
"""Verify the second rational tableau and its denominator/defect receipts."""
from fractions import Fraction as F
from functools import lru_cache
from math import gcd, lcm, prod, factorial
from pathlib import Path
from argparse import ArgumentParser
import json

D1 = 167647010724053278598487250944000
D2 = 60872310928282105497538809785677333251786646659783059681175834555608375037426392441416230346497300480000
P = 10450944000


def audit(path):
    j=json.loads(path.read_text())
    n=len(j["A"])
    assert n==len(j["b"])==15 and all(len(r)==i for i,r in enumerate(j["A"]))
    row=[tuple(map(F,r))for r in j["A"]]
    wt=tuple(map(F,j["b"]))
    D=lcm(*(c.denominator for r in row for c in r),*(q.denominator for q in wt))
    assert D==D2 and gcd(D1,D2)==P
    assert factorial(9)**3%P==0
    A=[tuple(int(c*D)for c in r)for r in row]
    b=tuple(int(q*D)for q in wt)
    assert len(set(r+(0,)*(n-len(r))for r in A))==n
    def act(v):return tuple(sum(a*x for a,x in zip(r,v))for r in A)
    def out(v):return sum(x*y for x,y in zip(b,v))
    W=[act((1,)*n)]
    G,Ff=[1],[1]
    sizes=[1]
    assert out((1,)*n)==D
    for s in range(2,10):
        init=len(G)
        @lru_cache(None)
        def forest(rem,lo):
            if rem==0:return ((),)
            return tuple((k,)+ch for k in range(lo,init)if G[k]<=rem
                         for ch in forest(rem-G[k],k))
        trees=forest(s-1,0)
        sizes.append(len(trees))
        for ch in trees:
            v=tuple(prod(W[k][i]for k in ch)for i in range(n))
            f=s*prod(Ff[k]for k in ch)
            assert f*out(v)==D**s
            W.append(act(v)); G.append(s); Ff.append(f)
    assert sum(sizes)==486
    v=(1,)*n
    for _ in range(9):v=act(v)
    rt=F(factorial(10)*out(v),D**10)-1
    rb=F(10*out(tuple(u**9 for u in W[0])),D**10)-1
    rm=F(70*out(tuple(a*a*c for a,c in zip(W[0],act(tuple(u**6 for u in W[0]))))),D**10)-1
    assert (rt,rb,rm)==(F(-2945609,320),F(71019553,1282889664),F(-24755745567906941,5885687017987200))
    assert gcd(rt.numerator,rb.numerator)==gcd(rm.numerator,rb.numerator)==1
    assert all(D**10%x.denominator==0 for x in (rt,rb,rm))
    print("15 distinct strict physical rows; exact order conditions:",sizes)
    print("Second common denominator:",D)
    print("D1/D2 gcd:",P,"divides (9!)^3")
    print("Tenth tall, bush and mixed bush attachment:",rt,rb,rm)
    print("Tall/bush and mixed/bush cleared numerator gcds are both one.")


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("tableau",type=Path,nargs="?",default=Path(__file__).with_name("second-tableau.json"))
    audit(p.parse_args().tableau)
