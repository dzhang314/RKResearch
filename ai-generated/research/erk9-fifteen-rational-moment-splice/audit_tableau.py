#!/usr/bin/env python3
"""Replay the literal rational tableau as a scaled integer matrix.
No construction routine, floating-point arithmetic, or Python packages are used.
"""
from argparse import ArgumentParser
from fractions import Fraction
from functools import lru_cache
from math import lcm, prod, isqrt
from pathlib import Path
import json

EXPECTED_D = 167647010724053278598487250944000
EXPECTED_FACTORS = {2:14,3:6,5:3,7:1,11:2,13:5,19:1,43:1,47:1,59:1,83:1,241:1,7879:1}


def certify(source):
    obj=json.loads(source.read_text())
    n=len(obj["A"])
    assert n==len(obj["b"])==15
    assert all(len(r)==i for i,r in enumerate(obj["A"]))
    rows=[list(map(Fraction,r)) for r in obj["A"]]
    weights=list(map(Fraction,obj["b"]))
    D=lcm(*(x.denominator for r in rows for x in r),*(x.denominator for x in weights))
    assert D==EXPECTED_D==prod(p**a for p,a in EXPECTED_FACTORS.items())
    assert all(not any(p%k==0 for k in range(2,isqrt(p)+1)) for p in EXPECTED_FACTORS)
    A=[tuple(int(x*D) for x in r) for r in rows]
    b=tuple(int(x*D) for x in weights)
    assert len(set(r+(0,)*(n-len(r)) for r in A))==n
    def act(v):
        return tuple(sum(x*y for x,y in zip(r,v)) for r in A)
    def out(v):
        return sum(x*y for x,y in zip(b,v))
    profiles=[(1,)*n]
    action=[act(profiles[0])]
    children=[()]
    order=[1]
    forest=[1]
    counts=[1]
    assert out(profiles[0])==D
    for s in range(2,10):
        prefix=len(children)
        @lru_cache(None)
        def subforests(left,last):
            if left==0:
                return ((),)
            return tuple((j,*rest) for j in range(last,prefix) if order[j]<=left
                         for rest in subforests(left-order[j],j))
        group=subforests(s-1,0)
        counts.append(len(group))
        for ch in group:
            v=tuple(prod(action[j][i] for j in ch) for i in range(n))
            f=prod(order[j]*forest[j] for j in ch)
            assert s*f*out(v)==D**s,(s,ch)
            profiles.append(v)
            action.append(act(v))
            children.append(ch)
            order.append(s)
            forest.append(f)
    assert counts==[1,1,2,4,9,20,48,115,286] and sum(counts)==486
    v=(1,)*n
    for _ in range(9): v=act(v)
    tall=Fraction(prod(range(1,11))*out(v),D**10)-1
    bush=Fraction(10*out(tuple(s**9 for s in act((1,)*n))),D**10)-1
    assert tall==Fraction(-29627,5184)
    assert bush==Fraction(5,9984)
    assert D%tall.denominator==D%bush.denominator==0
    assert 2*tall.numerator+11851*bush.numerator==1
    print("15 strict, distinct physical rows")
    print("Common denominator:",D)
    print("Prime powers:",EXPECTED_FACTORS)
    print("Exact rooted residual checks:",counts,"(total",sum(counts),")")
    print("Tenth tall defect:",tall,"; tenth bush defect:",bush)
    print("Unit-defect Bézout: 2·(−29627)+11851·5=1")


if __name__=="__main__":
    z=ArgumentParser(description=__doc__)
    z.add_argument("tableau",type=Path,nargs="?",default=Path(__file__).with_name("tableau.json"))
    certify(z.parse_args().tableau)
