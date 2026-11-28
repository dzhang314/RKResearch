#!/usr/bin/env python3
"""Independent integer replay of an exact rational mirrored tableau."""
from itertools import combinations_with_replacement,groupby,product
from functools import cache
from fractions import Fraction as Q
from math import prod,lcm,gcd
from pathlib import Path
import json,sys
def partitions(n,start=1):
    if not n:
        yield ()
    for a in range(start,n+1):
        for t in partitions(n-a,a):
            yield (a,*t)
@cache
def trees(n):
    out=[]
    for p in partitions(n-1):
        pools=[tuple(combinations_with_replacement(trees(k),len(tuple(u))))for k,u in groupby(p)]
        for s in product(*pools):out.append(tuple(t for c in s for t in c))
    return tuple(out)
@cache
def grade(t):
    return 1+sum(grade(u)for u in t)
@cache
def fac(t):
    return grade(t)*prod(fac(u)for u in t)
def check(f):
    j=json.loads(Path(f).read_text())
    D=int(j['denominator'])
    m=[[Q(z)for z in r]for r in j['A']];b=list(map(Q,j['b']))
    assert len(m)==len(b)==16 and all(len(r)==i for i,r in enumerate(m))
    assert D==lcm(*(x.denominator for r in m+[b]for x in r))
    assert len({tuple(r+[0]*(16-len(r)))for r in m})==16
    A=[[int(D*z)for z in r]for r in m];B=[int(D*z)for z in b]
    @cache
    def E(t):
        s=[M(u)for u in t]
        return tuple(prod(v[i]for v in s)for i in range(16))
    @cache
    def M(t):
        x=E(t)
        return tuple(sum(z*w for z,w in zip(r,x))for r in A)
    def output(t):
        return fac(t)*sum(a*x for a,x in zip(B,E(t)))
    n=0
    for k in range(1,11):
        for t in trees(k):
            assert grade(t)==k and output(t)==D**k
            n+=1
    assert n==1205
    bush=((),)*10
    bushdef=Q(output(bush)-D**11,D**11)
    assert bushdef==Q(j['next_failure_value']) and bushdef
    mixed=((),(),(),(),((),)*5)
    other=Q(output(mixed)-D**11,D**11)
    gn=gcd(bushdef.numerator,other.numerator)
    print(f,'literal checks',n,'D',D,'bush defect',bushdef,'mixed defect',other,'coprimality',gn)
if __name__=='__main__':
    for f in sys.argv[1:]:check(f)
