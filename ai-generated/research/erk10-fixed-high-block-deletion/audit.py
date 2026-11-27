#!/usr/bin/env python3
"""Exact finite facts for the fixed-high-block deletion obstruction."""
from argparse import ArgumentParser
from hashlib import sha256
from fractions import Fraction as F
from math import prod, factorial
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
PINS={
    'erk10-seventeen-half-port/tableau.json':
      '663c5fbfb6b303a61d30ec39830628b715f88e3349979fe0813327405bc318c4',
    'erk10-seventeen-half-port/seed6-prefix.json':
      '49e854cdda01628174223f46ba8bc9da03e1b8706b774380f7a4db9820a4f370',
}

def main():
    p=ArgumentParser()
    p.add_argument('--research-root',type=Path,default=HERE.parent)
    a=p.parse_args()
    root=a.research_root
    for rel,h in PINS.items():assert sha256((root/rel).read_bytes()).hexdigest()==h
    sys.path.insert(0,str(root/'erk10-seventeen-half-port-family'))
    from check_family import factory
    (A,U,V,w),_=factory(root/'erk10-seventeen-half-port')
    x=tuple(map(sum,A))
    assert x==tuple(map(F,('0','1/3','2/3','1/3','1','1/2','1','1','1/2',
                            '1/6','2/3','5/6','1/3','-1/6','-1/3','-1/2','1')))
    assert all(not sum(r)for r in (*U,*V))
    grid=tuple(F(j,6)for j in range(-3,7))
    assert set(x)==set(grid)==set(x[:-1])
    assert all((factorial(10)**2) % abs((u-v).numerator)==0 for u in grid for v in grid if u!=v)
    old=set(x[:9]);dups=[i for i in range(9,16)if x[i]in old]
    assert dups==[10,12] and {x[i]for i in dups}=={F(1,3),F(2,3)}
    assert all(x.count(x[i])==1 for i in range(9,16)if i not in dups)
    assert all(sum(wi*xi**j for wi,xi in zip(w,x))==F(1,j+1)for j in range(10))
    P=lambda z:(z-F(1,3))*(z-F(2,3))
    Q=lambda z:prod(z-r for r in old)
    y=list(map(Q,x))
    assert all(v==0 for v in y[:9]) and all(P(x[i])==0 for i in dups)
    assert w[-1]==F(7,150) and P(x[-1])==F(2,9)
    dot=lambda v,z:sum(r*s for r,s in zip(v,z))
    assert dot(A[-1],y)==F(-10,441) and dot(U[-1],y)==dot(V[-1],y)==0
    gap=w[-1]*P(x[-1])*dot(A[-1],y)
    assert gap==F(-2,8505) and 6**7*gap==F(-2304,35)
    assert all(factorial(10)**3%abs(v)==0 for v in (*[abs(gap.numerator),gap.denominator],35,2304))
    print('All ten scalar sites and paid gaps checked.')
    print('Unchanged old clock hull zeros; only duplicated high clocks are 1/3 and 2/3.')
    print('Reference last contribution (all affine parameters):',gap)
    print('With integer-polynomial scaling:',6**7*gap)

if __name__=='__main__':main()
