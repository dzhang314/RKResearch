#!/usr/bin/env python3
"""Independent, integer-only order replay after reading the literal fractions."""
from fractions import Fraction as F
from functools import cache
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
N=24
D=28868710429988352000000000000
COUNTS=[1,1,2,4,9,20,48,115,286,719,1842,4766]

@cache
def root_forest(n, lower=(1,())):
    if not n:return ((),)
    return tuple((r,)+tail for k in range(lower[0],n+1)
                 for r in root_forest(k-1) if (k,r)>=lower
                 for tail in root_forest(n-k,(k,r)))

@cache
def order(t):return 1+sum(order(v)for v in t)

@cache
def density(t):return order(t)*prod(density(v)for v in t)

def run():
    x=json.loads((HERE/'tableau.json').read_text())
    A=[tuple(map(F,r))for r in x['A']]
    w=tuple(map(F,x['b']))
    assert len(A)==len(w)==N and all(len(r)==i for i,r in enumerate(A))
    assert len({r+(F(0),)*(N-len(r))for r in A})==N
    assert lcm(*(z.denominator for z in w),*(z.denominator for r in A for z in r))==D
    assert D==2**21*3**10*5**12*7**2*11**7 and factorial(12)**7%D==0
    # Cut the integer stage matrix to its actual nonzero support.
    A0=[tuple((j,int(D*a))for j,a in enumerate(row)if a)for row in A]
    w0=tuple((j,int(D*b))for j,b in enumerate(w)if b)
    assert all(F(v,D)==A[i][j]for i,row in enumerate(A0)for j,v in row)
    assert all(F(v,D)==w[i]for i,v in w0)
    @cache
    def phi(t):
        values=[act(s)for s in t]
        return tuple(prod(row[i]for row in values)for i in range(N))
    @cache
    def act(t):
        v=phi(t)
        return tuple(sum(y*v[j]for j,y in row)for row in A0)
    def mass(t):return sum(v*phi(t)[i]for i,v in w0)
    for n,m in enumerate(COUNTS,1):
        fam=root_forest(n-1)
        assert len(fam)==m
        for t in fam:
            assert order(t)==n and density(t)*mass(t)==D**n,(n,t)
    assert sum(COUNTS)==7813
    print('24 strict distinct rows; all 7,813 rooted conditions verified.')
    print('Common denominator:',D,'= 2^21 3^10 5^12 7^2 11^7, divides (12!)^7.')
    t1=((),)*12
    t2=((),)*6+(((),)*5,)
    assert [order(t1),order(t2)]==[13,13] and [density(t1),density(t2)]==[13,78]
    e1,e2=[F(density(t)*mass(t),D**13)-1 for t in (t1,t2)]
    assert (e1,e2)==(F(1161187,1373847552),F(24764718696320825821075,351704973312))
    n1,n2=e1.numerator,e2.numerator
    assert gcd(n1,n2)==1
    v=pow(n2,-1,n1)
    if 2*v>n1:v-=n1
    u=(1-v*n2)//n1
    assert u*n1+v*n2==1
    a,b=u*e1.denominator,v*e2.denominator
    assert a*e1+b*e2==1
    assert D**13%e1.denominator==D**13%e2.denominator==0
    print('Order-13 factorial-scaled defects:',e1,e2)
    print('Integer blend coefficients:',a,b)

if __name__=='__main__':run()
