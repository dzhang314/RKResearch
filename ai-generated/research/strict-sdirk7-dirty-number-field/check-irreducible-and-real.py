#!/usr/bin/env python3
"""Verify the modular irreducibility receipt and the exact real-root bracket."""
from pathlib import Path
from fractions import Fraction
from math import isqrt, gcd
from json import loads
from flint import fmpz_poly, fmpq, nmod_poly

here=Path(__file__).resolve().parent
integers=[int(x) for x in loads((here/'primitive-z-degree-324.json').read_text())]
H=fmpz_poly(integers)
parts=loads((here/'modular-irreducibility.json').read_text())


def primes_dividing(d):
    for t in range(2,d+1):
        if d%t==0 and all(t%i for i in range(2,isqrt(t)+1)):
            yield t


def verify_irred(f,p):
    d=int(f.degree())
    assert d>=1
    x=nmod_poly([0,1],p)%f
    cuts={d//q for q in primes_dividing(d)}
    a=x
    for i in range(1,d+1):
        a=a.pow_mod(p,f)
        if i in cuts:
            assert (a-x).gcd(f).degree()==0
    assert a==x


def irreducible():
    assert H.degree()==324 and gcd(*integers)==1
    n=int(H.degree())
    mask=(1<<(n+1))-1
    for a in parts:
        p=a['prime']
        assert p>=2 and all(p%i for i in range(2,isqrt(p)+1))
        target=nmod_poly([q%p for q in integers],p)
        assert target.degree()==n and target.gcd(target.derivative()).degree()==0
        product=nmod_poly([a['unit']],p)
        deg=[]
        for x in a['factors']:
            f=nmod_poly(x,p)
            verify_irred(f,p)
            product*=f
            deg.append(int(f.degree()))
        assert product==target
        assert sorted(deg)==a['degrees']
        possible=1
        for d in deg:
            possible|=possible<<d
        mask&=possible
    assert mask==1|(1<<n)
    assert H(8)%19==0 and H.derivative()(8)%19!=0
    print('irreducible of degree 324: verified six modular factorizations and the degree intersection')


def real_bracket():
    c=Fraction("-13.47182912965382985896954070588903942474935511356358646252600203248228")
    c=fmpq(c.numerator,c.denominator)
    r=fmpq(1,10**30)
    assert H(c-r)<0<H(c+r)
    D=H.derivative()
    upper=fmpz_poly([abs(a) for a in D.derivative()])(abs(c)+r)
    assert D(c)>r*upper
    print('exact real root: opposite rational signs and positive derivative on the radius-10^-30 interval')


if __name__=='__main__':
    irreducible()
    real_bracket()
