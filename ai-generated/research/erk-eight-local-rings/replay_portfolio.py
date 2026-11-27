#!/usr/bin/env python3
"""Standalone integer replay for the three exact ERK8 denominator charts."""
from fractions import Fraction as Q
from functools import cache
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json,sys
sys.set_int_max_str_digits(0)
here=Path(__file__).resolve().parent
old=here.parent/'erk-eight-rank3-four'/'tableau.json'
if len(sys.argv)>1:
    old=Path(sys.argv[1])
tables=[json.loads(old.read_text()),*json.loads((here/'portfolio.json').read_text())]
T=[set(),{()}]
for n in range(2,10):
    T.append({tuple(sorted(u+(v,)))
        for k in range(1,n) for u in T[k] for v in T[n-k]})
assert [len(T[n]) for n in range(1,10)]==[1,1,2,4,9,20,48,115,286]

@cache
def order(t):return 1+sum(order(u) for u in t)
@cache
def tfact(t):return order(t)*prod(tfact(u) for u in t)

def check(t):
    A=[[Q(x) for x in r] for r in t['A']]
    b=tuple(map(Q,t['b']))
    assert len(A)==len(b)==11 and [len(r) for r in A]==list(range(11))
    D=lcm(*(x.denominator for r in A for x in r),*(x.denominator for x in b))
    if 'D' in t:
        assert D==t['D']
    M=tuple(tuple(int(x*D) for x in r) for r in A)
    w=tuple(int(x*D) for x in b)
    @cache
    def state(t):
        if not t:return (1,)*11
        x,y=state(t[0]),state(t[1:])
        return tuple(y[i]*sum(a*z for a,z in zip(M[i],x) if a) for i in range(11))
    def paid(t):return Q(tfact(t)*sum(x*y for x,y in zip(w,state(t))), D**order(t))
    assert all(paid(t)==1 for n in range(1,9) for t in T[n])
    bush=paid(((),)*8)-1
    assert bush == Q(t.get('bush9',t.get('bush9_normalized_defect')))
    nth_gcd=gcd(*(abs((paid(t)-1).numerator) for t in T[9]))
    assert nth_gcd==1
    print(f'11 stages, den = {D.bit_length()} bits: 200 paid conditions and unit ideal of ninth-order residual numerators')
    return D

D=[check(t) for t in tables]
g=gcd(*D)
assert g==6970199040==2**10*3**4*5*7**5
assert factorial(8)**5 % g==0
assert D[1]%11!=0 and D[2]%13!=0
print(f'hand-audited three-chart denominator gcd = {g} = 2^10·3^4·5·7^5')
