from collections import Counter
from fractions import Fraction as Q
from functools import cache
from math import factorial, gcd, lcm, prod
from pathlib import Path
import json, sys

obj = json.loads(Path(sys.argv[1]).read_text())
A = [list(map(Q, row)) for row in obj['A']]
b = list(map(Q, obj['b']))
s = len(b)
assert s == len(A) == 24
if [len(row) for row in A] == list(range(s)):
    assert len(set(tuple(row + [Q(0)]*(s-i)) for i,row in enumerate(A))) == s
else:
    assert all(len(row)==s and not any(row[i:]) for i,row in enumerate(A))
    assert len(set(map(tuple,A))) == s
    A = [row[:j] for j,row in enumerate(A)]
D = lcm(*(v.denominator for row in A for v in row), *(v.denominator for v in b))
assert D == 28868710429988352000000000000
assert (factorial(12)**12)%D == 0
M = [tuple(int(D*x) for x in row) for row in A]
w = tuple(int(D*x) for x in b)
sparse = [tuple((j,a) for j,a in enumerate(row) if a) for row in M]

@cache
def size(t):
    return 1+sum(map(size,t))
@cache
def gamma(t):
    return size(t)*prod(map(gamma,t))
@cache
def action(t):
    u=phi(t)
    return tuple(sum(a*u[j] for j,a in row) for row in sparse)
@cache
def phi(t):
    children = [action(q) for q in t]
    return tuple(prod(v[i] for v in children) for i in range(s))

T={1:{()}}
for n in range(2,13):
    T[n] = {tuple(sorted(parent+(child,)))
            for k in range(1,n) for parent in T[n-k] for child in T[k]}
counts=[len(T[j]) for j in range(1,13)]
assert counts==[1,1,2,4,9,20,48,115,286,719,1842,4766]
for n,layer in T.items():
    dn=D**n
    for t in layer:
        assert size(t)==n and gamma(t)*sum(a*x for a,x in zip(w,phi(t)))==dn,(n,t)

leaf=()
t1=(leaf,)*12
t2=(leaf,)*6 + ((leaf,)*5,)
assert size(t1)==size(t2)==13
def next_defect(t):
    return Q(gamma(t)*sum(a*x for a,x in zip(w,phi(t))),D**13)-1
x,y=map(next_defect,(t1,t2))
assert (x,y)==(Q(1161187,1373847552),Q(24764718696320825821075,351704973312))
assert gcd(x.numerator,y.numerator)==1 and D**13%x.denominator==D**13%y.denominator==0
print('24 literal distinct strict rows, D',D,'with only factorial-paid primes')
print('all',sum(counts),'denominator-cleared rooted conditions',counts)
print('two tree-factorial-scaled order-13 defects',x,y,'with coprime numerators')
