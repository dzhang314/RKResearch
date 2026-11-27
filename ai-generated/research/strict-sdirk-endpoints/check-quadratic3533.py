"""Independent replay over F_3533[t]/(t^2 - 824*t + 524)."""
from functools import cache
import json
from pathlib import Path
from runpy import run_path
from math import isqrt

here = Path(__file__).parent
trees = run_path(str(here / 'check-six.py'))
data = json.loads((here / 'quadratic3533.json').read_text())
p, a, b = (data[k] for k in ('p', 'constant', 'linear'))
assert (p, a, b) == (3533, 3009, 824)
assert all(p % i for i in range(2, isqrt(p) + 1))
assert all((j*j-b*j-a) % p for j in range(p))

def add(x,y):
    return ((x[0]+y[0])%p, (x[1]+y[1])%p)

def mul(x,y):
    r,s = x
    t,u = y
    return ((r*t+a*s*u)%p, (r*u+s*t+b*s*u)%p)

def dot(u,v):
    ans = (0,0)
    for x,y in zip(u,v):
        ans = add(ans, mul(x,y))
    return ans

A, weights = data['A'], data['b']
assert len(A) == len(weights) == 6
assert all(len(row) == i+1 and row[-1] == [189,0] for i,row in enumerate(A))
assert all(x != [0,0] for x in weights)
@cache
def stage(tree):
    out = [(1,0)]*6
    for child in tree:
        sub = stage(child)
        out = [mul(x,dot(row,sub)) for x,row in zip(out,A)]
    return out

def pay(t):
    return mul((trees['factorial'](t),0), dot(weights,stage(t)))

layers = trees['trees_by_size'](6)
assert list(map(len,layers)) == [1,1,2,4,9,20]
assert all(pay(t)==(1,0) for layer in layers for t in layer)
assert pay(((),)*6) == (1230,0)
print('F_3533^2: irreducible modulus; 37/37 paid, seventh bush (1230,0) != (1,0)')
