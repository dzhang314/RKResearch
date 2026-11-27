#!/usr/bin/env python3
"""Rebuild and verify the fixed real-algebraic DIRK10 chart in 32 prime fields."""
import argparse
import ast
from contextlib import redirect_stdout
from fractions import Fraction as Q
from functools import cache
from hashlib import sha256
from io import StringIO
from math import gcd, isqrt, prod
from pathlib import Path
from types import SimpleNamespace
import json

NAMES = [1, 1, 2, 4, 9, 20, 48, 115, 286, 719]
HERE = Path(__file__).resolve().parent
SRC = HERE.parent / 'causal-profile-reduction'

class R:
    mod = 0
    def __init__(self, x):
        if isinstance(x, R):
            self.x = x.x
        else:
            q = Q(x)
            self.x = q.numerator * pow(q.denominator, -1, self.mod) % self.mod
    def __add__(self, y):
        return R(self.x + R(y).x)
    __radd__ = __add__
    def __neg__(self):
        return R(-self.x)
    def __sub__(self, y):
        return self + -R(y)
    def __rsub__(self, y):
        return R(y) + -self
    def __mul__(self, y):
        return R(self.x * R(y).x)
    __rmul__ = __mul__
    def __pow__(self, n):
        return R(pow(self.x, n, self.mod))
    def __truediv__(self, y):
        return self * (R(y)**(-1))
    def __rtruediv__(self, y):
        return R(y) * (self**(-1))
    def __eq__(self, y):
        return self.x == R(y).x
    def __bool__(self):
        return self.x != 0

def definitions(filename, wanted, ns):
    """Reuse only corresponding function definitions, not another chart's setup."""
    filename = SRC / filename
    entire = ast.parse(filename.read_bytes(), filename=str(filename))
    functions = [node for node in entire.body
                 if isinstance(node, ast.FunctionDef) and node.name in wanted]
    assert {node.name for node in functions} == set(wanted)
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(filename), 'exec'), ns)

ns = dict(Q=Q, prod=prod, cache=cache)
definitions('check-dirk10-real-algebraic.py',
            ['ev', 'integral', 'polynomials_on_layout', 'solve_tableau', 'all_rooted'], ns)
separate = dict(cache=cache, prod=prod)
definitions('check-dirk10-zmod419.py', ['ordered', 'canonical', 'factorial', 'vertex_count'], separate)
binary_shapes = [sorted({separate['canonical'](tree) for tree in separate['ordered'](n)})
                 for n in range(1, 11)]
assert [len(layer) for layer in binary_shapes] == NAMES

def independent_orders(A, beta, modulus):
    @cache
    def evaluate(tree):
        children = [evaluate(child) for child in tree]
        return tuple(prod(sum(a*x for a, x in zip(row, w)) % modulus for w in children)
                     % modulus for row in A)
    return all(separate['factorial'](t)*sum(a*b for a,b in zip(beta,evaluate(t))) % modulus == 1
               for layer in binary_shapes for t in layer)

def reconstruct(p, k, l, m, n, known_star, known_derivative):
    assert p > 11 and all(p % d for d in range(2, isqrt(p)+1))
    R.mod = p
    a, b, u, xi = Q(1,10), Q(3,10), Q(3,5), Q(2)
    k,l,m,n = map(R, (k,l,m,n))
    f = 125*k**3-100*k**2-87*k+1314
    df = 375*k**2-200*k-87
    assert f == 0 and df == known_derivative and df
    y = (12948+3125*k)/(21210+7665*k)
    w = -25*(k**2-2*k-24)/(3*(434+77*k))
    Phi = [1,-14,56,-84,42]
    H = [0]+Phi
    M = [Q(17264,75),Q(-5656,15)]
    ev = ns['ev']
    def B(x):
        return (1-x)*(119-516*x+729*x**2-336*x**3)
    def elltarget(x):
        return -ev(M,x)*B(x)/ev(Phi,x)
    ly,lw=elltarget(y),elltarget(w)
    ell1=(lw-ly)/(w-y)
    def ell(x):
        return ly+(x-y)*ell1
    assert M[1]*336+42*ell1
    roots=[y,w,l,m,n]
    assert len({r.x for r in roots}) == 5
    assert all(ev(M,x)*B(x)+ev(Phi,x)*ell(x) == 0 for x in roots)
    V=SimpleNamespace(cast=R, zero=R(0), one=R(1))
    ns.update(a=a,b=b,u=u,xi=xi,y=y,w=w,lo=l,mi=m,hi=n,Phi=Phi,H=H,M=M,V=V)
    cv,beta,g,h,G=ns['polynomials_on_layout']()
    out=StringIO()
    with redirect_stdout(out):
        table=ns['solve_tableau'](cv,beta,g,h,G)
        assert ns['all_rooted'](table,beta)==NAMES
    ranks=[int(line.split()[-1]) for line in out.getvalue().splitlines()
           if line.startswith('linear block ')]
    assert sum(ranks)==79 and all(sum(row)==c for row,c in zip(table,cv))
    star=11*sum(b*c**10 for b,c in zip(beta,cv))-1
    assert star==known_star and star
    flat=[[a.x for a in row] for row in table]
    bs=[b.x for b in beta]
    assert independent_orders(flat,bs,p)
    return [c.x for c in cv], flat, bs

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--emit',type=Path,help='write all reconstructed prime-field tableaux')
args=parser.parse_args()
data=json.loads((HERE/'seeds.json').read_text())
literal=[]
primes=[row[0] for row in data['seeds']]
assert len(primes)==len(set(primes))==32
for seed in data['seeds']:
    p=seed[0]
    c,A,b=reconstruct(*seed)
    if p==59:
        ex=data['examples'][0]
        assert (c,A,b)==(ex['c'],ex['A'],ex['bvec'])
    literal.append(dict(p=p,c=c,A=A,b=b,scaled_order_11_star_defect=seed[5]))
    print(f'F{p}: simple front, five distinct roots, rank 79, both full replays, unit star {seed[5]}')
small,large=data['examples']
p=small['p']
q=large['p']
assert p==59 and q==p*p
assert [len(row) for row in large['A']]==list(range(1,12))
assert all(sum(row)%q == c for row,c in zip(large['A'],large['c']))
assert all([x%p for x in row] == old for row,old in zip(large['A'],small['A']))
assert [x%p for x in large['bvec']]==small['bvec']
assert [x%p for x in large['c']]==small['c']
assert independent_orders(large['A'],large['bvec'],q)
star=(11*sum(w*x**10 for w,x in zip(large['bvec'],large['c']))-1)%q
assert star==large['star'] and gcd(star,q)==1
print(f'Compatible literal lift modulo 59²: all 1,205 conditions, unit star {star}')

if args.emit is not None:
    args.emit.write_text(json.dumps(literal,separators=(',',':'))+'\n')
