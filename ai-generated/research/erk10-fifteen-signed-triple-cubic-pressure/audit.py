#!/usr/bin/env python3
"""Independent determinant, boundary minors and mod-19 audit, stdlib only."""
from fractions import Fraction as F
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod

N=3
O=(0,)*N

class P(dict):
    def __init__(self,x=0):
        if isinstance(x,dict): super().__init__({k:F(v) for k,v in x.items() if v})
        else: super().__init__({O:F(x)} if x else {})
    def __neg__(self):return P({i:-q for i,q in self.items()})
    def __add__(self,y):
        w=dict(self)
        for i,q in P(y).items():w[i]=w.get(i,0)+q
        return P(w)
    __radd__=__add__
    def __sub__(self,y):return self+-P(y)
    def __rsub__(self,y):return P(y)+-self
    def __mul__(self,y):
        w={}
        for i,q in self.items():
            for j,r in P(y).items():
                k=tuple(a+b for a,b in zip(i,j))
                w[k]=w.get(k,0)+q*r
        return P(w)
    __rmul__=__mul__
    def __pow__(self,n):return prod([self]*n,start=P(1))
    def value(self,args):return sum(q*prod(z**j for z,j in zip(args,i)) for i,q in self.items())
    def integrate_y(self):return sum((P({(0,i,j):q/(k+1)}) for (k,i,j),q in self.items()),P())
    def mod_value(self,args,p):
        z=0
        for i,q in self.items():
            z+=q.numerator*pow(q.denominator,-1,p)*prod(pow(a,e,p) for a,e in zip(args,i))
        return z%p

Y,a,d=[P({tuple(int(i==j) for j in range(N)):1}) for i in range(N)]
base=Y*(Y-1)
rows=[
    (Y-a)*(2*Y-3*a)*(Y-d),
    Y*(Y-a)*(2*Y-3*a)*(Y-d),
    (Y-d)*(7*Y-15*a),
    (5*a-6*d)*Y**2+(15*a*d-9*a**2)*Y-9*a**2*d,
]
left=2*(2*Y-3*a)*(-(3*d-a)*(d-2*a)*Y+a*d*(3*d-7*a))-a*a*rows[2]
assert left==(2*d-3*a)*rows[3]
M=[[(base*f*Y**j).integrate_y() for j in range(4)] for f in rows]
def det(A):
    n=len(A)
    return sum(
      (-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
      *prod(A[i][p[i]] for i in range(n))
      for p in permutations(range(n))
    )
lead=-8694*a**4+11340*a**3-4536*a**2+630*a-21
lin=17010*a**5-20412*a**4+7560*a**3-966*a*a+25*a
Fap=lead*d*d+lin*d+6*a*a
assert 280052640000*det(M)==-Fap
print('saturated exact moment determinant: -P/280052640000')
p=19
assert all(lead.mod_value((0,j,0),p) for j in range(p))
print('leading coefficient A(a) has no residue root modulo 19')
factors=[(i,1) for i in range(p)]+[(1,0)]
def split_poly(f):
    u=[1]
    for x,s in f:
        v=[0]*(len(u)+1)
        for i,c in enumerate(u):
            v[i]=(v[i]-x*c)%p
            v[i+1]=(v[i+1]+s*c)%p
        u=v
    k=next(i for i in reversed(range(len(u))) if u[i])
    v=pow(u[k],-1,p)
    return tuple(c*v%p for c in u)
split={split_poly(t) for t in combinations_with_replacement(factors,3)}
def cvec(A):
    return [(-1)**j*det([[row[i] for i in range(4) if i!=j] for row in A])
            for j in range(4)]
rootpairs=[]
for aa,dd in product(range(p),repeat=2):
    if Fap.mod_value((0,aa,dd),p): continue
    mat=[[r.mod_value((0,aa,dd),p) for r in row] for row in M]
    assert not det(mat)%p
    for rowids in combinations(range(4),3):
        cc=cvec([mat[i] for i in rowids])
        if cc[3]%p:break
    else:raise AssertionError('no degree-three affine nullvector')
    m=pow(cc[3],-1,p)
    cc=tuple(x*m%p for x in cc)
    assert all(sum(x*y for x,y in zip(r,cc))%p==0 for r in mat)
    assert cc not in split
    rootpairs.append((aa,dd))
    print('affine',aa,dd,'rows',*rowids,'monic nonsplit',*cc)
assert len(rootpairs)==14
print('affine residue branches:',len(rootpairs))
cc=cvec(M[:3])
one=([5,-35,70,-42],4939200)
two=([-1,9,-21,14],117600)
for e,(want,scale),erho,wexp in ((3,one,0,-3),(-1,two,3,-6)):
    for v,z in zip(cc,want):
        assert min(-i+e*j for k,i,j in v)==wexp
        assert {(k,j):c for (k,i,j),c in v.items() if -i+e*j==wexp}=={(0,erho):F(z,scale)}
    inv=pow(want[-1],-1,p)
    assert tuple(q*inv%p for q in want) not in split
    print('boundary',e,'valuation exponent',wexp,'unit-power',erho,
          'cofactor',want,'scale',scale)
squares={i*i%p for i in range(p)}
assert 105%19==10 and 33%19==14 and not({10,14}&squares)
print('boundary quadratic discriminants: nonsquares 10 and 14 modulo 19')
