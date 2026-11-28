#!/usr/bin/env python3
"""Rational quadratic coefficient chart for the retuned rank-three seed."""
from fractions import Fraction as F
from functools import cache
from math import prod
from pathlib import Path
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-sixteen-f17'))
from rooted import trees as rooted,size,tf
def trees(n):
  return rooted(n+1)

class Alg:
 __slots__=('a','b')
 def __init__(self,a=0,b=0):
  self.a=F(a.a if isinstance(a,Alg)else a)
  self.b=F(a.b if isinstance(a,Alg)else b)
 def __add__(self,o):
  z=Alg(o);return Alg(self.a+z.a,self.b+z.b)
 __radd__=__add__
 def __neg__(self):return Alg(-self.a,-self.b)
 def __sub__(self,o):return self+-Alg(o)
 def __rsub__(self,o):return Alg(o)+-self
 def __mul__(self,o):
  z=Alg(o);a,b,c,d=self.a,self.b,z.a,z.b
  return Alg(a*c-F(20,3)*b*d,a*d+b*c+5*b*d)
 __rmul__=__mul__
 def inv(self):
  a,b=self.a,self.b
  n=a*(a+5*b)+F(20,3)*b*b
  return Alg((a+5*b)/n,-b/n)
 def __truediv__(self,o):return self*Alg(o).inv()
 def __rtruediv__(self,o):return Alg(o)*self.inv()
 def __pow__(self,n):
  if n<0:return self.inv()**(-n)
  if n==0:return Alg(1)
  if n==1:return self
  h=self**(n//2);return h*h*self if n%2 else h*h
 def __bool__(self):return bool(self.a or self.b)
 def __eq__(self,o):
  z=Alg(o);return self.a==z.a and self.b==z.b
 def __repr__(self):return f'({self.a},{self.b})'
 def pair(self):return [str(self.a),str(self.b)]

TH=Alg(0,1)
Z=Alg(0)
O=Alg(1)
def dot(u,v):return sum(a*b for a,b in zip(u,v))
def phi(A):
 @cache
 def p(t):
  W=[a(u)for u in t]
  return tuple(prod(v[i]for v in W)for i in range(len(A)))
 @cache
 def a(t):return tuple(dot(r,p(t))for r in A)
 return p
def eliminate(A,N):
 B={}
 for rr in A:
  r=list(rr)
  for j,z in enumerate(r):
   if j>=N:
    if any(r[j:]):raise ValueError('inconsistent matrix')
    break
   if not r[j]:continue
   z=r[j]
   if j not in B:
    B[j]=[x/z for x in r];break
   r=[x-z*y for x,y in zip(r,B[j])]
 return B
def solve(A,T):
 N=len(A[0])
 B=eliminate(([*a,b]for a,b in zip(A,T)),N)
 assert len(B)==N
 b=[Z]*N
 for j in sorted(B,reverse=True):b[j]=B[j][-1]-dot(B[j][j+1:N],b[j+1:])
 return b

def gen():
  # f=1,v=3,r=4 and seventh-row tap g=0. These rows are
  # literal evaluations of the canonical dense family.
  A=[[],[F(2,3)],[F(1,4),F(3,4)],[F(1),F(-3),F(4)],
    [F(-1),F(6),F(-4),F(1)],
    [F(9,4),F(-27,4),F(6),F(0),F(3,2)]]
  # Row 7 with r=4,v=3,f=1,g=0, and its formal g=1 associate.
  def r7(g):
    r,v,f=map(F,(4,3,1));g=F(g)
    return [(-6*g*r*v*v+18*g*r*v-12*g*r-8*g*v**3+36*g*v*v-52*g*v+24*g+4*r**4-21*r**3+38*r*r-24*r)/(12*(r-2)),
     -3*(-4*g*v**3+12*g*v*v-8*g*v+r**4-4*r**3+4*r*r)/(4*(r-2)),
     (3*g*r*v*v-6*g*r*v-8*g*v**3+18*g*v*v-4*g*v+r**4-3*r**3+2*r*r)/(3*(r-2)),
     -(6*f*g*r*v*v-6*f*g*r*v-4*f*g*v**3+4*f*g*v-f*r**4+3*f*r**3-2*f*r*r-3*g*r*v**3+7*g*r*v*v-4*g*r*v+6*g*v**3-14*g*v*v+8*g*v+r**5-5*r**4+8*r**3-4*r*r)/(12*f*(r-2)),
     (-3*g*v**3+7*g*v*v-4*g*v+r**4-3*r**3+2*r*r)/(12*f),g]
  A=A[:6]+[r7(0)]
  p0=phi(A);p1=phi(A[:6]+[r7(1)])
  grades=[t for h in range(1,6)for t in trees(h-1)]
  assert len(grades)==17
  M=[[*(Alg(v)for v in p0(t)),Alg(p1(t)[6]-p0(t)[6])]for t in grades]
  th=TH
  assert 3*th*th-15*th+20==0
  b=solve(M,[th**size(t)/tf(t)for t in grades])
  assert b[-1]==0
  A=[[Alg(x)for x in r]for r in A]+[b[:-1]]
  assert sum(A[-1])==th
  pm=phi(A)
  P=[solve([pm(t)for t in grades],[Alg(F(size(t),tf(t)))*(size(t)-1==k)for t in grades])
      for k in range(5)]
  assert P[0]==[O]+[Z]*7
  assert [sum(P[k][i]/(k+1)*th**(k+1)for k in range(5))for i in range(8)]==A[-1]+[Z]
  assert all(pm(t)[7]==F(size(t),tf(t))*th**(size(t)-1)for h in range(1,7)for t in trees(h-1))
  RR=[[-dot(row,pm(t))for row in P]+[Alg(F(6,tf(t)))]for t in trees(5)]
  assert all(r[0]==0 and dot(r,[th**k for k in range(6)])==0 for r in RR)
  B=eliminate(RR,6)
  H=list(B.values())
  assert len(H)==3
  for r in RR:
    q=list(r)
    for j in sorted(B):
      assert B[j][j]==1 and not any(B[j][:j])
      q=[a-q[j]*b for a,b in zip(q,B[j])]
    assert not any(q)
  assert all(q.a.denominator%17 and q.b.denominator%17 for r in A+P+H for q in r)
  return A,P,H
def main():
 A,P,H=gen()
 print('exact root relation, all dense order-five conditions, literal FSAL, rank-three H6: confirmed.')
 import argparse
 from math import lcm
 q=argparse.ArgumentParser(description=__doc__)
 q.add_argument('--emit',type=Path)
 args=q.parse_args()
 data=json.dumps({k:[[x.pair()for x in r]for r in v]for k,v in [('A',A),('Pi',P),('H6',H)]},indent=2)+'\n'
 for k,V in [('A',A),('Pi',P),('H6',H)]:
  d=lcm(*(r.denominator for v in V for x in v for r in (x.a,x.b)))
  assert d%17
  print(k,'common denominator',d,'residue',d%17)
 if args.emit:args.emit.write_text(data)
 else:assert data==(HERE/'prefix-algebraic.json').read_text()
if __name__=='__main__':main()
