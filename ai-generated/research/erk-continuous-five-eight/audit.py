#!/usr/bin/env python3
"""Independent exact check of the continuous-order-five decoder and FSAL."""
from functools import cache
from fractions import Fraction as F
from math import prod,lcm
from hashlib import sha256
from pathlib import Path
from argparse import ArgumentParser
import json
import re

@cache
def trees(n):
    if n==1:return ((),)
    smaller=[(k,t)for k in range(1,n)for t in trees(k)]
    def walks(k,j):
      if k==0:yield ()
      for i in range(j,len(smaller)):
        s,t=smaller[i]
        if s>k:break
        for c in walks(k-s,i):yield (t,*c)
    return tuple(walks(n-1,0))
@cache
def size(t):return 1+sum(map(size,t))
@cache
def tf(t):return size(t)*prod(map(tf,t))
def rank(A):
  P={}
  for row in A:
    v=list(row)
    for k in range(len(v)):
      z=v[k]
      if not z:continue
      if k not in P:
        P[k]=[x/z for x in v];break
      v=[x-z*y for x,y in zip(v,P[k])]
  return len(P)
def dot(x,y):return sum(a*b for a,b in zip(x,y))

def main(p):
 data=json.loads(Path(__file__).with_name('prefix.json').read_text())
 A,Pi=([[F(x)for x in r]for r in data[name]]for name in ('A','Pi'))
 assert len(A)==8 and all(len(r)==i for i,r in enumerate(A))
 assert len(Pi)==5 and all(len(r)==8 for r in Pi)
 if p:
  s=p.read_bytes();assert sha256(s).hexdigest()==data['source_sha256']
  s=s.decode().split('function OwrenZen5ConstantCache(::Type{T}, ::Type{T2}) where {T, T2}',1)[1]
  s=s.split('    return OwrenZen5ConstantCache',1)[0]
  d={(int(i)-1,int(j)-1):F(int(v),int(q or 1))
     for i,j,v,q in re.findall(r'a([0-9])([0-9]) = convert\(T, (-?[0-9]+)(?: // ([0-9]+))?\)',s)}
  assert A==[[d.get((i,j),F(0))for j in range(i)]for i in range(8)]
  print('Pinned primary implementation: exact literal A match.')
 @cache
 def phi(t):
  receivers=[act(u)for u in t]
  return tuple(prod(v[i]for v in receivers)for i in range(8))
 @cache
 def act(t):return tuple(dot(row,phi(t))for row in A)
 stages=[t for n in range(1,6)for t in trees(n)]
 assert len(stages)==17
 assert rank([phi(t)for t in stages])==8
 for t in stages:
  n=size(t)
  assert [dot(row,phi(t))for row in Pi]==[F(n,tf(t))*(n-1==j)for j in range(5)]
 assert [sum(Pi[j][i]/(j+1)for j in range(5))for i in range(8)]==A[-1]+[F(0)]
 for n in range(1,7):
  for t in trees(n):assert phi(t)[7]==F(n,tf(t))
 for n in (6,7):
  Q=[]
  for t in trees(n):
   r=[-dot(row,phi(t))for row in Pi]+[F(0)]*(n-5)
   r[n-1]+=F(n,tf(t))
   assert r[0]==0
   if n==6:assert sum(r)==0
   Q.append(r)
  assert rank(Q)==n-2
  print('Actual size',n,'residual rank:',n-2)
 print('All 17 continuous order-five profile identities; literal FSAL alias; last profile exact through six.')
 print('Clock vector:',[str(sum(r))for r in A])
 print('Matrix denominator:',lcm(*(x.denominator for r in A for x in r)))
 print('Decoder denominator:',lcm(*(x.denominator for r in Pi for x in r)))

if __name__=='__main__':
 p=ArgumentParser()
 p.add_argument('--pinned-source',type=Path)
 main(p.parse_args().pinned_source)
