#!/usr/bin/env python3
import sys,json
from math import lcm,prod
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
@lru_cache(None)
def forest(n,lo=(0,())):
 if not n:return ((),)
 return tuple((v,)+r for k in range(max(lo[0],1),n+1)for v in forest(k-1)if (k,v)>=lo for r in forest(n-k,(k,v)))
@lru_cache(None)
def size(t):return 1+sum(map(size,t))
@lru_cache(None)
def tf(t):return size(t)*prod(map(tf,t))
def mul(x,y):return (x[0]*y[0]+15*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def P(x):return '('+str(x[0])+','+str(x[1])+')'
def array(l):return '#['+','.join(l)+']'
def vec(cols):return '#[\n'+',\n'.join('  '+array(x)for x in cols)+'\n]'
def data(src,dst):
 j=json.load(open(src))
 D=lcm(*(F(x).denominator for row in j['A']for z in row for x in z),*(F(x).denominator for z in j['b']for x in z))
 pair=lambda z: tuple(int(F(x)*D)for x in z)
 B=[list(map(pair,row))for row in j['A']]
 order=[()] + [t for n in range(2,10)for t in forest(n-1)]
 ids={t:i for i,t in enumerate(order)}
 cut=[sum(size(t)<=n for t in order)for n in range(10)]
 rawkids=[sorted(ids[v]for v in t)for t in order]
 sortedK={tuple(z):i for i,z in enumerate(rawkids)}
 join=[]
 for i,t in enumerate(order):
  join.append([sortedK[tuple(sorted(rawkids[i]+[k]))]for k in range(cut[9-size(t)])])
 act=[]
 for i,t in enumerate(order[:cut[8]]):
  feat=[]
  for z in range(14):
   r=(1,0)
   for k in rawkids[i]:r=mul(r,act[k][z])
   feat.append(r)
  y=[]
  for row in B:
   r=(0,0)
   for x,a in zip(row,feat):r=add(r,mul(x,a))
   y.append(r)
  act.append(y)
 s='''module

public import RKCert.ReviewedNative.CanonicalStageMemo
public import RKCert.ReviewedNative.ERKQuadraticIntegerReplay

@[expose] public section

namespace RKResearch.Certified.ERK149QuadraticMemoData
open CanonicalStageMemo ERKQuadraticIntegerReplay
set_option maxHeartbeats 0
set_option maxRecDepth 30000

abbrev Count := 486

def tag (i : ℕ) : Fin Count := ⟨i % Count, Nat.mod_lt _ (by decide)⟩

'''
 s+='def den : Int := '+str(D)+'\n\n'
 s+='def aNumRows : Array (Array Pair) := '+vec(map(P,r)for r in B)+'\n\n'
 s+='def bNumRow : Array Pair := '+array(map(P,map(pair,j['b'])))+'\n\n'
 s+='def keyData : Array (ℕ × ℕ × List ℕ) := #[\n'+',\n'.join(f'  ({size(t)}, {tf(t)//size(t)}, {rawkids[i]})'for i,t in enumerate(order))+'\n]\n\n'
 s+='def actData : Array (Array Pair) := '+vec(map(P,r)for r in act)+'\n\n'
 s+='def joinData : Array (Array ℕ) := '+vec(map(str,r)for r in join)+'\n\n'
 s+='def cutoff (n : ℕ) : ℕ := ('+array(map(str,cut))+' : Array ℕ)[n]!\n\n'
 s+='''def aNum (i j : Fin 14) : Pair :=
  if j < i then (aNumRows[i.val]!)[j.val]! else pack 0

def bNum (i : Fin 14) : Pair := bNumRow[i.val]!

def key (i : Fin Count) : Key Count :=
  let (n,f,c) := keyData[i.val]!
  ⟨n,f,c.map tag⟩

def numAct (i : Fin Count) (j : Fin 14) : Pair := (actData[i.val]!)[j.val]!
def join (i j : Fin Count) : Fin Count := tag ((joinData[i.val]!)[j.val]!)

end RKResearch.Certified.ERK149QuadraticMemoData
'''
 Path(dst).write_text(s)
if __name__=='__main__':data(sys.argv[1],sys.argv[2])
