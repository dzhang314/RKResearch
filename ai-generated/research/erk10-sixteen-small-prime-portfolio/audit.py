#!/usr/bin/env python3
"""Verify the actual strict tableaux over the indicated small coefficient rings."""
from pathlib import Path
from functools import cache
from math import prod
import json
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'erk10-sixteen-f17'))
from rooted import trees,tf

def replay(A,b,m,p):
 assert len(A)==len(b)==16 and all(len(r)==i for i,r in enumerate(A))
 assert len({tuple(r+[0]*(16-len(r)))for r in A})==16
 assert all(0<=x<m for r in A for x in r)and all(0<=x<m for x in b)
 @cache
 def phi(t):
  vals=[act(u)for u in t]
  return [prod(r[i]for r in vals)%m for i in range(16)]
 @cache
 def act(t):
  val=phi(t)
  return [sum(a*x for a,x in zip(r,val))%m for r in A]
 n=0
 for j in range(1,11):
  for t in trees(j):
   val=tf(t)*sum(a*b for a,b in zip(b,phi(t)))%m
   assert val==1,(m,j,t,val)
   n+=1
 assert n==1205
 f=((),)*10
 defect=(11*sum(w*x for w,x in zip(b,phi(f)))-1)%m
 assert defect%p
 return n,defect

def read(p):
 row=json.loads((HERE/('f'+str(p)+'.json')).read_text())
 assert row['field']==p
 return row,[list(map(int,r))for r in row['A']],list(map(int,row['b']))
if __name__=='__main__':
 for p,k in [(11,10),(13,5),(19,11),(23,15)]:
  j,A,b=read(p)
  n,g=replay(A,b,p,p)
  assert g==k==int(j['next_failure_value']) and j['next_failure_tree']==[[]]*10
  print('F'+str(p)+': strict distinct width 16;',n,'ordinary rooted conditions, bush defect',g)
