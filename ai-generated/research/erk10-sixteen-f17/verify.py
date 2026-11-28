#!/usr/bin/env python3
"""Check only the literal 16-stage tableau. No constructor or profile cache."""
from functools import cache
from pathlib import Path
from math import prod
import json
import sys
from rooted import trees,tf,size
HERE=Path(__file__).resolve().parent

def replay(A,b,p):
 n=len(A)
 assert n==len(b)==16 and all(len(a)==i for i,a in enumerate(A))
 assert len({tuple(r+[0]*(n-len(r)))for r in A})==16
 assert all(0<=x<p for a in A for x in a) and all(0<=x<p for x in b)
 c=tuple(sum(row)%p for row in A)
 @cache
 def phi(t):
  W=[act(u)for u in t]
  return tuple(prod(v[i]for v in W)%p for i in range(n))
 @cache
 def act(t):
  z=phi(t)
  return tuple(sum(a*x for a,x in zip(r,z))%p for r in A)
 checks=0
 for h in range(1,11):
  for t in trees(h):
   got=tf(t)*sum(a*x for a,x in zip(b,phi(t)))%p
   assert got==1,(h,t,got)
   checks+=1
 assert checks==1205
 next=((),)*10
 assert size(next)==tf(next)==11
 assert phi(next)==tuple(pow(x,10,p)for x in c)
 defect=(11*sum(w*pow(x,10,p)for w,x in zip(b,c))-1)%p
 assert defect%17==2
 return c,checks,defect

def main():
 data=json.loads((HERE/'tableau.json').read_text())
 p=int(data['field'])
 A=list(map(lambda a:list(map(int,a)),data['A']))
 b=list(map(int,data['b']))
 assert p==17
 c,k,d=replay(A,b,p)
 assert d==int(data['next_failure_value'])==2 and data['next_failure_tree']==[[]]*10
 print('Sixteen strict distinct literal rows; scalar clocks:',list(c))
 print('All',k,'ordinary rooted conditions through order ten modulo',p)
 print('Eleven-vertex bush: factorial-scaled defect',d)
if __name__=='__main__':main()
