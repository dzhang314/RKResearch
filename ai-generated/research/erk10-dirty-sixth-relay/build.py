#!/usr/bin/env python3
"""A true early size-six ghost and a later full grade-five decoder."""
import sys,json
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
from math import prod,lcm
S=Path(__file__).resolve().parent.parent/'erk10-six-opening-singleton'
sys.path.insert(0,str(S))
from port import table,cardinal,trees,size,fact,dot
Z,O=Q(0),Q(1)
def phi_builder(A):
 @lru_cache(None)
 def phi(t):
    return tuple(prod(v[i]for v in map(prim,t))for i in range(len(A)))
 @lru_cache(None)
 def prim(t):
    return tuple(dot(r,phi(t))for r in A)
 return phi

def init(p,q,start,z,w,sl=1):
 A=[a.copy()for a in table(p,q,start)]
 # The four old evaluation sites are actually pure through derivative size four.
 nodes=(Z,p,q,O)
 weights=[sum(v*z**(j+1)/(j+1)for j,v in enumerate(cardinal(nodes,k)))for k in range(4)]
 A.append([weights[0],Z,Z,weights[1],weights[2],sl*weights[3],(1-sl)*weights[3],Z])
 phi=phi_builder(A)
 def solve(cols,b,n):
    V={}
    for rr,x in zip(cols,b):
       r=list(map(Q,rr))+[Q(x)]
       for k in range(n):
          if not r[k]:continue
          if k in V:
              a=r[k];r=[x-a*y for x,y in zip(r,V[k])]
          else:
              v=r[k];V[k]=[x/v for x in r];break
       else:
          if r[-1]:return
    x=[Z]*n
    for k in sorted(V,reverse=True):x[k]=V[k][-1]-dot(V[k][k+1:n],x[k+1:n])
    return x,len(V)
 T=[t for k in range(1,6)for t in trees(k)]
 v=solve(map(phi,T),(w**size(t)/fact(t)for t in T),8)
 assert v is not None and v[1]==8
 row=v[0]
 A.append(row+[Z])
 A=[a+[Z]*(len(A)-len(a))for a in A]
 # Full degree-four actual decoder, each row gives one coefficient in X.
 phi=phi_builder(A)
 Pic=[]
 for j in range(5):
    a=solve(map(phi,T),[Q(size(t),fact(t))if size(t)==j+1 else Z for t in T],9)
    assert a is not None and a[1]==9
    Pic.append(a[0])
 return A,Pic

def main():
 z=Q(1,3);w=Q(2,3);p=Q(3,10);q=Q(3,4);e=Q(1,10)
 A,Pi=init(p,q,e,z,w)
 phi=phi_builder(A)
 def local(i,k):
    c=sum(A[i]);L=[]
    for j in range(1,k+1):
       for t in trees(j):
          L.append(phi(t)[i]-Q(j,fact(t))*c**(j-1))
    return L
 assert not any(local(6,6));assert not any(local(7,5));assert not any(local(8,6))
 f=next((d for d in local(7,6)if d),None)
 assert f
 print('early pure checks',37,17,37,'first sixth-degree ghost defect',f)
 print('stage 8',list(map(str,A[7])),'stage 9',list(map(str,A[8])),'D',lcm(*(x.denominator for r in A for x in r)))
 out={'A':[list(map(str,a[:i]))for i,a in enumerate(A)],'decoder':[list(map(str,a))for a in Pi],
      'matrix_denominator':lcm(*(x.denominator for r in A for x in r)),
      'decoder_denominator':lcm(*(x.denominator for r in Pi for x in r)),
      'local':[[7,6],[8,5],[9,6]],'ghost_failure':{'child':[[],[],[],[]],'primitive_defect':'11/4860'}}
 if len(sys.argv)>1:
    Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n')
 else:
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
