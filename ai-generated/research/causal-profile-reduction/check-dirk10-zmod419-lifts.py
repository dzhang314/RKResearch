#!/usr/bin/env python3
"""Lift the entire rooted order system from F419 to Z/(419**11), exactly.

NumPy is used only for small bounded integer Jacobian entries modulo 419.
The lifted tableau and its complete rooted-order rechecks use Python ints.
The 4 prescribed zero diagonals and physical b2=0 are preserved.
Exact modular lifts through a finite number of powers do not imply a
characteristic-zero or an infinite p-adic lift.
"""
import importlib.util
from functools import cache
import numpy as np
from pathlib import Path
x=Path(__file__).resolve().with_name('check-dirk10-zmod419.py')
spec=importlib.util.spec_from_file_location('probe',x); d=importlib.util.module_from_spec(spec); spec.loader.exec_module(d)
p=d.P;n=len(d.B)
trees=tuple(sorted({d.canonical(t) for j in range(1,11)for t in d.ordered(j)},key=lambda t:(d.vertex_count(t),t)))
A0=np.array([r+(0,)*(n-len(r))for r in d.A],dtype=np.int64)
b0=np.array(d.B,dtype=np.int64)
aVars=[(i,j)for i in range(n)for j in range(i+1)if not (i==j and i in (0,4,6,10))]
bVars=[i for i in range(n)if i!=1]
m=len(aVars)+len(bVars)
D=np.zeros((n,n,m),dtype=np.int64)
for k,(i,j)in enumerate(aVars):D[i,j,k]=1
db=np.zeros((n,m),dtype=np.int64)
for k,i in enumerate(bVars,len(aVars)):db[i,k]=1
@cache
def jacstage(t):
 v=np.ones(n,dtype=np.int64); dv=np.zeros((n,m),dtype=np.int64)
 for x in t:
    u,du=jacstage(x)
    w=A0@u%p
    dw=(A0@du+np.einsum('ijk,j->ik',D,u))%p
    v,dv=v*w%p,(v[:,None]*dw+dv*w[:,None])%p
 return v,dv
J=np.array([d.factorial(t)*(b0@dv+v@db)%p for t in trees for v,dv in [jacstage(t)]],dtype=np.int64)
row=J.copy(); idx=np.arange(len(row)); pv=[]; es=[]
for c in range(m):
 j0=len(pv); pos=np.flatnonzero(row[j0:,c])
 if len(pos)==0: continue
 j=int(pos[0])+j0; row[[j,j0]]=row[[j0,j]]; idx[[j,j0]]=idx[[j0,j]]
 sc=pow(int(row[j0,c]),-1,p); row[j0]=row[j0]*sc%p
 k=row[j0+1:,c].copy(); row[j0+1:]=(row[j0+1:]-k[:,None]*row[j0])%p
 es.append((j,sc,k));pv.append(c)
print('actual 1205-by-72 Jacobian rank',len(pv),'variable count',m,'free',[('b',bVars[i-len(aVars)]+1)if i>=len(aVars)else('a',aVars[i])for i in range(m)if i not in pv],flush=True)
def solve(rhs):
 rhs=np.array(rhs,dtype=np.int64)
 for j0,(j,sc,k) in enumerate(es):
    rhs[[j,j0]]=rhs[[j0,j]];rhs[j0]=rhs[j0]*sc%p
    rhs[j0+1:]=(rhs[j0+1:]-k*rhs[j0])%p
 assert all(r==0 for r in rhs[len(pv):]), ('obstruction',np.count_nonzero(rhs[len(pv):]))
 dx=np.zeros(m,dtype=np.int64)
 for i,c in reversed(list(enumerate(pv))):
    dx[c]=(rhs[i]-row[i]@dx)%p
 return dx
def errs(A,b,P):
 @cache
 def elementary(t):
    v=[1]*n
    for q in t:
        u=elementary(q)
        v=[v[i]*sum(A[i][j]*u[j] for j in range(i+1))%P for i in range(n)]
    return v
 return [(d.factorial(t)*sum(x*y for x,y in zip(b,elementary(t)))-1)%P for t in trees]
A=[[int(x)for x in r]for r in A0]; b=[int(x)for x in b0]
M=p
for k in range(1,11):
 residue=errs(A,b,M*p)
 assert all(e%M==0 for e in residue)
 dx=solve([-e//M for e in residue])
 for (i,j),v in zip(aVars,dx): A[i][j]+=M*int(v)
 for i,v in zip(bVars,dx[len(aVars):]):b[i]+=M*int(v)
 M*=p
 assert not any(errs(A,b,M))
 c=[sum(r)%M for r in A]
 assert (11*sum(w*x**10 for w,x in zip(b,c))-1)%p !=0
 print('all rooted equations lift exactly to modulus',p,'^',k+1,flush=True)
print('verified exact finite lifts, not a claim of a Z_419 or real lift')
