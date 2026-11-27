#!/usr/bin/env python3
"""Symmetric early-clock special fiber; exact two-coordinate polynomial elimination."""
from flint import fmpq_mpoly_ctx,nmod_mpoly_ctx,nmod_poly,fmpq
from math import comb,gcd,lcm,prod
from functools import reduce
from time import monotonic
import sympy as S
import json
C=fmpq_mpoly_ctx.get(['z','r'],'lex')
z,r=C.gens()
C0=lambda x=0:C.constant(x)
time=monotonic()
def info(f):return f.degrees(),f.total_degree(),len(f.to_dict())
def verify_projected_roots(V):
 scale,fs=V.factor()
 assert scale*prod((F**j for F,j in fs),start=C0(1))==V
 degrees=[];roots=[];certs=[]
 for F,n in fs:
  d=int(F.total_degree())
  assert F.degrees()[1]==0
  if d==1:
   q=F(0,0);p=F(1,0)-q
   roots.append(-q/p)
   continue
  degrees.append(d)
  rr=[F.to_dict().get((e,0),fmpq(0)) for e in range(d+1)]
  dl=lcm(*(int(q.denominator) for q in rr))
  co=[int(q.numerator)*(dl//int(q.denominator)) for q in rr]
  g=gcd(*co);co=[q//g for q in co]
  for p in S.primerange(3,2000):
   f=nmod_poly([r%p for r in co],p)
   x=nmod_poly([0,1],p)
   if f.degree()==d and (x.pow_mod(p,f)-x).gcd(f).degree()==0:
    certs.append(p);break
  else: raise AssertionError("missing projective rootless prime")
 assert set(roots)<={fmpq(4)}
 print("projection non-linear degrees",degrees,"rootless primes",certs,"rational roots",roots,flush=True)
 return (sorted(degrees),sorted(map(str,roots)))

def add(a,b):return [(a[i] if i<len(a) else C0())+(b[i] if i<len(b) else C0()) for i in range(max(len(a),len(b)))]
def mul(a,b):
  y=[C0() for _ in range(len(a)+len(b)-1)]
  for i,k in enumerate(a):
    for j,v in enumerate(b):y[i+j]+=k*v
  return y
def scale(a,b):return [k*b for k in a]
def ev(f,c):return sum(k*c**i for i,k in enumerate(f))
def I(f,k=0):return sum(v*z**(k+i)/(k+i+1) for i,v in enumerate(f))

# p = square of displacement from z/2.
pN=13*z**4/1120+(r+4-5*z)*z*z/80
pD=3*z*z/40+(r+4-5*z)/12
hN=r+2-z
hD=4-z
m=z/2
J1=z**4*pD/80-pN*z*z/12
J0=z*z*pD/12-pN
R=[-r,4+r,-5,1]
Kc=(3*m-5)*J1+ev(R,m)*J0
W0=(5-z)*hN-r*hD
W1=(z-1)*hD-hN
mW=W0+m*W1
M=2-r
L3=m**3-9*m*m+18*m-6
P3=L3*(m*hD-hN)*Kc+(4*M+(4-M)*(m-1))*J1*mW
print('P3 raw',info(P3),flush=True)
cp,ss=P3.factor()
assert cp*prod((f**n for f,n in ss),start=C0(1))==P3
print('P3 factors',[(info(x),j,str(x) if x.total_degree()<15 else 'long') for x,j in ss],flush=True)
# Only factors visibly excluded by the fiber hypotheses are removed.
def strip_factors(f,units):
 for y in units:
  while f.gcd(y).total_degree()>0:
   q=f.gcd(y)
   f/=q
 return f
units=(z,pD,z-4,r-3,r-2,(r-4),m*hD-hN,Kc,J1,ev(R,m))
P3=strip_factors(P3,units)
print('active P3',info(P3),str(P3),flush=True)
# Multiply by K on the 6-dimensional residue P quotient; all columns share
# the same pD scaling by using the same pseudo-remainder degree.
PX=mul(mul(R,[-m,1]),[m*m*pD-pN,-2*m*pD,pD])
assert len(PX)==7
K=[I(PX[i+1:],0) for i in range(6)]
# The slice above is exact on X-power j because summand indexed k≥j+1.
assert K[-1]==pD
def prem(f):
 a=add(f,[C0()]*11)
 for k in range(10,5,-1):
  w=a.pop()
  a=scale(a,pD)
  for t in range(6):
   a[t+k-6]-=w*PX[t]
 d=reduce(lambda x,y:x.gcd(y),a)
 return [x/d for x in a]
columns=[prem([C0()]*j+K) for j in range(5)]+[prem(mul([W0,W1],[W0,W1]))]
M=[[columns[j][i] for j in range(6)] for i in range(6)]
print('matrix degrees',[max(y.total_degree() for y in col if not y.is_zero()) for col in columns],flush=True)
def det(M):
 v=M[:]
 p=1; old=C0(1)
 for k in range(len(v)-1):
   if v[k][k].is_zero():
    j=next(i for i in range(k+1,len(v)) if not v[i][k].is_zero())
    v[k],v[j]=v[j],v[k];p=-p
   pivot=v[k][k]
   for i in range(k+1,len(v)):
    for j in range(k+1,len(v)):
     v[i][j]=(pivot*v[i][j]-v[i][k]*v[k][j])/old
   old=pivot
 return v[-1][-1]*p
P4=det(M)
print('P4 raw',info(P4),'sec',monotonic()-time,flush=True)
P4=strip_factors(P4,units)
print('P4 active',info(P4),flush=True)
ct,fac=P4.factor()
assert ct*prod((f**n for f,n in fac),start=C0(1))==P4
print('P4 factors',[(info(f),n,str(f) if f.total_degree()<8 else '') for f,n in fac],flush=True)
if __name__=="__main__":
 records=[verify_projected_roots(P3.resultant(f,"r")) for f,n in fac]
 assert sorted(records)==[([5,21],["4"]),([7],[])]
