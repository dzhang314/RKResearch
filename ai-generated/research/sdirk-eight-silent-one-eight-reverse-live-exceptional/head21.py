"""Exact universal top-three cancellation in the silent-eighth nodal determinant."""
from flint import fmpq_mpoly_ctx
from itertools import permutations
from time import perf_counter

C=fmpq_mpoly_ctx.get(['u','g','a','b','s','p','q','r'])
u,g,a,b,s,p,q,r=C.gens()
O=C.constant(1);Z=C.constant(0)
x=1-g;c=x-g*u;k=1+2*u-u*u
L3=[-1,12,-30,20,0,0]
L4=[1,-20,90,-140,70,0]
L5=[-1,30,-210,560,-630,252]
def ev(P,z):return sum(v*z**i for i,v in enumerate(P))
def gap(P):
 U,R=divmod((u-2)*ev(P,c)-(2*u+k*(u-2))*ev(P,x),u);assert not R
 return U
F=list(map(gap,(L3,L4,L5)))
H=[p*(F[1]*a0-F[0]*b0)+q*(F[2]*a0-F[0]*c0)+r*(F[2]*b0-F[1]*c0)
   for a0,b0,c0 in zip(L3,L4,L5)]
def nodal(V):
 P=[O]
 for x0 in V:
     S=[Z]*(len(P)+1)
     for i,v in enumerate(P):S[i]-=x0*v;S[i+1]+=v
     P=S
 return P
E=nodal([a,b,s,x,c])
def W(F):return [sum((F[j]/(j-i) for j in range(i+1,len(F))),Z) for i in range(len(F)-1)]
def cf(F,G,n):return sum((F[i]*G[n-i] for i in range(len(F)) if 0<=n-i<len(G)),Z)
WH=W(H)
def head(P,n,depth):
 by=[{} for _ in range(depth)]
 for M,v in P.to_dict().items():
   i,*tail=M
   assert i<=n
   if n-i<depth:by[n-i][(0,*tail)]=v
 return [C.from_dict(w) for w in by]
A=[]
start=perf_counter()
for j in range(4):
 L=[Z]*j+E;WL=W(L)
 A.append([head(cf(H,WL,k)-cf(L,WH,k),6,4) for k in range(1,5)])
print('exact universal heads built',round(perf_counter()-start,2),flush=True)
def conv(F,G,n):
 return [sum((F[i]*G[j-i] for i in range(j+1)),Z) for j in range(n)]
def hd(n):
 S=[Z]*n
 for prm in permutations(range(4)):
   sign=(-1)**sum(prm[i]>prm[j] for i in range(4) for j in range(i+1,4))
   W=[O]+[Z]*(n-1)
   for j in range(4): W=conv(W,A[j][prm[j]],n)
   for i,v in enumerate(W):S[i]+=sign*v
 return S
def check_head():
    P=hd(4)
    assert all(not P[j] for j in range(3)) and P[3]
    print('generic exact degree <=21, nonzero head at 21',len(P[3].to_dict()),flush=True)
