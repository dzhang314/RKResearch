#!/usr/bin/env python3
from flint import nmod_poly,fq_default_ctx,fq_default_poly_ctx
from itertools import permutations
from math import lcm,isqrt

def peel(a,g):
 while a.degree()>0:
  h=a.gcd(g)
  if h.degree()<1:break
  a,r=divmod(a,h);assert r.is_zero()
 return a

for p in (37,269,379,397,487,69877):
 assert all(p%d for d in range(2,isqrt(p)+1))
 d=lcm(*(f.degree() for f,e in nmod_poly([1,-20,90,-140,70],p).factor()[1]))
 F=fq_default_ctx(p,d,'a');R=fq_default_poly_ctx(F);U=R.gen();O=F.one();Z=F.zero()
 gs=[x for x,e in (70*U**4-140*U**3+90*U*U-20*U+1).roots()]
 assert len(gs)==4 and all(x!=0 for x in gs)
 val=lambda P,x:sum((c*x**i for i,c in enumerate(P)),R.zero())
 J=lambda P,k,x:sum((c*x**(i+k+1)/(i+k+1) for i,c in enumerate(P)),R.zero())
 def homog(P,n,N,D):return sum((c*N**i*D**(n-i) for i,c in enumerate(P)),R.zero())
 hnd=0; rr=[]; ss=[]
 for x,y in permutations(gs,2):
  v=(y-x)/x
  dd=O/x
  L=[dd**4,-20*dd**3,90*dd**2,-140*dd,70*O]
  L3=lambda w:w**3-3*dd*w*w/2+3*dd**2*w/5-dd**3/20
  if p in (37,269,379):
   z=4*x-y
   if z not in gs or z in (x,y):continue
   bc=[(O-a,O-z) for a in gs if a not in (x,y,z)]
   ghost=None
  else:
   if v**3-4*v*v-v+2!=0:continue
   bc=[(O-a,O-b) for a,b in permutations([c for c in gs if c not in (x,y)],2)]
   ghost=(1-(2*y-x))/x
  for b,c in bc:
   b/=x;c/=x
   for mode in ('S','A'):
    hnd+=1
    h=-2+U+4*U**2-U**3 if mode=='A' else R.one()
    j=3*U-2 if mode=='A' else R.zero()
    k=1+2*U-U*U
    P=[-h+j*(1+U),2*h-j*(2+U),-h/2+j]
    assert 2*val(P,O)==h and 2*val(P,1+U)==h*k
    guard=U*k
    if mode=='S':
     assert 2*val(P,3-U)==h*k
     guard*= (U-1)*(U-2)
    else:
     assert 2*val(P,1+2*U)==h*(1+4*U-4*U*U)+4*U*U*j
     guard*=h*j*(h*(1+4*U-4*U*U)+4*U*U*j)
    if ghost is not None:guard*=val(P,ghost)
    if guard.is_zero():continue
    D=J(P,0,b)-val(P,b)
    N=J(P,1,b)-b*val(P,b)
    S=D.gcd(N)
    if S.is_zero():ss.append((mode,b,c,'fully singular'))
    else:
     S=peel(S,guard)
     if S.degree()>0:ss.append((mode,b,c,S))
    if D.is_zero():continue
    U_A=[-P[0],P[0]-P[1],P[1]/2-P[2],P[2]/3]
    G1=homog(U_A,3,N,D)
    Db=D**2*(b*b*val(P,b)-J(P,2,b))+N*N*D
    Dc=D**2*(c*c*val(P,c)-J(P,2,c))+(N+b*D)*D*(J(P,1,c)-c*val(P,c))-N*b*D*(J(P,0,c)-val(P,c))
    G2=L3(b)*Dc-L3(c)*Db
    bad=guard*D*homog(L,4,N,D)*homog(P,2,N,D)
    if bad.is_zero():continue
    G=G1.gcd(G2)
    assert not G.is_zero()
    G=peel(G,bad)
    if G.degree()>0:rr.append((mode,b,c,G))
 assert hnd==4 and not ss and not rr
 print(p,'complete rear/forward charts',hnd,'singular and regular gcds constant',flush=True)
