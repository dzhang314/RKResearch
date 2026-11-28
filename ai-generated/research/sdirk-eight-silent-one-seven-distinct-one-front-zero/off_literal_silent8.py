"""Sole terminal balance physically eighth; the actual fourth adds an ordinary peg."""
from off_literal_active8 import *
from silent_guard import split_h4,explicit_fields

@lru_cache(None)
def silent_project(f,slot,ori):
 Phi,T,A,*_=eqs(f,slot,None,ori)
 A0,B0,_,_,_,_,_,anc,off,_,Aq,Bq,Dn,Nn,_,_,guards,sh=tail_profile(f,slot,None,ori)
 def trim_s(K):
  for a in (A0,B0):
   while True:
    N,rr=exdiv(K,s-expr(a))
    if rr:break
    K=N
  return K
 Z=can(T.resultant(A,0))
 Z=trim_s(Z);Phi0=trim_s(Phi)
 print('before silent pseudo-remainder',f,slot,ori, Z.degrees(),flush=True)
 from arithmetic_nonzero import pseudo
 p0=vec_s(Phi0);v0=vec_s(Z)
 lead=p0[-1]
 # Work over the exact quadratic field, folding t^2 in each polynomial operation.
 J=pseudo(v0,p0)
 print('after silent pseudo-remainder',f,slot,ori,[len(w)-1 for w in J],flush=True)
 # Divide only common leading factors, and retain their gamma roots separately.
 while True:
  C=lead
  for V in J:
   if V:C=gcdp(C,V)
  if len(C)<=1:break
  J=[divp(V,C)[0] if V else [] for V in J]
 J0=can(sum(term(v,g)*s**i for i,v in enumerate(J) if v))
 assert J0
 R=can(Phi0.resultant(J0,1))
 G=mul(lead,exact_g(R))
 P=mon(guarded(G,[*guards,sh]))
 S=mon(guarded(sh,[*guards,Bq]))
 print('silent-only zero factor projections',f,slot,ori,len(P)-1,'hole',len(S)-1,flush=True)
 return P,S,Phi0

def finish_silent(F,gg,s0,Y,r,kind,Et,Ea,T0,A0):
 T=eval_y(Et,F,gg,s0);A=eval_y(Ea,F,gg,s0)
 V=Nested(Y);y0=V.gen()
 span_unit(V,ev(list(map(V,T)),y0),ev(list(map(V,A)),y0))
 if kind=='hole':
  z=r/gg
  span_unit(F,ev(eval_y(T0,F,gg,s0),z),ev(eval_y(A0,F,gg,s0),z))

def geom_fields(G,kind,Phi,p,t):
 ex=vec_s(Phi)
 deg=len(ex)-1
 H=gcdp(G,ex[-1])
 L=mon(guarded(G,[ex[-1]]))
 print('guarded silent early leading split',kind,deg,len(H)-1,len(L)-1,flush=True)
 # The only special leading branch we normalize here is precisely one lower.
 if len(H)>1:assert len(gcdp(H,ex[-2]))==1
 B=Bfield(nmod_poly([0,1],p),p,t)
 for J,k in ((L,deg),(H,deg-1)):
  if len(J)<=1:continue
  Md=nmod_poly([int(B(x).x[0]) for x in J],p);assert Md.degree()==len(J)-1
  for M,_ in Md.factor()[1]:
   F=Bfield(M,p,t);gg=F(nmod_poly([0,1],p))
   T=eval_s(Phi,F,gg,F(0))
   assert len(T)==k+1,(kind,len(T)-1,k)
   if len(T)==1:
    T[0].inv();continue
   U=Tower(mon(T));s0=U.gen()
   yield U,U(gg),s0

def verify_silent(f,slot,ori,p,t):
 P,H,Phi0=silent_project(f,slot,ori)
 A,B,_,C,D,_,_,anc,off,hh,Aq,Bq,_,_,_,_,_,sh=tail_profile(f,slot,None,ori)
 Phi,_,_,Et,Ea,T0,A0,*_=eqs(f,slot,None,ori)
 K=gcdp(P,Bq);M=mon(guarded(P,[Bq]))
 for G,kind in ((H,'hole'),(K,'constant'),(M,'coprime')):
  G0,ex=split_h4(tuple(G),Phi0,f)
  from itertools import chain
  pts=chain(geom_fields(G0,kind,Phi0,p,t),*(explicit_fields(J,Y,p,t) for J,Y in ex))
  for F,gg,s0 in pts:
   a,b=(ev(list(map(F,v)),gg) for v in (Aq,Bq))
   an,c0=map(F,(anc,C))
   X,c=(1-gg)/gg,1/gg-c0
   nodes=[gg*v for v in (an,X,c,s0)]
   Y,r=other_nodes(F,gg,a,b,nodes,kind)
   assert Y is not None
   finish_silent(F,gg,s0,Y,r,kind,Et,Ea,T0,A0)
 return True
