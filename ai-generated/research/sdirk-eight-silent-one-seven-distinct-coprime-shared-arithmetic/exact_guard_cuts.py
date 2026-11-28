"""Retain other u roots at each diagonal while exactly deleting forbidden Gauss tails."""
from shared_arith_projection import *
from shared_silent8_projection import enorm,norm_irreducible
from front_tail_close import split_deg

@lru_cache(None)
def guard_coeffs():
 x=1-g;c=x-g*u;d=x-2*g*u
 L=lambda z:sum(w*z**j for j,w in enumerate(Lco))
 return tuple(map(Vcoeff,(L(c),L(d))))

def e_sf(F):return eexact(F,egcd(F,E(F.a.derivative(),F.b.derivative()))).monic()

def prep(f,i):
 G,Phi,D,R,P0,q0p,q1p=build_arith(f,i)
 R0=list(map(ef,Vcoeff(R)))
 L0,L1=guard_coeffs()
 U0,U1=[syl(R0,list(map(ef,T))) for T in (L0,L1)]
 assert U0 and U1
 Z=ef(G)
 vals=[ef(Gcoeff(w)) for w in (g,1-g-g*C(frontdata(f,i)[6]),sum(v*(1-g)**j for j,v in enumerate(Lco)),sum(v*(g*C(frontdata(f,i)[5]))**j for j,v in enumerate(Lco)),1-g-g*C(frontdata(f,i)[5]))]
 UC,UD=map(e_sf,(eguard(U0,vals),eguard(U1,vals)))
 assert UC.degree()==UD.degree()==36
 print("exact Gauss guard distinct degrees",f,i,UC.degree(),UD.degree(),flush=True)
 pieces=[];seen=[]
 for V in (UC,UD):
  for H,_ in enorm(V).factor()[1]:
   T=egcd(V,E(H))
   B=eguard(T,seen)
   if B.degree()<=0:continue
   seen.append(B)
   if norm_irreducible(B):
    J=B if etry(Z,B) is not None else E(1)
   else:J=e_sf(egcd(Z,B))
   print("exact guard piece",T.degree(),B.degree(),J.degree(),flush=True)
   if J.degree()>0:pieces.append(J)
 S=eguard(Z,pieces)
 assert [w.degree() for w in pieces]==([4,32,20,12] if f else [4,32,20])
 assert S.degree()==(301 if f else 313)
 print('exact Gauss-tail guards',f,i,'raw',U0.degree(),U1.degree(),
       'cut',sum(w.degree() for w in pieces),S.degree(),
       'pieces',[w.degree() for w in pieces],flush=True)
 return unef(S),list(map(unef,pieces)),Vcoeff(R),L0,L1
