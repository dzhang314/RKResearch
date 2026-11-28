"""Monic residue descent and actual fifth tests."""
from nonliteral_fourth_projection import *
from nonliteral_fourth_tight import tight_profiles as profiles,tightened as tail_pair
from nofront_residue import ff_factors
from leading_branch import nodal_y5,unit_b,test_unit,polyres
from shared_silent8_projection import red_e
from flint import nmod_poly

CACHE={}
def records(W):
 if id(W) in CACHE:return CACHE[id(W)][1]
 V={}
 for (j,k,m,l,h),c in W.to_dict().items():
  U=V.setdefault((j,k,m,l),[Q(0),Q(0)])
  U[h]+=c
 r=[(e,F2(E(*q))) for e,q in V.items()]
 CACHE[id(W)]=(W,r)
 return r

def cv_poly(W,F,evs,idx=0):
 V=records(W)
 d=max((e[idx] for e,v in V),default=-1)
 R=[F(0)]*(d+1)
 for es,c in V:
  y,s,u,g=es
  a=F(c)
  for j,(b,k) in enumerate(zip(evs,es)):
   if j!=idx and k:
    assert b is not None
    a*=b**k
  R[es[idx]]+=a
 return trim(R)

def at(W,F,g,s,u=None):
 R=cv_poly(W,F,[None,s,u,g],0)
 assert len(R)<=1
 return R[0] if R else F(0)

def finite_checks(f,i,star,H,SS,flags,p,t):
 J,T,A,D,Q0,P0,guards=profiles(f,i)
 K,R,S=tail_pair(f,i,star)
 m0,m1=coeff_var(Q0,0)
 Dg=red_e(H,p,t)
 assert Dg.degree()==H.degree() and int(Dg.leading_coefficient())==1
 warnings=[];nG,nS,nY=0,0,0
 hi=(J.degrees()[1]+1,K.degrees()[1]+1)
 for M,_ in Dg.factor()[1]:
  nG+=1
  F=Bfield(M,p,t);g0=F(nmod_poly([0,1],p))
  J0=cv_poly(J,F,[None,None,None,g0],1);K0=cv_poly(K,F,[None,None,None,g0],1)
  if SS:
   S0=trim([F(red_e(v,p,t)) for v in SS])
   if len(S0)!=len(SS):
    warnings.append(('fourth s exact lead',M.degree(),str(M)));continue
  else:
   if len(J0)!=hi[0] and len(K0)!=hi[1]:
    warnings.append(('both fourth leads',M.degree(),str(M)));continue
   S0=J0 if len(J0)==hi[0] else K0
  C0=gcdp(gcdp(S0,J0),K0)
  if len(C0)<=1:continue
  for scol in ff_factors(F,C0,p):
   nS+=1
   U=Tower(mon(scol));s0=U.gen();gg=U(g0)
   a=U(frontdata(f,i)[5])
   q0,q1=[gg*at(m0,U,gg,s0),at(m1,U,gg,s0)]
   x0,z0=1-gg,gg*s0
   Lu=list(map(U,Lco));fd=frontdata(f,i)
   su=[name for name,value in [('H4',ev(list(map(U,fd[8])),s0)),('s-a',s0-a),('s-b',s0-U(fd[6])),('q1',q1),
          ('qx',q0+q1*x0),('xz',x0-z0),('Lz',ev(Lu,z0)),('LsX',ev(Lu,x0)),('La',ev(Lu,gg*a))] if not value]
   if star:
    R0=[at(P,U,gg,s0) for P in R];S1=[at(P,U,gg,s0) for P in S]
    if not R0[1] and not S1[1]:
     warnings.append(('both centered gap slopes',M.degree(),len(scol)-1,su,str(M)));continue
    V=-R0[0]/R0[1] if R0[1] else -S1[0]/S1[1]
    if ev(R0,V) or ev(S1,V):continue
    W=Nested([-V,U(0),U(1)]);v=W.gen();u=1+v
   else:
    R0=cv_poly(R,U,[None,s0,None,gg],2);S1=cv_poly(S,U,[None,s0,None,gg],2)
    if len(R0)!=R.degrees()[2]+1 and len(S1)!=S.degrees()[2]+1:
     warnings.append(('both actual gap leads',M.degree(),len(scol)-1,su,str(M)));continue
    GG=gcdp(R0,S1)
    if len(GG)<=1:continue
    W=Nested(mon(GG));u=W.gen()
   gg,s0,a,q0,q1=map(W,(gg,s0,a,q0,q1))
   x=1-gg;c=x-gg*u;d=x-gg*(2-u if star else 2*u)
   Gt=cv_poly(T,W,[None,s0,None,gg],0)
   Ga=cv_poly(A,W,[None,s0,None,gg],0)
   Nd=nodal_y5(W,gg,[gg*a,x,c,d],q0,q1)
   Z=[polyres(W,Gt,Ga,3,3),polyres(W,Gt,Nd,3,3),polyres(W,Ga,Nd,3,3)]
   nY+=1
   if not test_unit(W,*Z):
    z=gg*s0;L0=list(map(W,Lco));k=1+2*u-u*u
    gates=[('k',k),('u',u),('c-d',c-d),('c-z',c-z),('d-z',d-z),('c-a',c-gg*a),('d-a',d-gg*a),
       ('Lc',ev(L0,c)),('Ld',ev(L0,d)),('qc',q0+q1*c),('qd',q0+q1*d)]
    warnings.append(('fifth',M.degree(),len(scol)-1,su,[q for q,x in gates if not unit_b(W,x)],str(M)))
 print('j4 local result',f,i,star,H.degree(),flags,p,(nG,nS,nY),warnings,flush=True)
 return warnings
