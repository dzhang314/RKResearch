"""Finite chronology after literal fourth/fifth diagonal projection."""
from front_only_projection import *
from exact_hole8_h4 import GaussExact,SplitAt,a0
from gauss_tail_nonliteral import p0 as p0t,aX,bX,dX,K,H,J,uX,gX,remR,all_div,divX,by_g_u
from functools import lru_cache

def split_deg(G,W):
 for n in range(len(W)-1,-1,-1):
  if not W[n]:continue
  C=gcdp(G,W[n]);D=mon(guarded(G,[W[n]]))
  if len(D)>1:yield D,n
  G=C
  if len(G)<=1:return
 assert len(G)<=1,'identically zero projection'

@lru_cache(None)
def tails(mode):
 px,pc=map(p0t,(aX,bX))
 if mode=='arith':
  F=all_div(remR(H*p0t(dX(False))+2*J*pc-K*J*px),uX)
 else:
  assert mode=='silent'
  F=divX(remR((uX-2)*pc-(2*uX+K*(uX-2))*px),uX)
 U=by_g_u(F)
 assert len(U)-1==3
 print('tail eliminated root degree',mode,len(U)-1,flush=True)
 return U

def exact_allowed(G,PH,H4):
 X=GaussExact(G);g=X.gen()
 try:
  P=trim([ev(list(map(X,w)),g) for w in PH]);assert P
  h=list(map(lambda h:X(a0(h)),H4))
  d=len(P)-1
  while True:
   V=gcdp(P,h)
   if len(V)<=1:break
   P,e=qr(P,V);assert not e
  assert P
  a=[list(v.x) for v in mon(P)]
  return [(G,a,d)]
 except SplitAt as e:
  A=mon(e.d);B,rem=qr(G,A);assert not rem
  return exact_allowed(A,PH,H4)+exact_allowed(B,PH,H4)

@lru_cache(None)
def g_and_s(f,i,typ):
 N,Ho,Phi,FT,FA,T0,A0=project(f,i)
 G=Ho if typ=='hole' else N
 fd=frontdata(f,i);hh=fd[8]
 a=E0(fd[5]);gamma_px=bg(C(p0(1-g)));ga=bg(C(1-g-g*a))
 G=mon(guarded(G,[gamma_px,ga]))
 bad=bg(C(term0(hh,s).resultant(p0(g*s),1)))
 I=gcdp(G,bad);J=mon(guarded(G,[bad]));PH=bsg(Phi)
 a=exact_allowed(squarefree(I),PH,hh) if len(I)>1 else []
 simple=[(D,PH[:j+1],j) for D,j in split_deg(J,PH)] if len(J)>1 else []
 print('exact fourth splits',f,i,typ,len(G)-1,len(I)-1,len(J)-1,[(len(D)-1,len(PH)-1,j) for D,PH,j in a+simple],flush=True)
 return a+simple

def whole_field_s(f,i,typ,mode,p,t):
 tail=tails(mode)
 for G,SH,j in g_and_s(f,i,typ):
  if len(SH)==1:
   # an exact monic constant (H4-filtered branch) excludes this g component
   assert SH==[[B0(1)]]
   continue
  for D,k in split_deg(G,tail):
   for F,g,r,lift in cut_gamma(D,p,t):
    sy=trim([ev(list(map(lift,v)),g) for v in SH])
    assert len(sy)==len(SH),(f,i,typ,mode,'fourth',D,len(sy),len(SH))
    ut=trim([ev(list(map(lift,v)),g) for v in tail])
    assert len(ut)==k+1,(f,i,typ,mode,'gap',D,len(ut),k)
    if len(ut)==1:continue
    U=Tower(mon(ut));u=U.gen()
    W=Nested(mon(list(map(U,sy))));s0=W.gen()
    yield W,W(g),W(u),W(r),s0

def unit_b(F,p):
 if isinstance(p,U):return conditional_zero(F,p)
 assert isinstance(p,V)
 if not p:return False
 n=len(p.A.F)-1;B=p.A.B
 if n==1:return unit_b(B,p.x[0])
 cols=[]
 for i in range(n):
  l=(p*p.A([B(0)]*i+[B(1)])).x
  cols.append(l+[B(0)]*(n-len(l)))
 return unit_b(B,det(list(zip(*cols))))

def test_unit(F,*a):
 if any(unit_b(F,v) for v in a):return True
 for k in range(1,22):
  r=sum(F(k)**j*v for j,v in enumerate(a))
  if unit_b(F,r):return True
 return False

def hom(F,E,num,den,n):return sum(v*num**j*den**(n-j) for j,v in enumerate(E))

def diag(f,i,typ,mode,p,t):
 fd=frontdata(f,i);n=0
 assert len(gcdp(fd[8],exact_uc_y(fd[19])))==1
 for F,g,u,r,s in whole_field_s(f,i,typ,mode,p,t):
  n+=1
  a,b,ha=map(F,fd[5:8]);H4=list(map(F,fd[8]))
  pp=Pcoeff(F,r)
  Jp=[g**i*v for i,v in enumerate(pp)]
  Q,P=ev(Jp,a),sc(Jp,ha)
  h,T0,A0,T1,A1=fterms(F,fd,a,s,H4)
  X=1-g;C1=X-g*u;D=X-2*g*u
  Xp,Cp=ev(pp,X),ev(pp,C1)
  K=1+2*u-u*u
  Zden=Cp-K*Xp;Znum=X*Cp-K*C1*Xp
  J4=g*Zden*s-Znum
  if typ=='hole':
   Y=r/g;E1,E2=ev(T0,Y),ev(A0,Y)
  else:
   A=add(sc(T0,h*Q),mul(T1,P))
   B=add(sc(A0,h*Q),mul(A1,P))
   A,err=qr(A,list(map(F,nodal([a,s]))));assert not err
   B,err=qr(B,list(map(F,nodal([a,s]))));assert not err
   E1,E2=polyres(F,A,B,2,2),F(0)
  if mode=='arith':
   # Rows six/seven silent => five known ordinary pegs; 1 missing node.
   P5=nodal([g*a,X,C1,D,g*s]);nu=intp(F,pp)/ev(pp,r);p5r=ev(P5,r)
   m0,m1,m2=[intp(F,P5,j)-nu*p5r*r**j for j in range(3)]
   DD=m0*m2-m1*m1
   assert test_unit(F,DD,E1,E2),(n,'j67')
   if typ=='hole':
    assert test_unit(F,J4,E1,E2),(n,'j4 hole')
   else:
    M=hole_moment(F,g,r,[g*a,X,C1,D])
    R1,R2=polyres(F,M,A,2,2),polyres(F,M,B,2,2)
    assert test_unit(F,J4,E1,R1,R2),(n,'j4 ord')
    assert test_unit(F,hom(F,A,Znum,g*Zden,2),hom(F,B,Znum,g*Zden,2)),(n,'j5')
  else:
   if typ=='hole':
    assert test_unit(F,E1,E2),(n,'silent8 hole')
   else:
    M=hole_moment(F,g,r,[g*a,X,C1,g*s])
    R1,R2=polyres(F,M,A,2,2),polyres(F,M,B,2,2)
    assert test_unit(F,E1,R1,R2),(n,'silent8 ordinary')
 assert n
 print('verified finite literal front and tail:',f,i,typ,mode,p,n,flush=True)
 return True
