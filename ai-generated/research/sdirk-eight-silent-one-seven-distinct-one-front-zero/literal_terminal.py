"""Seven active distinct, k=0, one literal front silent and at x."""
from one_front_zero import *
from seven_k0_anchors import F2,cv
from constant_q_nonzero import moment_const
from arithmetic_nonzero import guarded
from gauss_separate import span_unit
from unequal_finite import moment
from off8_fibers import cramer

def data(F,f,slot,rear,ori):
 A,B,m=map(lambda q:cv(F,q),ends(f,1));a,b,v=map(lambda q:cv(F,q),ends(True if rear is None else rear,ori))
 ha,hb=(A-1)/2,(B-1-m)/2
 anc,sil,hh=(A,B,ha) if slot==0 else (B,A,hb)
 g=1/(1+sil);X=1/g-1;C=1/g-a;D=1/g-b
 u=a-1
 return A,B,m,ha,hb,anc,sil,hh,g,X,C,D,u,b-1-v

def only_literal(f,slot,rear,ori,p,t):
 U=Bfield(nmod_poly([0,1],p),p,t)
 A,B,m,ha,hb,anc,sil,hh,g,X,C,D,u,v=data(U,f,slot,rear,ori)
 L=[U(k)*g**j for j,k in enumerate(Lco)]
 a0,b0=ev(L,A)/ha,ev(L,B)/hb
 q1=(b0-a0)/(B-A);q0=a0-q1*A
 T= u*ev(L,D)*(q0+q1*C)-v*ev(L,C)*(q0+q1*D)
 T.inv()
 return True

def pair_data(F,f,slot,rear,ori):
 A,B,m,ha,hb,anc,sil,hh,g,X,C,D,u,v=data(F,f,slot,rear,ori)
 L=[F(k)*g**j for j,k in enumerate(Lco)]
 if rear is None:
  c0,c1=ev(L,C),-2*u*u*ev(L,X);p0,p1=X,C
 else:
  c0,c1=u*ev(L,D),-v*ev(L,C);p0,p1=C,D
 qa=ev(L,anc)/hh
 den=c0*(p0-anc)+c1*(p1-anc)
 q1=-qa*(c0+c1)/den
 q0=qa-anc*q1
 H4=[cv(F,q) for q in pol(h4(f),lambda x:x)]
 return (A,B,m,ha,hb,anc,g,X,C,D,q0,q1,L,H4)

def missing(F,g,q0,q1,pegs,n):
 if q1:MM=moment(F,pegs,[g*q0,q1],2*n)
 else:MM=moment_const(F,pegs,2*n)
 M=[[MM[i+j] for j in range(n)] for i in range(n)]
 D=det(M)
 if not D:return None # Exact zero pivot excludes actual n distinct missing singleton nodes.
 return [x/(D*g**(n-j)) for j,x in enumerate(cramer(M,[-MM[n+j] for j in range(n)]))]+[F(1)]

@lru_cache(None)
def pair_projection(f,slot,rear,ori):
 F=F2
 A,B,m,ha,hb,anc,g,X,C,D,q0,q1,L,H4=pair_data(F,f,slot,rear,ori)
 E=add(mul([q0,q1],H4),sc(L,-1))
 guards=[A,B,X,C]+([] if rear is None else [D])
 M=mon(guarded(E,[list(map(F,nodal(guards)))]))
 if rear is not None:
  Y=missing(F,g,q0,q1,[g*v for v in (anc,X,C,D)],3)
  if Y is None:return None
  M=gcdp(M,Y)
 print('literal terminal shared projection',f,slot,rear,ori,len(M)-1,bool(q1),flush=True)
 return M

def testrow5(F,f,slot,A,B,m,ha,hb,anc,g,X,C,D,q0,q1,L,H4,s,Y,other_at_five):
 hp=ev(H4,s)
 TA=A**3+A-1-A**4/4 if slot==0 else B**3+B-1-m+m*A**3-B**4/4
 AA=ha if slot==0 else hb+m*ha
 T,Aa=slopes(A,B,m,ha,hb,s,hp,AA,TA,anc)
 T0,A0=row5(F,A,B,s,ha,hb,hp,T,Aa,[F(0)])
 T1,A1=row5(F,A,B,s,ha,hb,hp,T,Aa,[F(1)])
 F1=add(mul(T0,[q0,q1]),mul(add(T1,sc(T0,-1)),L))
 F2=add(mul(A0,[q0,q1]),mul(add(A1,sc(A0,-1)),L))
 if Y:test_poly(Y,F1,F2)
 if other_at_five:test_nonzero(ev(F1,X),ev(F2,X))

def both_literal(f,slot,rear,ori,p,t):
 M=pair_projection(f,slot,rear,ori)
 if M is None or len(M)<=1:return True
 V=Bfield(nmod_poly([0,1],p),p,t)
 H=nmod_poly([int(V(q).x[0]) for q in M],p)
 assert H.degree()==len(M)-1 and H.leading_coefficient()==1
 for fac,_ in H.factor()[1]:
  U=Bfield(fac,p,t);s=U(nmod_poly([0,1],p))
  A,B,m,ha,hb,anc,g,X,C,D,q0,q1,L,H4=pair_data(U,f,slot,rear,ori)
  assert bool(q1)==bool(pair_data(F2,f,slot,rear,ori)[11])
  if rear is not None:
   Y=missing(U,g,q0,q1,[g*v for v in (anc,X,C,D)],3)
   assert Y is not None
   Y,rr=qr(Y,[-s,U(1)]);assert not rr and len(Y)==3
  else:
   Y=missing(U,g,q0,q1,[g*v for v in (anc,X,C,s)],3)
   assert Y is not None
  testrow5(U,f,slot,A,B,m,ha,hb,anc,g,X,C,D,q0,q1,L,H4,s,Y,rear is not None)
 return True
