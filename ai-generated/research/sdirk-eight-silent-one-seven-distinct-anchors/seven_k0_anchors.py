"""Detected one-invisible seven distinct active clocks, both literal fronts active, k=0."""
from one_front_zero import *
from arithmetic_nonzero import guarded
from unequal_finite import det3,moment
from off8_fibers import cramer

F2=ExField(E(P([0,1])))
def cv(F,q):return F(Epoly(JJ(q))) if q else F(0)

def hole_terminal(rear,ori,p,t):
 U=Bfield(nmod_poly(list(Lco),p),p,t)
 r=U(nmod_poly([0,1],p));g=1-r
 A,B,m=map(lambda q:cv(U,q),ends(rear,ori));u=A-1
 c,d=1-g*A,1-g*B
 P=Pcoeff(U,r)
 (u*ev(P,d)-(B-1-m)*ev(P,c)).inv()

@lru_cache(None)
def gproj(front,rear,ori):
 U=F2
 A,B,m=map(lambda q:cv(U,q),ends(front,1))
 a,b,n=map(lambda q:cv(U,q),ends(True if rear is None else rear,ori))
 ha,hb=(A-1)/2,(B-1-m)/2
 qa=[U(k)*A**j/ha for j,k in enumerate(Lco)]
 qb=[U(k)*B**j/hb for j,k in enumerate(Lco)]
 q1=sc(add(qb,sc(qa,-1)),1/(B-A))
 q0=add(qa,sc(q1,-A))
 g=[U(0),U(1)];L=list(map(U,Lco));u=a-1
 x=[U(1),U(-1)];c=[U(1),-a];d=[U(1),-b]
 Q=lambda h:add(mul(g,q0),mul(h,q1))
 LC0,LC1,LC2=map(lambda h:subst(L,h),(x,c,d))
 QX,QC,QD=map(Q,(x,c,d))
 if rear is None:G=add(mul(LC1,QX),sc(mul(LC0,QC),-2*u*u))
 else:G=add(sc(mul(LC2,QC),u),sc(mul(LC1,QD),-(b-1-n)))
 assert G
 guards=[g,LC0,LC1,QX,QC,sc(qa,ha),sc(qb,hb)]
 if rear is not None:guards.extend([LC2,QD])
 M=mon(guarded(G,guards))
 print('seven distinct zero factor exact γ',front,rear,ori,len(M)-1,'constant piece',len(gcdp(M,q1))-1,flush=True)
 # Exact homogeneous shared-root polynomial, including gamma=1/2.
 T=mul(g,q0)
 R=sum_poly([sc(mul(power(sc(T,-1),j),power(q1,4-j)),U(l)) for j,l in enumerate(Lco)])
 assert len(gcdp(M,R))==1
 C=gcdp(M,q1)
 if len(C)>1:
  assert rear is not None and len(C)==5
  M=mon(guarded(M,[q1]))
 return M,C,q0,q1

def const_mom(F,pegs):
 L=list(map(F,Lco));D=mul(L,L);assert len(D)==9
 I=[F(1)/(j+1) for j in range(8)]
 a=-sum(D[j]*I[j] for j in range(8))/D[8]
 b=-(sum(D[j]*I[j+1] for j in range(7))+D[7]*a)/D[8]
 I.extend([a,b])
 M=nodal(pegs)
 return [sum(q*I[j+i] for i,q in enumerate(M)) for j in range(5)]

def use(front,rear,ori,p,t):
 M,C,qs0,qs1=gproj(front,rear,ori)
 U=Bfield(nmod_poly([0,1],p),p,t)
 for Y,constant in ((M,False),(C,True)):
  if len(Y)<=1:continue
  G=nmod_poly([int(U(x).x[0]) for x in Y],p)
  assert G.degree()==len(Y)-1 and G.leading_coefficient()==1
  for J0,_ in G.factor()[1]:
   F=Bfield(J0,p,t);g=F(nmod_poly([0,1],p))
   cq=lambda q:cv(F,q)
   A,B,m=map(cq,ends(front,1));a,b,_=map(cq,ends(True if rear is None else rear,ori))
   X=1/g-1;c,d=1-g*a,1-g*b;x=1-g
   Q0,Q1=(ev(list(map(F,q)),g) for q in (qs0,qs1))
   pegs=[g*A,g*B,x,c]+([] if rear is None else [d])
   if constant:
    assert not Q1
    Q0.inv()
    det3(const_mom(F,pegs)).inv()
    continue
   Q1.inv()
   xi=-g*Q0/Q1
   LP=list(map(F,Lco));ev(LP,xi).inv()
   mm=moment(F,pegs,[g*Q0,Q1],6 if rear is None else 5)
   if rear is not None:
    det3(mm).inv();continue
   Hm=[[mm[i+j] for j in range(3)] for i in range(3)]
   n=det(Hm);n.inv()
   ZZ=[q/(n*g**(3-i)) for i,q in enumerate(cramer(Hm,[-mm[3],-mm[4],-mm[5]]))]+[F(1)]
   ha,hb=(A-1)/2,(B-1-m)/2
   H=[cq(q) for q in pol(h4(front),lambda v:v)]
   f0=first5(F,A,B,m,ha,hb,[],H)
   f1=first5(F,A,B,m,ha,hb,[F(1)],H)
   E=add(mul(f0,[Q0,Q1]),mul(add(f1,sc(f0,-1)),[q*g**j for j,q in enumerate(LP)]))
   multicol(ZZ,E).inv()
 return True
