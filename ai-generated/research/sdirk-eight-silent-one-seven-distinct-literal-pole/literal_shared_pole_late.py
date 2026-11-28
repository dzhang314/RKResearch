"""Strict fourth and fifth for the no-extra one-front chart."""
from literal_shared_pole_front import *
from one_front_zero import Nested
from gauss_separate import span_unit

def squarefree(a):
 d=[a[i]*i for i in range(1,len(a))]
 b=gcdp(a,d)
 return mon(divp(a,b)[0])

def split_degree(G,U):
 G=squarefree(G)
 for n in range(len(U)-1,-1,-1):
  C=gcdp(G,U[n])
  D=mon(divp(G,C)[0])
  if len(D)>1:yield D,n
  G=C
  if len(G)<=1:return
 assert len(G)<=1

def polyres(F,a,b,m,n):
 a,b=trim(a),trim(b)
 if not a or not b:return F(0)
 assert len(a)<=m+1 and len(b)<=n+1
 a.extend([F(0)]*(m+1-len(a)));b.extend([F(0)]*(n+1-len(b)))
 # No inverse; routine used on small n,m over a nonreduced finite ring.
 X=[[F(0)]*(m+n) for _ in range(m+n)]
 aa=a[::-1];bb=b[::-1]
 for j in range(n):X[j][j:j+m+1]=aa
 for j in range(m):X[j+n][j:j+n+1]=bb
 @lru_cache(None)
 def sub(i,bits):
  if not bits:return F(1)
  z=F(0);sg=1
  for j in range(m+n):
   if bits>>j&1:
    if X[i][j]:z+=sg*X[i][j]*sub(i+1,bits^(1<<j))
    sg=-sg
  return z
 return sub(0,(1<<(m+n))-1)

def known_guards(f,i,kind,A,g,u,frontdata0):
 A0,B0,m,ha,hb,aa,bb,hh,*_=frontdata0
 a,b=map(A,(aa,bb))
 x=1-g;c=x-g*u;z=g*b
 k=1+2*u-u*u
 d=z if kind is None else x-g*(2-u if kind else 2*u)
 LL=list(map(A,Lco))
 g.inv();ev(LL,z).inv() # Actual diagonal and rational moment denominator.
 return a,b,x,c,d,z,k


def moments(A,g,z,pegs,n):
 M=moment(A,pegs,[-z,A(1)],2*n)
 H=[[M[i+j] for j in range(n)] for i in range(n)]
 D=det(H)
 N=[x*g**i for i,x in enumerate(cramer(H,[-M[n+j] for j in range(n)]))]+[D*g**n]
 return N,D

def phi(F,f,i,g,a,b,hh,H4):
 Lp=[g**j*F(v) for j,v in enumerate(Lco)]
 den=ev(Lp,a)
 Q=[-b*den,den]
 P=sc(Lp,hh*(a-b))
 P4=add(mul(Q,H4),sc(P,-1))
 # Active fourth cannot repeat either literal physical front clock.
 T,R=qr(P4,[-a,F(1)]);assert not R
 return P4,T,Q,P

def fourth_silent_equations(F,ff,ii,g,u,tail,out):
 _,_,_,ha,hb,aa,bb,hh,H4,L0,e,tau,ah,HS,XT,XA,dT,dA,T4,A4=out
 a,b,x,c,d,z,k=tail
 H4=list(map(F,H4));P4,Phi,Q,P=phi(F,ff,ii,g,a,b,F(hh),H4)
 return H4,P4,Phi,Q,P
def verify_late(f,i,kind,p,t):
 G,U0,V0=tails(f,i,kind)
 Z=Bfield(nmod_poly([0,1],p),p,t)
 ks=[]
 fd=frontdata(f,i)
 cases=list(split_degree(G,U0))
 assert {n for _,n in cases}==({3} if kind is None else {2,3})
 for H,n in cases:
  M=nmod_poly([int(Z(v).x[0]) for v in H],p)
  assert M.degree()==len(H)-1
  for B,_ in M.factor()[1]:
   W=Bfield(B,p,t);g0=W(nmod_poly([0,1],p))
   uv=[ev(list(map(W,v)),g0) for v in U0]
   vv=[ev(list(map(W,v)),g0) for v in V0]
   assert len(trim(uv))==n+1,(H,n,B,len(trim(uv)))
   uv=mon(trim(uv))
   H2=gcdp(uv,vv)
   if len(H2)<=1:continue
   A=Tower(H2);g=A(g0);u=A.gen()
   a,b,x,c,d,z,k=tail=known_guards(f,i,kind,A,g,u,fd)
   ks.append((B.degree(),len(H2)-1))
   H4,P4,Phi,Q,P=fourth_silent_equations(A,f,i,g,u,tail,fd)
   if kind is not None:
    N,D=moments(A,g,z,[g*a,x,c,d],3)
    r=polyres(A,Phi,N,3,3)
    r.inv()
   else:
    assert len(trim(Phi))==4
    Phi[-1].inv()
    Phi=mon(Phi)
    V=Nested(Phi);s0=V.gen()
    h4=ev(list(map(V,H4)),s0)
    a0,b0=V(a),V(b)
    A0,B0=map(V,fd[:2])
    L0,e=list(map(V,fd[9])),list(map(V,fd[10]))
    tau,ah=map(V,fd[11:13])
    XT=ev(list(map(V,exact_uc_y(fd[14]))),s0)
    XA=ev(list(map(V,exact_uc_y(fd[15]))),s0)
    dT=ev(list(map(V,fd[16])),s0)
    dA=ev(list(map(V,fd[17])),s0)
    ab=A0*B0;ss=A0+B0
    m0=[V(-1),V(1)]
    m1=[V(0),V(-1),V(1)/2]
    m2=[V(0),V(0),V(-1),V(1)/3]
    J=sum_poly([m2,sc(m1,-ss),sc(m0,ab)])
    T0=sum_poly([[V(0)]*3+[V(1),V(-1)/4],sc(m2,ss),sc(m1,-ab),sc(J,s0)])
    A0=sum_poly([sc(m0,L0[0]),sc(m1,L0[1]),sc(J,ev(e,s0))])
    T1=[h4*(dT-tau)+XT*a0,-XT]
    A1=[h4*(dA-ah)+XA*a0,-XA]
    F1=add(sc(mul(T0,list(map(V,Q))),h4),mul(T1,list(map(V,P))))
    F2=add(sc(mul(A0,list(map(V,Q))),h4),mul(A1,list(map(V,P))))
    # Padded y=a is guaranteed only after the current Phi relation.
    F1,E1=qr(F1,[-a0,V(1)]);F2,E2=qr(F2,[-a0,V(1)]);assert not E1 and not E2
    N,D=moments(V,V(g),V(z),[*map(V,(g*a,x,c)),V(g)*s0],3)
    R1=polyres(V,N,F1,3,4);R2=polyres(V,N,F2,3,4)
    span_unit(V,R1,R2)
 print('verified literal pole tail:',f,i,kind,'local gap degrees',ks,flush=True)
 return True
