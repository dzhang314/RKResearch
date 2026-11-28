"""Use signed rational masked moments at actual fifth in the centered seven-distinct chart."""
from shared_star_projection import *
from constant_front_tail import gammas
from front_tail_close import split_deg,test_unit
from front_gauss_nonliteral import fterms
from literal_shared_pole_late import polyres
from off8_fibers import cramer

def mmask(F,X,xi,count):
 L=list(map(F,Lco));q=[-xi,F(1)]
 I=lambda f:sum(F(c)/(j+1) for j,c in enumerate(f))
 S,r0=qr(L,q);P,r1=qr(S,q)
 assert len(r0)==1 and len(r1)<=1
 delta=r0[0];D=r1[0] if r1 else F(0)
 A=-I(S)/delta;B=-(I(mul(S,S))+2*delta*(I(P)+D*A))/(delta*delta)
 q2=mul(q,q)
 V=[]
 for j in range(count):
  w,r=qr([F(0)]*j+X,q2)
  r=r+[F(0)]*(2-len(r))
  V.append(I(w)+r[0]*B+r[1]*(A+xi*B))
 return V

def cmask(F,g,M,k):
 H=[[M[i+j] for j in range(k)] for i in range(k)]
 D=det(H)
 return [v*g**i for i,v in enumerate(cramer(H,[-M[k+i] for i in range(k)]))]+[D*g**k]

def phase(f,i,p,t):
 G,Phi,D,A,B,q0p,q1p=build(f,i)
 pc,dc=Scoeff(Phi),Scoeff(D)
 q0c,q1c=Vcoeff(q0p),Vcoeff(q1p)
 fd=frontdata(f,i);n=0
 for J,ds in split_deg(G,pc):
  for F,g in gammas(J,p,t):
   gg=lambda L:ev(list(map(F,L)),g)
   u0=trim([gg(v) for v in pc])
   u1=trim([gg(v) for v in dc])
   assert len(u0)==ds+1
   S=gcdp(u0,u1)
   if len(S)<=1:continue
   n+=1
   W=Tower(S);s0=W.gen();ggg=W(g)
   a,b,ha=map(W,fd[5:8]);H4=list(map(W,fd[8]))
   v0=-gg(A)/gg(B)
   q0=ev([gg(r) for r in q0c],v0);q1=ev([gg(r) for r in q1c],v0)
   xi=W(-q0/q1)
   p4=list(map(W,Lco));X=1-ggg;mid=X-ggg
   R=mul(list(map(W,nodal([ggg*a,X]))),[mid*mid-ggg*ggg*W(v0),-2*mid,W(1)])
   N3=cmask(W,ggg,mmask(W,R,xi,6),3)
   E0=ev(N3,s0)
   R5=mul(R,[-ggg*s0,W(1)])
   mr=mmask(W,R5,xi,5)
   P2=cmask(W,ggg,mr,2)
   Dr=det([[mr[i+j] for j in range(3)] for i in range(3)])
   Lp=ev(p4,ggg*a)
   Q=[Lp*W(q0),Lp*W(q1)*ggg]
   P=[ha*(W(q0)+W(q1)*ggg*a)*v*ggg**j for j,v in enumerate(p4)]
   hh,T0,A0,T1,A1=fterms(W,fd,a,s0,H4)
   X=add(sc(mul(T0,Q),hh),mul(T1,P));Y=add(sc(mul(A0,Q),hh),mul(A1,P))
   ny=list(map(W,nodal([a,s0])))
   X,r=qr(X,ny);assert not r
   Y,r=qr(Y,ny);assert not r
   E1,E2,E3=polyres(W,P2,X,2,3),polyres(W,P2,Y,2,3),polyres(W,X,Y,3,3)
   assert test_unit(W,E0,Dr,E1,E2,E3)
 assert n
 print('verified shared star literal fourth/fifth gates:',f,i,p,n,flush=True)
 return True
