"""Separate reverse aggregate at an actual literal front, constant Q."""
from literal_shared_pole_late import *
from constant_q_nonzero import moment_const

@lru_cache(None)
def ctail(f,i,kind,shared=False):
 # i labels the actual silent literal clock at the reverse root.
 # In the shared chart its individual defect is not transported.
 A,B,m,ha,hb,a,b,h,*_=frontdata(f,i)
 L4=lambda v:sum(vv*v**j for j,vv in enumerate(Lco))
 a,b=map(expr,(a,b));z=g*a
 x=1-g;c=x-g*u
 k=1+2*u-u*u
 px,pc=L4(x),L4(c)
 qx,qc=x-z,c-z
 F9=exdiv(can(pc*qx-k*px*qc),u)
 if kind is None:
  assert shared
  F8=can(2*qx+g*k*(u-2))
 else:
  d=x-g*(2-u if kind else 2*u)
  pd,qd=L4(d),d-z
  if kind:
   F8=exdiv(can(pd*qx-k*px*qd),u-2)
   F8=exdiv(can(F8+F9),u-1)
  else:
   H=-2+u+4*u*u-u**3;T=4*u**3-12*u*u+3*u+2
   F8=exdiv(can(H*pd*qx+k*T*px*qd),u)
   while True:
    J,R=divmod(F8,u)
    if can(R):break
    F8=can(J)
 gl=[g,qx,px]+([] if shared else [L4(z)])
 guards=[gcoeff(can(v)) for v in gl]
 J=gcoeff(can(F9.resultant(F8,1)))
 G=mon(guarded(J,guards))
 const=gcoeff(can(expr(ha)*L4(g*expr(frontdata(f,i)[1]))-expr(hb)*L4(g*expr(frontdata(f,i)[0]))))
 Aonly=gcdp(G,const)
 assert len(G)-1==({True:16,False:35,None:14}[kind])
 print('constant literal tail',f,i,kind,shared,len(G)-1,'both exact literals',len(Aonly)-1,flush=True)
 return G,exact_uc(F9),exact_uc(F8),Aonly

def cphi(F,ff,ii,g,a,b,hh,H4):
 Lp=[g**j*F(v) for j,v in enumerate(Lco)]
 den=ev(Lp,a)
 Q=[den]
 P=sc(Lp,hh)
 P4=add(mul(Q,H4),sc(P,-1))
 T,R=qr(P4,[-a,F(1)]);assert not R
 return P4,T,Q,P

def cmoments(A,g,pegs,n):
 M=moment_const(A,pegs,2*n)
 H=[[M[i+j] for j in range(n)] for i in range(n)]
 D=det(H)
 N=[x*g**i for i,x in enumerate(cramer(H,[-M[n+j] for j in range(n)]))]+[D*g**n]
 return N,D

def fifth(F,gg,fd,a,b,s0,H4,Q,P):
 h4=ev(list(map(F,H4)),s0)
 A0,B0=map(F,fd[:2])
 L0,e=list(map(F,fd[9])),list(map(F,fd[10]))
 tau,ah=map(F,fd[11:13])
 XT=ev(list(map(F,exact_uc_y(fd[14]))),s0)
 XA=ev(list(map(F,exact_uc_y(fd[15]))),s0)
 dT=ev(list(map(F,fd[16])),s0)
 dA=ev(list(map(F,fd[17])),s0)
 ab=A0*B0;ss=A0+B0
 m0=[F(-1),F(1)]
 m1=[F(0),F(-1),F(1)/2]
 m2=[F(0),F(0),F(-1),F(1)/3]
 J=sum_poly([m2,sc(m1,-ss),sc(m0,ab)])
 T0=sum_poly([[F(0)]*3+[F(1),F(-1)/4],sc(m2,ss),sc(m1,-ab),sc(J,s0)])
 A0=sum_poly([sc(m0,L0[0]),sc(m1,L0[1]),sc(J,ev(e,s0))])
 T1=[h4*(dT-tau)+XT*a,-XT]
 A1=[h4*(dA-ah)+XA*a,-XA]
 F1=add(sc(mul(T0,list(map(F,Q))),h4),mul(T1,list(map(F,P))))
 F2=add(sc(mul(A0,list(map(F,Q))),h4),mul(A1,list(map(F,P))))
 F1,E1=qr(F1,[-a,F(1)]);F2,E2=qr(F2,[-a,F(1)]);assert not E1 and not E2
 return F1,F2

def ctest(f,i,kind,p,t):
 G,U0,V0,C=ctail(f,i,kind)
 # One-active / literal sole transported hence both literal readings on profile.
 assert len(C)==1
 Z=Bfield(nmod_poly([0,1],p),p,t)
 fd=frontdata(f,i)
 ks=[]
 cases=list(split_degree(G,U0))
 assert {n for _,n in cases}=={3}
 for H,n in cases:
  M=nmod_poly([int(Z(v).x[0]) for v in H],p)
  assert M.degree()==len(H)-1
  for B,_ in M.factor()[1]:
   W=Bfield(B,p,t);g0=W(nmod_poly([0,1],p))
   uv=trim([ev(list(map(W,v)),g0) for v in U0])
   vv=[ev(list(map(W,v)),g0) for v in V0]
   assert len(uv)==n+1
   Hg=gcdp(uv,vv)
   if len(Hg)<=1:continue
   F=Tower(Hg);gamma=F(g0);u=F.gen()
   a,b=map(F,fd[5:7]);ha=F(fd[7])
   z=gamma*a;x=1-gamma;c=x-gamma*u
   d=x-gamma*(2-u if kind else 2*u)
   H4=list(map(F,fd[8]))
   P4,Phi,Q,P=cphi(F,f,i,gamma,a,b,ha,H4)
   ks.append((B.degree(),len(Hg)-1))
   assert len(Phi)==4
   Phi[-1].inv()
   S=Nested(mon(Phi));s=S.gen()
   F1,F2=fifth(S,S(gamma),fd,S(a),S(b),s,H4,Q,P)
   N,D=cmoments(S,S(gamma),[S(x),S(c),S(d),S(gamma)*s],3)
   R1=polyres(S,N,F1,3,4);R2=polyres(S,N,F2,3,4)
   span_unit(S,R1,R2)
 print('verified constant literal reverse root:',f,i,kind,p,ks,flush=True)
 return True


def cshared(f,i,kind,p,t):
 # Only physical clocks are shared: no assignment of individual h or w.
 G,U0,V0,C=ctail(f,i,kind,True)
 Z=Bfield(nmod_poly([0,1],p),p,t)
 fd=frontdata(f,1-i)
 ks=[]
 cases=list(split_degree(G,U0))
 assert {n for _,n in cases}=={3}
 for H,n in cases:
  M=nmod_poly([int(Z(v).x[0]) for v in H],p)
  assert M.degree()==len(H)-1
  for B,_ in M.factor()[1]:
   W=Bfield(B,p,t);g0=W(nmod_poly([0,1],p))
   uv=trim([ev(list(map(W,v)),g0) for v in U0])
   vv=[ev(list(map(W,v)),g0) for v in V0]
   assert len(uv)==n+1
   Hg=gcdp(uv,vv)
   if len(Hg)<=1:continue
   F=Tower(Hg);gamma=F(g0);u=F.gen()
   a,b=map(F,fd[5:7]);ha=F(fd[7])
   x=1-gamma;c=x-gamma*u
   H4=list(map(F,fd[8]))
   P4,Phi,Q,P=cphi(F,f,1-i,gamma,a,b,ha,H4)
   ks.append((B.degree(),len(Hg)-1))
   if kind is not None:
    d=x-gamma*(2-u if kind else 2*u)
    N,D=cmoments(F,gamma,[gamma*a,x,c,d],3)
    polyres(F,Phi,N,3,3).inv()
   else:
    assert len(Phi)==4
    Phi[-1].inv()
    S=Nested(mon(Phi));s=S.gen()
    F1,F2=fifth(S,S(gamma),fd,S(a),S(b),s,H4,Q,P)
    N,D=cmoments(S,S(gamma),[S(gamma*a),S(x),S(c),S(gamma)*s],3)
    span_unit(S,polyres(S,N,F1,3,4),polyres(S,N,F2,3,4))
 print('verified constant shared literal clock:',f,i,kind,p,ks,flush=True)
 return True
