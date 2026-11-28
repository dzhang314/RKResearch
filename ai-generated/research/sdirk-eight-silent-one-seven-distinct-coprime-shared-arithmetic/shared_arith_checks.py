"""Pole-free fifth node residuals in the shared arithmetic chart."""
from shared_arith_projection import *
from constant_front_tail import gammas
from front_tail_close import split_deg,test_unit,unit_b
from front_gauss_nonliteral import fterms
from literal_shared_pole_late import polyres
from one_front_zero import Nested
from pseudo_cut import fast_cuts

def UScoeff(F):
 V={}
 for (i,j,k,l),a in can(F).to_dict().items():
  d=V.setdefault(i,{}).setdefault(j,{})
  d[k]=d.get(k,F2(0))+F2(E(a) if not l else E(0,a))
 return [[trim([V.get(i,{}).get(j,{}).get(k,F2(0)) for k in range(max(V.get(i,{}).get(j,{}),default=-1)+1)])
          for j in range(max(V.get(i,{}),default=-1)+1)]
         for i in range(max(V,default=-1)+1)]

def evaluate(F,gg,P,u):
 return ev([ev(list(map(F,a)),gg) for a in P],u)

def inverse_one(U,v):
 n=len(U.F)-1;F=U.B
 cols=[]
 for j in range(n):
  c=(v*U([F(0)]*j+[F(1)])).x
  cols.append(c+[F(0)]*(n-len(c)))
 M=list(zip(*cols));d=det(M).inv()
 from off8_fibers import cramer
 w=U([x*d for x in cramer(M,[F(1)]+[F(0)]*(n-1))])
 assert v*w==1
 return w

def phase(f,i,p,t):
 M,Phi,D,R,P0,q0p,q1p=build_arith(f,i)
 U0,U1=Vcoeff(R),Vcoeff(P0)
 AP,DP=map(UScoeff,(Phi,D))
 Q0,Q1=map(Vcoeff,(q0p,q1p))
 fd=frontdata(f,i);n=0
 for J,RR,d in fast_cuts(f,i):
  if len(RR)<=1:
   assert RR==[[F2(1)]]
   continue
  for F,gg in gammas(J,p,t):
   at=lambda X:ev(list(map(F,X)),gg)
   A=trim([at(w) for w in RR]);assert len(A)==len(RR)
   B=trim([at(w) for w in U1])
   D0=gcdp(A,B)
   if len(D0)<=1:continue
   n+=1
   U=Tower(D0);u=U.gen();g=U(gg)
   atU=lambda X:evaluate(U,g,X,u)
   Uphi=[atU(w) for w in AP]
   Udet=[atU(w) for w in DP]
   assert len(Uphi)==len(Udet)==4
   C=None
   if unit_b(U,Uphi[-1]):C=Uphi
   elif unit_b(U,Udet[-1]):C=Udet
   else:
    for k in range(1,20):
     L=add(Uphi,sc(Udet,k))
     if len(L)==4 and unit_b(U,L[-1]):C=L;break
   assert C is not None,(n,'both s leading')
   W=Nested(sc(C,inverse_one(U,C[-1])));ss=W.gen();g0=W(g);u0=W(u)
   a,b,ha=map(W,fd[5:8]);H4=list(map(W,fd[8]))
   q0,q1=W(atU(Q0)),W(atU(Q1))
   L=list(map(W,Lco));La=ev(L,g0*a)
   Qp=[La*q0,La*q1*g0];Pp=[ha*(q0+q1*g0*a)*v*g0**k for k,v in enumerate(L)]
   h,T0,A0,T1,A1=fterms(W,fd,a,ss,H4)
   A=add(sc(mul(T0,Qp),h),mul(T1,Pp));B=add(sc(mul(A0,Qp),h),mul(A1,Pp))
   D1=list(map(W,nodal([a,ss])))
   A,e0=qr(A,D1);B,e1=qr(B,D1)
   Y,r=qr(list(map(W,Udet)),[-ss,W(1)])
   P=ev(list(map(W,Uphi)),ss)
   E1,E2,E3=polyres(W,Y,A,2,3),polyres(W,Y,B,2,3),polyres(W,A,B,3,3)
   assert test_unit(W,r[0] if r else W(0),P,E1,E2,E3),(n,'fifth')
 assert n
 print('verified arithmetic shared reduced checks',f,i,p,n,flush=True)
 return True
