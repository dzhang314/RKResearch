"""Exact tail-leading-zero branch, with no rational pole inverse."""
from nofront_arith_tails import *
from nofront_arith_cross import fronts as front_polys,E_su
from constant_front_tail import gammas
from front_tail_close import split_deg,unit_b,test_unit
from front_gauss_nonliteral import fterms
from literal_shared_pole_late import polyres
from one_front_zero import Nested
from extra_active import bezout
from shared_arith_checks import inverse_one

def nodal_y5(F,gg,pegs,q0,q1):
 L=list(map(F,Lco))
 C=[q0*q0,2*q0*q1,q1*q1]
 W=bezout()
 V=[sum(C[j]*F(W[j][k]) for j in range(3) if k<len(W[j])) for k in range(4)]
 H=[F(1)]+[F(0)]*7;Hs=[]
 for p in pegs:
  H=list(H)
  for j in range(1,8):H[j]+=p*H[j-1]
  Hs.append(H)
 A=[]
 for i in range(4):
  A.append([sum(L[k]*Hs[i][k+j-i] for k in range(5) if k+j>=i) for j in range(4)]
           +[sum(V[k]*Hs[i][k-i] for k in range(i,4))])
 Z=[]
 for j in range(4):
  Z.append([sum(L[k]*H[k+j-4-d] for k in range(5) if k+j>=4+d)*gg**d for d in range(j+1)])
 Z.append([])
 return sum_poly([sc(Z[j],(-1)**j*det([[x for k,x in enumerate(r) if k!=j] for r in A])) for j in range(4)])

def check(f,i,p,t):
 R,q0p,q1p,safe=tail(f,i)
 rv=Vcoeff(R)
 GG=unef(e_sf(eguard(ef(rv[-1]),[ef(Gcoeff(x)) for x in safe])))
 assert len(GG)-1==4
 Fp,_,_,_=front_polys(f,i)
 ph=[[unef(v) for v in a] for a in E_su(Fp)]
 q0c,q1c=map(Vcoeff,(q0p,q1p))
 fd=frontdata(f,i)
 n=0;fails=[]
 for J,k in split_deg(GG,rv):
  assert k==4
  for G,gg in gammas(J,p,t):
   evg=lambda p:ev(list(map(G,p)),gg)
   ur=trim([evg(v) for v in rv]);assert len(ur)==k+1
   U=Tower(mon(ur));u0=U.gen();g0=U(gg)
   evu=lambda b:ev([U(evg(w)) for w in b],u0)
   S=[evu(v) for v in ph]
   assert len(S)==4
   n+=1
   if not unit_b(U,S[-1]):
    fails.append((n,'s leading'));continue
   W=Nested(sc(S,inverse_one(U,S[-1])));s0=W.gen()
   g0,u0=W(g0),W(u0)
   a,b,ha=map(W,fd[5:8]);H4=list(map(W,fd[8]))
   x=1-g0;c=x-g0*u0;d=x-2*g0*u0
   q0,q1=W(evu(q0c)),W(evu(q1c))
   L=list(map(W,Lco));La=ev(L,g0*a)
   Qp=[La*q0,La*g0*q1];Pp=[ha*(q0+q1*g0*a)*v*g0**j for j,v in enumerate(L)]
   h,T0,A0,T1,A1=fterms(W,fd,a,s0,H4)
   T=add(sc(mul(T0,Qp),h),mul(T1,Pp));A=add(sc(mul(A0,Qp),h),mul(A1,Pp))
   D=list(map(W,nodal([a,s0])))
   T,r=qr(T,D);assert not r
   A,r=qr(A,D);assert not r
   Y=nodal_y5(W,g0,[x,c,d,g0*s0],q0,q1)
   if not test_unit(W,polyres(W,Y,T,3,3),polyres(W,Y,A,3,3),polyres(W,T,A,3,3)):
    fails.append((n,'residual',str(G.M)))
 print('exact tail-leading-zero phase',f,i,p,n,fails,flush=True)
 return fails

if __name__=='__main__':
 from itertools import product
 for f,i in product((True,False),(0,1)):
  check(f,i,1103,161)
