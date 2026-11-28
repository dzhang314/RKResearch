"""Diagnostic and finite residual checks for the no-literal arithmetic chart."""
from fourth_drop_branch import *
from infinity_certificate import inputs
from reduced_projection import reduced
from shared_silent8_projection import red_e
from flint import fq_default_ctx,fq_default_poly_ctx,fmpz_mod_poly_ctx,nmod_poly
from leading_branch import nodal_y5
from nofront_arith_cross import s as ss,g as gg,term,L,CX,fold
from collections import Counter
from time import perf_counter

def H4_support(f,i):
 H4=term(frontdata(f,i)[8],ss)
 return e_sf(E_su(fold(H4.resultant(L(gg*ss),1)))[0][0])

def ff_factors(G,P,p):
 M=fmpz_mod_poly_ctx(p)(list(map(int,G.M)))
 C=fq_default_ctx(modulus=M,check_modulus=False)
 PC=fq_default_poly_ctx(C)
 pol=PC([C(list(map(int,a.x))) for a in P])
 _,V=pol.factor()
 GG=lambda a:G(nmod_poly(list(map(int,a.to_list())),p))
 return [[GG(a) for a in u] for u,_ in V]

def reg_data(f,i):
 rv,q0,q1,sa=tail(f,i)
 R,Phi,J,_,_=inputs(f,i)
 sp=guards(f,i);hf=H4_support(f,i)
 tx=exact_carrier(f,i)[0]
 E0=[ef(Gcoeff(v)) for v in sa]+[R[-1]]
 return R,Phi,J,q0,q1,E0,sp,tx,hf

def residual(F,g,u,s,f,i,q0,q1):
 fd=frontdata(f,i)
 a,b,ha=map(F,fd[5:8]);H4=list(map(F,fd[8]))
 x=1-g;c=x-g*u;d=x-2*g*u
 L=list(map(F,Lco));La=ev(L,g*a)
 Qp=[La*q0,La*g*q1];Pp=[ha*(q0+q1*g*a)*v*g**j for j,v in enumerate(L)]
 h,T0,A0,T1,A1=fterms(F,fd,a,s,H4)
 T=add(sc(mul(T0,Qp),h),mul(T1,Pp));A=add(sc(mul(A0,Qp),h),mul(A1,Pp))
 D=list(map(F,nodal([a,s])))
 T,r=qr(T,D);assert not r
 A,r=qr(A,D);assert not r
 B=nodal_y5(F,g,[x,c,d,g*s],q0,q1)
 return T,A,B

def U_gammas(M,p,t):
 for d,_ in M.factor()[1]:
  G=Bfield(d,p,t);g=G(nmod_poly([0,1],p))
  yield d,G,g
