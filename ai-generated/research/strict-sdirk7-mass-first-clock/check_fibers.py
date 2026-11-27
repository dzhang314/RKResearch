#!/usr/bin/env python3
from flint import fmpz_mpoly_ctx,fmpz_poly,nmod_poly
from sympy import primerange
from math import prod
import argparse

def asvalue(C,v):return C.constant(v) if isinstance(v,int) else v
def sat(P,den):
    if not P:return P
    for D in den:
      if not D:raise ArithmeticError('zero chart pivot')
      while (G:=P.gcd(D)).total_degree()>0:
        P,R=divmod(P,G)
        assert not R
    return P

def val(poly,y):
    return sum(c*y**k for k,c in enumerate(poly))

def op(u,r,e):
    M=u*u-4*u+2;T=u**3-7*u*u+10*u-2;J=4*u**3-24*u*u+39*u-17
    v=2*u-1
    # nu clock moments, up to a common nonzero scale.
    A0,A1,A2,A3=((u-3)*(2*u*u-10*u+11),(u-3)*(u-2)*(2*u-3),
       4*(u-2)**2*(u-1),6*(u-1)**2*(2*u-3))
    a,b,c,d=A0,r*A1-A0,3*r*r*A2-6*r*A1+2*A0,5*r**3*A3-15*r*r*A2+12*r*A1-2*A0
    H=[4*a-5*c,12*b-21*d,15*c,35*d]
    G=[9-15*e*e,15*e*(5-7*e*e),15*(3*e*e-1),35*e*(5*e*e-3)]
    F=val(H,e)
    sm=(r-1,r*u-1,r*v-1)
    K=(u-3)*(u-2)**2
    B=(u-3)*(u-1)*(2*u-3)
    L1=M*val(G,sm[0])+val(G,sm[1])
    L0=-M*u*val(G,sm[0])-val(G,sm[1])
    E1=K*(1-M)+3*T
    E0=3*M*B-2*M*K-E1
    kap=T*M*(u-1)*G[3]*r**3-K*L1
    f0=-2*K*(u-1)**3*L0+kap*E0
    f1=-2*K*(u-1)**3*L1+kap*E1
    N,D=-f0,f1
    nu,du=r*N-D,D
    a=1-r
    P=sum((H[i]*G[j]-G[i]*H[j])*sum(a**(i-1-k)*nu**(j+k)*du**(2-j-k)
            for k in range(i-j)) for i in range(1,4) for j in range(i))
    den=[u-1,u-2,u-3,r,M,T,J,G[3],D,kap,L0*D+L1*N,
      *[e-t for t in sm],e-a,nu-e*du,*[nu-t*du for t in sm],nu-a*du]
    return F,P,(N,D),H,G,den

def rootless(F):
    for p in primerange(2,400):
      a=nmod_poly(F.coeffs(),p)
      if a.degree()==F.degree() and not a.roots():
        return p

def univ(P,j=0):
    assert sum(P.degrees())==P.degrees()[j], P.degrees()
    d=P.to_dict()
    return fmpz_poly([int(d.get(tuple(i if k==j else 0 for k in range(len(P.degrees()))),0))
                  for i in range(P.degrees()[j]+1)])

def univ_roots(P):
    c,f=P.factor()
    assert P==c*prod(q**m for q,m in f)
    return [(q.degree(),m,rootless(q),[] if q.degree()!=1 else q.roots()) for q,m in f]

def cut(u):
    C=fmpz_mpoly_ctx.get(('r','e'),'lex')
    r,e=C.gens()
    F,P,K,H,G,d=op(u,r,e)
    d=[asvalue(C,x) for x in d]
    Fs,Ps=(sat(z,d) for z in (F,P))
    R=Fs.resultant(Ps,1)
    print('fixed-u',u,'F/P/R raw',Fs.degrees(),Ps.degrees(),R.degrees(),flush=True)
    R=sat(R,[r])
    if R:
      rec=univ_roots(univ(R))
      expected={-2:(11,11),-1:(11,17),0:(11,19),4:(11,19),5:(11,17),
        6:(17,29),7:(11,17),8:(11,29),9:(11,11)}
      if u in expected:
          p,q=expected[u]
          assert sorted(rec)==[(6,2,p,[]),(42,1,q,[])]
      print(' r factors',rec,flush=True)

def helper_cut(x):
    C=fmpz_mpoly_ctx.get(('u','r'),'lex');u,r=C.gens()
    # y_e=z-x, so centered normalized e is 1-rx.
    F,P,K,H,G,d=op(u,r,1-r*x)
    d=[asvalue(C,x) for x in d]
    Fs,Ps=(sat(z,d) for z in (F,P))
    R=Fs.resultant(Ps,1)
    print('fixed-helper',x,'F/P/R raw',Fs.degrees(),Ps.degrees(),R.degrees(),flush=True)
    R=sat(R,[u-1,u-2,u-3,d[4],d[5],d[6]])
    if R:
      rec=univ_roots(univ(R))
      expected={2:(11,19),4:(11,11),5:(11,29),9:(13,11)}
      if x in expected:
          p,q=expected[x]
          assert sorted(rec)==[(2,1,5,[]),(27,1,p,[]),(66,1,q,[])]
      print(' u factors',rec,flush=True)

def full():
   C=fmpz_mpoly_ctx.get(('u','r','e'),'lex');u,r,e=C.gens()
   F,P,K,H,G,d=op(u,r,e)
   d=[asvalue(C,x) for x in d]
   Fs,Ps=(sat(z,d) for z in (F,P))
   print('full operands',Fs.degrees(),Ps.degrees(),flush=True)
   R=Fs.resultant(Ps,2)
   print('full resultant',R.degrees(),flush=True)
   R=sat(R,[u-1,u-2,u-3,r,d[4],d[5],d[6]])
   q,f=R.factor()
   assert R==q*prod(P**n for P,n in f)
   rec=sorted((F.degrees(),len(F.to_dict()),n) for F,n in f)
   assert rec==[((9,6,0),70,2),((36,42,0),1591,1)]
   print('full factors',rec,flush=True)

if __name__=='__main__':
    a=argparse.ArgumentParser()
    a.add_argument('--u',type=int,nargs='*')
    a.add_argument('--helper',type=int,nargs='*')
    a.add_argument('--full',action='store_true')
    cfg=a.parse_args()
    F,P,(N,D),H,G,den=op(9,13,17)
    assert F%19==P%19==N%19==0 and D%19
    for u in cfg.u or []:cut(u)
    for x in cfg.helper or []:helper_cut(x)
    if cfg.full:full()
