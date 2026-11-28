#!/usr/bin/env python3
"""Exact reciprocal rank check and two ordered nonalias intervals; python-flint 0.9.0."""
import flint
from itertools import permutations
F=flint.fmpq
P=flint.fmpq_poly
x=P([0,1]);one=P([1]);zero=P()
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def dot(L,R):
 return 210*sum((L[i]*N[i][j]*R[j] for i in range(5) for j in range(5)),zero)
def scale(L,s):return [c*s for c in L]
def sub(A,B):return [u-v for u,v in zip(A,B)]
def add(A,B):return [u+v for u,v in zip(A,B)]
def EL(y):return [y**(j+1) for j in range(5)]
def ER(y):return [(1-y)*y**j for j in range(5)]
def int_(p):
 return p.integral()(1)
def response(a,d):
 W=x*x*(x-a)**2; V=(1-x)**2*(x-d)**2
 PL=W.integral(); PR=int_(V)-V.integral()
 H=int_(PL*V); C1=int_(x*PL*V);C2=int_(x*W*PR);J=int_(PL*PR)
 I0,I1,I2=[int_(x**j*W*V) for j in range(3)]
 assert J==C1-C2 and H==int_(W*PR)
 return W,V,PL,PR,H,C1,C2,J,I0,I1,I2
def qvec(A,p):
 out=[]
 for t in A:
  q,r=divmod(t,p);assert r.is_zero();out.append(q)
 return out
def det(M):
 n=len(M);o=zero
 for pm in permutations(range(n)):
  v=one
  for i,j in enumerate(pm):v*=M[i][j]
  sg=sum(pm[i]>pm[j] for i in range(n) for j in range(i+1,n))
  o=o-v if sg%2 else o+v
 return o
def coeffs(f):
 p00=f(0,0);p10=f(1,0);p01=f(0,1);p11=f(1,1)
 return [p00,p10-p00,p01-p00,p11-p10-p01+p00]
def rows(a,d):
 W,V,PL,PR,H,C1,C2,J,I0,I1,I2=response(a,d)
 A=x*(x-a);B=(1-x)*(x-d)
 lp=scale(EL(a),1/PL(a));rp=scale(ER(d),1/PR(d))
 l=qvec(sub(EL(x),scale(lp,PL)),A)
 r=qvec(sub(ER(x),scale(rp,PR)),B)
 DL0=[1,0,0,0,0];DLa=[(i+1)*a**i for i in range(5)]
 DR1=[1]*5;DRd=[d**i-((1-d)*i*d**(i-1) if i else 0) for i in range(5)]
 def lr(u,v):return add(l,scale(lp,u)),add(r,scale(rp,v))
 def d1(u,v):
  L,R=lr(u,v)
  return dot(L,R)-u*v/J
 def d2(u,v):
  L,R=lr(u,v)
  Lb=sub(scale(DL0,dot(DLa,R)),scale(DLa,dot(DL0,R)))
  Rb=sub(scale(DR1,dot(L,DRd)),scale(DRd,dot(L,DR1)))
  return dot(Lb,Rb)
 M0=I1-x*I0;T=I2-2*x*I1+x*x*I0
 E1=C1-H*x;E2=C2-H*x
 U=J*A;V0=J*B
 c=[U*V0*(J*T-E1*E2),J*V0*(-H*T+E2*M0),J*U*(-H*T+E1*M0),
    P([J*(H*H*I2-H*(C1+C2)*I1+I0*C1*C2)])]
 return [coeffs(d1),coeffs(d2),c]
def verify_schur(a,d,M):
    W,V,PL,PR,H,C1,C2,J,I0,I1,I2=response(a,d)
    Y=1-x
    b=1-d
    l=[x-x*x/(2*a),x*x/(2*a),W,x*W,PL]
    r=[Y-Y*Y/(2*b),Y*Y/(2*b),V,x*V,PR]
    G=flint.fmpq_mat([[int_(f*g) for g in r] for f in l])
    assert G.det()!=0
    K=G.inv().transpose()
    D2=K[0,0]*K[1,1]-K[0,1]*K[1,0]
    G3=flint.fmpq_mat([[I0,I1,H],[I1,I2,C2],[H,C1,J]])
    assert D2*G.det()==G3.det()
    A,B,C=M
    assert all(v==J**2*G.det()*(D2*u-w) for u,w,v in zip(A,B,C))
    print('widths',a,d,'exact Schur redundancy of all 4 mixed coefficients')

def pullback(f,lo,hi):
    n=f.degree()
    return sum((c*(lo+hi*x)**j*(1+x)**(n-j) for j,c in enumerate(f.coeffs())),zero)

def replay():
    for a,d in ((F(2,5),F(1,3)),(F(1,5),F(2,5)),(F(1,3),F(3,4))):
        M=rows(a,d)
        assert [[q.degree() for q in m] for m in M]==[[6,3,3,0]]*3
        verify_schur(a,d,M)
    A,B,C=rows(F(1,5),F(2,5))
    E0=A[0]*C[2]-C[0]*A[2]
    E1=A[0]*C[3]+A[1]*C[2]-C[0]*A[3]-C[1]*A[2]
    E2=A[1]*C[3]-C[1]*A[3]
    assert [v.degree() for v in (E0,E1,E2)]==[9,6,3]
    assert E0.gcd(E1).gcd(E2).degree()==0
    disc=E1**2-4*E0*E2
    assert disc.degree()==12
    print('a=1/5,d=2/5: quadratic coefficient degrees (9,6,3), joint zeta gcd 1; discriminant degree 12')
    for lo,hi in ((F(133,200),F(67,100)),(F(7,10),F(3,4))):
        h=pullback(disc,lo,hi)
        assert h.degree()==12 and all(c<0 for c in h.coeffs())
        assert disc(hi)<0
        print('closed interval',lo,hi,': all 13 exact homogeneous discriminant coefficients negative')
    print('all exact nonalias quadratic and ordered checks passed')

if __name__=='__main__':
    replay()
