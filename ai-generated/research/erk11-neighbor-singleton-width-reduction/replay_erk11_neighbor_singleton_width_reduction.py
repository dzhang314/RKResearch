#!/usr/bin/env python3
"""Neighboring singleton width gate and finite diagonal-pole projection.
Requires python-flint 0.9.0. No external data or random search.
"""
import flint
from itertools import combinations, permutations
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
def det3(r):
  a,b,c=r
  return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
def num_dot(L,R):return sum((L[i]*N[i][j]*R[j] for i in range(5) for j in range(5)),F(0))
def sample(a,d):
 W,V,p,q,H,C1,C2,J,I0,I1,I2=response(a,d)
 s=C2/H
 z=(I2-s*I1)/(I1-s*I0)
 b=1-d
 A=s*(s-a);B=(1-s)*(s-d)
 if any(v==0 for v in (a,b,A,B,J,I1-s*I0,s-z,C1-H*z)):return
 v=J*B*(s-z)/(C1-H*z)
 Dr=[F(1)]*5;Dd=[d**j-((1-d)*j*d**(j-1) if j else 0) for j in range(5)]
 Dl=[F(1),F(0),F(0),F(0),F(0)];Da=[(j+1)*a**j for j in range(5)]
 lp=scale(EL(a),1/p(a));rp=scale(ER(d),1/q(d))
 L0=scale(sub(EL(s),scale(lp,p(s))),1/A)
 R0=scale(sub(ER(s),scale(rp,q(s))),1/B)
 R=add(R0,scale(rp,v))
 U0=210*num_dot(L0,R);U1=210*num_dot(lp,R)-v/J
 if U1==0:return print(a,d,'u pole',U0)
 u=-U0/U1
 if u==0:return print(a,d,'u zero')
 L=add(L0,scale(lp,u))
 ll0,ll1=[num_dot(vv,R) for vv in (Dl,Da)]
 L7=sub(scale(Dl,ll1),scale(Da,ll0))
 rr0,rr1=[num_dot(L7,vv) for vv in (Dr,Dd)]
 if ll0==0 or rr0==0:return print(a,d,'slope rank',ll0,rr0)
 rho=J/(u*v)
 def solve(left):
  if left:
   w,c,vloc,ol0,ol1,x0=a,d,R,ll0,ll1,s
   sm=s
   e0=P([F(0)]+[sum(N[i][j]*vloc[j] for j in range(5)) for i in range(5)])
  else:
   w,c,vloc,ol0,ol1,x0=b,1-a,L7,rr0,rr1,1-z
   sm=1-s
   zvec=[sum(vloc[i]*N[i][j] for i in range(5)) for j in range(5)]
   e0=sum((g*x*(1-x)**j for j,g in enumerate(zvec)),zero)
  h=w/2; phi=x*x*(w-x)
  B0=x*(x-w)*(x-h);B1=(x-h)*(w*ol0-(ol0-ol1)*x)
  E,r=divmod(w**5*e0-x**3*(6*x**2-15*w*x+10*w*w)*e0(w),x*(x-w));assert r.is_zero()
  S0=-w*E[0]*(x-w)*(x-h)
  S1,r=divmod(w*(E*B1(0)-E[0]*B1),x);assert r.is_zero()
  cols=[phi,x*B0,x*B1,B0,B1]
  wt=x*(1-x)*(x-w)*(x-c)
  M=[[int_(x**j*wt*cc)-rho*sm**j*cc(sm) for cc in cols] for j in range(3)]
  dM=det3([c[:3] for c in M])
  O=[w*x0*(x0-w)*E[0],x0*S0(x0),x0*S1(x0),S0(x0),S1(x0)]
  if dM==0:return
  Cs=[[-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in M]) for i in range(3)]
        for j in (3,4)]
  gg=[sum(c*o for c,o in zip(Cs[j],O[:3]))+dM*O[3+j] for j in range(2)]
  if gg[1]==0:return
  t=-gg[0]/gg[1]
  if t==0:return
  U_,W_,T_=[(c0+t*c1)/dM for c0,c1 in zip(*Cs)]
  P_=w*(U_+(x-h)*(T_-t*W_)/t)
  Q_=U_*phi+W_*x*B0+T_*x*B1+B0+t*B1
  B_=B0+t*B1
  assert B_.degree()==3 and ((Q_-P_*phi/w)%B_).is_zero()
  return P_,Q_,B_,x0
 left,right=solve(True),solve(False)
 if left is None or right is None:return print(a,d,'fixed/affine drop',bool(left),bool(right))
 P_,Q_,Bl,x0=left
 Pr,Qr,Br,z0=right
 mark=P_[0]*Pr[1]+P_[1]*(Pr[0]+Pr[1])
 q2=Qr(1-x)
 qdif=Q_[0]*q2[1]-Q_[1]*q2[0]
 lead_nz=not mark.is_zero() if hasattr(mark,'is_zero') else mark!=0
 q_nz=qdif!=0
 assert lead_nz and all(f!=0 for f in (Bl(x0),Br(z0),P_(x0),Q_(x0),Pr(z0),Qr(z0)))
 assert all(Q_[i]*q2[j]-Q_[j]*q2[i]==0 for i,j in combinations(range(5),2))
 rs=int(mark.numerator)*pow(int(mark.denominator),-1,101)%101
 assert rs==38
 print('regular s=c8 witness (a,d)=(1/5,2/5): all reconstructive guards live, P mark residue 38 mod101; no Q mark')
 return dict(s=s,z=z,u=u,v=v,left=left,right=right,mark=mark,qdif=qdif)
def compact_pole():
    C=flint.fmpq_mpoly_ctx.get(('a','b','X'))
    a,b,X=C.gens()
    R=flint.fmpq_mpoly_ctx.get(('a','b'))
    aa,bb=R.gens()
    rr=R.from_dict({})
    d=1-b
    W=X**2*(X-a)**2
    V=(1-X)**2*(X-d)**2
    def primitive(p):
        return C.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in p.to_dict().items()})
    def integrate(p,shift=0):
        u={}
        for (i,j,k),c in p.to_dict().items():
            u[(i,j,0)]=u.get((i,j,0),0)+c/(k+shift+1)
        return C.from_dict(u)
    def width_poly(p):
        assert p.degrees()[2]<=0
        return R.from_dict({(i,j):c for (i,j,k),c in p.to_dict().items()})
    p=primitive(W)
    q=integrate(V)-primitive(V)
    H=integrate(p*V)
    C1=integrate(p*V,1)
    C2=integrate(W*q,1)
    J=integrate(p*q)
    assert C1-C2==J and H==integrate(W*q)
    I0,I1,I2=[integrate(W*V,k) for k in range(3)]
    T=H**2*I2-2*H*C2*I1+C2**2*I0
    epoch=H*X-C2
    w=(1-X)*(X-d)
    M=[width_poly(T*integrate(p*w*epoch,j)-J*H*integrate(W*w*epoch**2,j))
       for j in range(3)]
    assert all(f.degrees()==(10,9) for f in M)
    assert -M[2]+(2-bb)*M[1]-(1-bb)*M[0]==rr
    for poly in M[:2]:
        dct=poly.to_dict()
        U=P()
        aa_deg,bb_deg=poly.degrees()
        for k in range(bb_deg+1):
            U=U.gcd(P([dct.get((j,k),0) for j in range(aa_deg+1)]))
        assert U==P([1])
    re=M[0].resultant(M[1],'b')
    assert re.degrees()[1]==0
    dic=re.to_dict()
    univ=P([dic.get((i,0),0) for i in range(re.degrees()[0]+1)])
    fac=sorted((t.degree(),m) for t,m in univ.factor()[1])
    assert univ.degree()==176
    assert fac==[(1,8),(2,2),(2,2),(8,1),(8,1),(8,9),(12,1),(60,1)]
    print('compact diagonal pole: two exact (10,9) conditions with b-coefficient gcd 1')
    print('resultant degree 176; irreducible degrees/powers',fac)

if __name__=='__main__':
    compact_pole()
    q=sample(F(1,5),F(2,5))
    assert q is not None
    print('all scoped neighboring singleton reductions replayed (not a full branch exclusion)')
