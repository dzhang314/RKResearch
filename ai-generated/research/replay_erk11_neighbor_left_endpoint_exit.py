#!/usr/bin/env python3
"""Exact sole-left-endpoint ERK11 exit. Requires python-flint 0.9.0 and SymPy 1.14.0."""
from itertools import combinations
import flint
F=flint.fmpq
P=flint.fmpq_poly
C=flint.fmpq_mpoly_ctx.get(('a','b','s'))
a,b,s=C.gens()
zero=C.from_dict({})
one=C.from_dict({(0,0,0):1})
d=1-b; Y=1-s
W=s*s*(s-a)**2
V=(1-s)**2*(s-d)**2
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def dot(l,r):return 210*sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
def prim(f):return C.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in f.to_dict().items()})
def it(f,shift=0):
 o={}
 for (i,j,k),c in f.to_dict().items():o[(i,j,0)]=o.get((i,j,0),0)+c/(k+shift+1)
 return C.from_dict(o)
def L(t):return [t**(j+1) for j in range(5)]
def R(t):return [(1-t)*t**j for j in range(5)]
def qdiv(p,g):
 q,r=divmod(p,g)
 assert r.is_zero()
 return q
C2d=flint.fmpq_mpoly_ctx.get(('a','b'))
aa,bb=C2d.gens()
one0=C2d.from_dict({(0,0):1})
zero0=C2d.from_dict({})
def dcol(f,k=0):
 return C2d.from_dict({(i,j):v for (i,j,h),v in f.to_dict().items() if h==k})
def fs(poly,u,v,n):
 return sum((dcol(poly,i)*u**i*v**(n-i) for i in range(n+1)),zero0)
def dv(f):
 if f.degrees()[1]!=0:print(f.degrees());assert False
 a0=f.to_dict()
 return P([a0.get((i,0),0) for i in range(f.degrees()[0]+1)])
def rowdot(L,R):return 210*sum((L[i]*N[i][j]*R[j] for i in range(5) for j in range(5)),zero0)
def gcdgeo(f,known):
 for t in known:
  while True:
   h=f.gcd(t)
   if h.total_degree()==0:break
   f=f//h
 return f
def form():
  p=prim(W);q=it(V)-prim(V)
  H=it(p*V); C1=it(p*V,1);C2=it(W*q,1);J=it(p*q)
  I0,I1,I2=[it(W*V,k) for k in range(3)]
  zd=H*I1-C2*I0
  zn=H*I2-C2*I1
  U=C1*zd-H*zn
  S=C2*zd-H*zn
  one=C.from_dict({(0,0,0):1})
  dl=[one,zero,zero,zero,zero];da=[(i+1)*a**i for i in range(5)]
  r1=[one]*5;rd=[d**j-((1-d)*j*d**(j-1) if j else zero) for j in range(5)]
  def dto(l,r):return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
  k00=dto(dl,r1);assert k00==one
  K10=dto(da,r1)
  phi=[u-K10*v for u,v in zip(da,dl)]
  detK=dto(phi,rd)
  g=dto(phi,R(s))
  atd=g.compose(a,b,d)
  hr=qdiv(b**5*g-30*atd*q,(1-s)**2)
  gr=qdiv(hr,s-d)
  gAtd=gr.compose(a,b,d)
  hh=qdiv(gr-gAtd,s-d)
  assert hh.degrees()[2]<=1
  h0,h1=[dcol(hh,k) for k in range(2)]
  Z=dcol(zd)*h0+dcol(zn)*h1
  Aux=30*dcol(atd)*dcol(J*zd)+h1*dcol(U)
  poly=[dcol(detK),Z,Aux]
  names=['a','b','a-d','H','J','zD','U','s-z','s-1','s-0','s-a','s-d','z-a','z-d']
  guards=list(map(dcol,[a,b,a-d,H,J,zd,U,S,H-C2,C2,C2-a*H,C2-d*H,zn-a*zd,zn-d*zd]))
  return poly,guards,names

qp=flint.fmpq_poly

def monic(f):
    return f/f[f.degree()]

def number_field(F):
    F=monic(F)
    qone=qp([1])
    qzero=qp()
    def trim(xs):
        while xs and xs[-1].is_zero():
            xs.pop()
        return xs
    def inv(x):
        r,s=F,x
        y,z=qzero,qone
        while not s.is_zero():
            h,v=divmod(r,s)
            r,s=s,v
            y,z=z,(y-h*z)%F
        assert r.degree()==0 and r[0]!=0
        return (y/r[0])%F
    def rem(f,g):
        out=f[:]
        i=inv(g[-1])
        while len(out)>=len(g):
            shift=len(out)-len(g)
            c=(out.pop()*i)%F
            for j in range(len(g)-1):
                out[shift+j]=(out[shift+j]-c*g[j])%F
            trim(out)
        return out
    def gcd(f,g):
        while g:
            f,g=g,rem(f,g)
        assert f
        c=inv(f[-1])
        return [(x*c)%F for x in f]
    def from_biv(f):
        c=f.to_dict()
        na,nd=f.degrees()
        return trim([qp([c.get((i,j),0) for i in range(na+1)])%F for j in range(nd+1)])
    def at_biv(f,v):
        z=qzero
        for u in reversed(from_biv(f)):
            z=(z*v+u)%F
        return z
    return from_biv,at_biv,gcd

def setup(C,a,b):
 x=C.gen();y=1-x;zero=C([0])[0];one=C([1])[0];d=1-b
 w=x*x*(x-a)**2;V=y*y*(x-d)**2
 def int_(r,k=0):return sum((r[i]/(i+k+1) for i in range(len(r))),zero)
 def primitive(p):return C([zero]+[p[i]/(i+1) for i in range(len(p))])
 P=primitive(w);Q=int_(V)-primitive(V)
 H=int_(P*V);C1=int_(P*V,1);C2=int_(w*Q,1);J=int_(P*Q)
 I0,I1,I2=[int_(w*V,i) for i in range(3)]
 s=C2/H;z=(I2-s*I1)/(I1-s*I0)
 A=s*(s-a);B=(1-s)*(s-d)
 vv=J*B*(s-z)/(C1-z*H)
 L0=[(s**(i+1)-P(s)/P(a)*a**(i+1))/A for i in range(5)]
 L1=[a**(i+1)/P(a) for i in range(5)]
 R0=[((1-s)*s**i-Q(s)/Q(d)*(1-d)*d**i)/B+vv*(1-d)*d**i/Q(d) for i in range(5)]
 D0=[one,zero,zero,zero,zero];Da=[(i+1)*a**i for i in range(5)]
 E0=[one]*5;Ed=[d**i-((1-d)*i*d**(i-1) if i else zero) for i in range(5)]
 def dt(l,r):return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
 S=[(dt(l,e0),dt(l,e1)) for l in (L0,L1) for e0,e1 in [(E0,Ed)]]
 K=[(dt(l,E0),dt(l,Ed)) for l in (D0,Da)]
 return (a,b,d,s,z,vv,J,L0,L1,R0,D0,Da,E0,Ed,S,K,H,I0,I1,I2),dt
def det3(A):
 x,y,z=A
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])

def residue(p,a0,b0):
    C=flint.fmpz_mod_poly_ctx(p)
    r=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    a=C([a0])[0]
    b=C([b0])[0]
    z=C([0])[0]
    def ev(f):
        return sum((r(c)*a**i*b**j for (i,j),c in f.to_dict().items()),z)
    def spec(f):
        v=[z]*(f.degrees()[1]+1)
        for (i,j),c in f.to_dict().items():v[j]+=r(c)*a**i
        return C(v)
    return C,a,b,r,ev,spec

def measure(C,a,b):
    data,dot=setup(C,a,b)
    a,b,d,s,z,v,J,L0,L1,R0,D0,Da,E0,Ed,*_=data
    beta=210*dot(L1,R0)-v/J
    assert beta!=0
    u=-210*dot(L0,R0)/beta
    assert u!=0
    L=[r+u*t for r,t in zip(L0,L1)]
    return (data,dot,beta,u,L)

def full_fit(C,w,c,x0,sc,vr,side,J,v,u,D0,Da,E0,Ed,f):
   if side:
     l0,l1=f(D0,vr),f(Da,vr)
   else:
     l0,l1=f(vr,E0),f(vr,Ed)
   if l0==0:return ('slope',)
   X=C.gen();Y=1-X;z=C([0])[0]
   if side:
      es=C([0]+[sum((N[i][j]*vr[j] for j in range(5)),z) for i in range(5)])
   else:
      es=sum((sum((vr[i]*N[i][j] for i in range(5)),z)*X*Y**j for j in range(5)),C([]))
   h=w/2;phi=X*X*(w-X)
   B0=X*(X-w)*(X-h);B1=(X-h)*(w*l0-(l0-l1)*X)
   E,R=divmod(w**5*es-X**3*(6*X**2-15*w*X+10*w*w)*es(w),X*(X-w));assert R.is_zero()
   S0=-w*E[0]*(X-w)*(X-h)
   S1,R=divmod(w*(E*B1(0)-E[0]*B1),X);assert R.is_zero()
   Cc=[phi,X*B0,X*B1,B0,B1]
   wt=X*Y*(X-w)*(X-c)
   def it(p,j):return sum((p[i]/(i+j+1) for i in range(len(p))),z)
   rho=J/(u*v)
   M=[[it(wt*p,j)-rho*sc**j*p(sc) for p in Cc] for j in range(3)]
   det=det3([v[:3] for v in M])
   vv=[[-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in M]) for i in range(3)]
       for j in (3,4)]
   Oo=[w*x0*(x0-w)*E[0],x0*S0(x0),x0*S1(x0),S0(x0),S1(x0)]
   g0,g1=[sum((u*v for u,v in zip(col,Oo[:3])),z)+det*Oo[3+i] for i,col in enumerate(vv)]
   if g1==0:return ('affine',)
   t=-g0/g1
   if t==0:return ('t=0',)
   js=None
   for jj in combinations(range(4),3):
       rows=[(M+[Oo])[i] for i in jj]
       deti=det3([r[:3] for r in rows])
       if deti!=0:
           js=jj
           break
   if js is None:return ('rank',)
   U,W,T=[-det3([[r[k] if k!=i else r[3]+t*r[4] for k in range(3)] for r in rows])/deti for i in range(3)]
   assert all(r[0]*U+r[1]*W+r[2]*T+r[3]+t*r[4]==0 for r in M+[Oo])
   P=w*(U+(X-h)*(T-t*W)/t)
   Q=U*phi+W*X*B0+T*X*B1+B0+t*B1
   return 'fit',P,Q,t,(l0,l1,det,g0,g1),js

def place(F,K,Q,guards,p,a0,b0):
    C,a,b,red,evalw,spec=residue(p,a0,b0)
    h=C([red(c) for c in monic(F).coeffs()])
    assert h.degree()==F.degree() and h(a)==0 and h.derivative()(a)!=0
    kk=spec(K)
    assert kk.degree()==3
    g=kk.gcd(spec(Q))
    assert g.degree()==1 and -g[0]/g[1]==b
    assert all(evalw(w)!=0 for w in guards)
    return C,a,b

def det4(M):
  O=M[3]
  return sum(((-1)**(3+j)*O[j]*det3([[row[k] for k in range(4) if k!=j] for row in M[:3]]) for j in range(4)),zero)
def toC(f):return C.from_dict({(i,j,0):t for (i,j),t in f.to_dict().items()})
def width_rows():
 p=prim(W);q=it(V)-prim(V)
 H=it(p*V);C1=it(p*V,1);C2=it(W*q,1);J=it(p*q)
 I0,I1,I2=[it(W*V,k) for k in range(3)]
 Hd,Cl,Cr,Jd,I0d,I1d,I2d=map(dcol,(H,C1,C2,J,I0,I1,I2))
 zD=Hd*I1d-Cr*I0d;zN=Hd*I2d-Cr*I1d
 U=Cl*zD-Hd*zN;S=Cr*zD-Hd*zN
 BN=(Hd-Cr)*(Cr-(1-bb)*Hd)
 Rhat=[U*fs(qdiv(b**5*f-30*q*g,(1-s)*(s-d)),Cr,Hd,3)+30*Jd*BN*S*dcol(g) for f,g in zip(R(s),R(d))]
 Lhat=[fs(qdiv(a**5*f-30*p*g,s*(s-a)),Cr,Hd,3) for f,g in zip(L(s),L(a))]
 la=[dcol(g) for g in L(a)]
 beta=30*rowdot(la,Rhat)-aa**5*bb**5*BN*S
 alpha=rowdot(Lhat,Rhat)
 L9=[beta*v-30*alpha*w for v,w in zip(Lhat,la)]
 Rs,guards,_=form()
 K=gcdgeo(Rs[0],guards)
 return p,q,Hd,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,guards+[BN,alpha,beta],zD,zN
def A_polys(R):
    ngh=R.degrees()[1]
    tab=[{} for _ in range(ngh+1)]
    for (i,j),c in R.to_dict().items():tab[j][i]=c
    return [qp([row.get(i,0) for i in range(max(row,default=-1)+1)]) for row in tab]

def compact_spec(f,p,a):
    xs=A_polys(f)
    r=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    C=flint.fmpz_mod_poly_ctx(p)
    return C([C([r(c) for c in f.coeffs()])(a) for f in xs])

from itertools import count, permutations
from math import gcd,lcm
from time import monotonic
import sympy as sy

def laws():
    p,q,Hd,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,guards,zD,zN=width_rows()
    ld=[one0,zero0,zero0,zero0,zero0];la=[(i+1)*aa**i for i in range(5)]
    ll0,ll1=rowdot(ld,Rhat),rowdot(la,Rhat)
    gg=ll0.gcd(ll1);ll0,ll1=ll0//gg,ll1//gg
    L7=[ll0*x-ll1*y for x,y in zip(la,ld)]
    G=L7[0]
    for x in L7[1:]:G=G.gcd(x)
    L7=[x//G for x in L7]
    rrD=[dcol(d**i-((1-d)*i*d**(i-1) if i else zero)) for i in range(5)]
    rr0,rr1=rowdot(L7,[one0]*5),rowdot(L7,rrD)
    def eL():
        return sum((toC(Rhat[j])*N[i][j]*s**(i+1) for i in range(5) for j in range(5)),zero)
    def eR(L):
        return sum((toC(L[i])*N[i][j]*s*(1-s)**j for i in range(5) for j in range(5)),zero)
    el=eL()
    er0=eR(L9)
    er=eR(L7)
    ql=qdiv(el-el.compose(a,b,a),s-a)
    qr=qdiv(er0-er0.compose(a,b,b),s-b)
    def primitive(w,e):
       P=prim(s**2*(s-w)**2)
       return qdiv(w**5*e-30*P*e.compose(a,b,w),s*(s-w))
    def slope(e,w):
       f=e.derivative(2)
       return toC(dcol(f)),f.compose(a,b,w)
    def jt(w,E,QL,l0,l1):
       ql0=toC(dcol(QL));qla=QL.compose(a,b,w)
       return qdiv(E*((w-s)*l1*ql0-s*l0*qla)-w*l1*toC(dcol(E))*QL,s)
    JL=jt(a,primitive(a,el),qr.compose(a,b,1-s),*slope(el,a))
    JR=jt(b,primitive(b,er),ql.compose(a,b,1-s),*slope(er,b))
    assert JL.degrees()[2]<=3 and JR.degrees()[2]<=3
    G=guards+[K,ll0,ll1,rr0,rr1]
    out=[fs(p,aa0,bb0,3) for p,aa0,bb0 in [(JR,zD-zN,zD),(JL,Cr,Hd)]]
    reduced=[gcdgeo(F,G) for F in out]
    E0=rowdot([dcol(g) for g in L(a)],Rhat)
    E1=rowdot(L9,[dcol(g) for g in R(d)])
    ends=[gcdgeo(F,G) for F in [E0,E1]]
    print('opposite temporal laws raw/deflated',[t.degrees() for t in out],[t.degrees() for t in reduced],flush=True)
    return ends,reduced,G,ql,qr

def inv_shape(C,w,l,Qt):
  X=C.gen();h=w/2
  l0,l1=l
  L=w*l0-(l0-l1)*X
  phi=X*X*(w-X)
  Uf=Qt(h)/phi(h)
  G,rem=divmod(Qt-Uf*phi,X-h);assert rem.is_zero()
  Bf=G[0]/L[0]
  Tf=(G(w)/L(w)-Bf)/w
  Cq,r=divmod(G-(Tf*X+Bf)*L,X*(X-w));assert r.is_zero()
  Af,Wf=Cq[0],Cq[1]
  assert Cq.degree()<=1
  return Uf,Wf,Tf,Af,Bf

def interpret(C,w,c):
  Uf,Wf,Tf,Af,Bf=c
  if Af==0 or Bf==0:return None
  t=Bf/Af
  P=w*(Uf+(C.gen()-w/2)*(Tf/t-Wf))
  if P.is_zero():return None
  return t,P

def primitive_dict(R):
   D=R.to_dict()
   dd=lcm(*(int(v.denominator) for v in D.values()))
   zz={k:int(v.numerator)*(dd//int(v.denominator)) for k,v in D.items()}
   g=gcd(*[abs(c) for c in zz.values()])
   return {k:v//g for k,v in zz.items()}

def modular_resultant(AA,BB,p,md,nd):
    C=flint.nmod_mpoly_ctx.get(('a','b'),modulus=p)
    A=C.from_dict({k:c%p for k,c in AA.items()})
    B=C.from_dict({k:c%p for k,c in BB.items()})
    if A.degrees()[1]!=md or B.degrees()[1]!=nd:return None
    R=A.resultant(B,'b')
    assert R.is_zero() or R.degrees()[1]==0
    return R

def reconstruct(A,B,progress=True):
    Aa,Bb=primitive_dict(A),primitive_dict(B)
    m,n=A.degrees()[1],B.degrees()[1]
    bound=sum(abs(v) for v in Aa.values())**n*sum(abs(v) for v in Bb.values())**m
    degree=A.degrees()[0]*n+B.degrees()[0]*m
    M=1
    coeffs=[0]*(degree+1)
    ts=monotonic();used=0
    for p in count((1<<60)+39,2):
        if not flint.fmpz(p).is_prime():continue
        r=modular_resultant(Aa,Bb,p,m,n)
        if r is None:continue
        s=r.to_dict()
        inv=pow(M,-1,p)
        coeffs=[a+M*((s.get((i,0),0)-a)*inv%p) for i,a in enumerate(coeffs)]
        M*=p;used+=1
        if progress and (used%20==0 or M>2*bound):
            print('CRT primes',used,'bits',M.bit_length(),'limit',bound.bit_length(),'wall',monotonic()-ts,flush=True)
        if M>2*bound:break
    out=[x-M if 2*x>M else x for x in coeffs]
    assert all(abs(x)<=bound for x in out)
    return flint.fmpz_poly(out)

def ep_eta():
    p,q,H,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,G,zD,zN=width_rows()
    j=dcol(it(p*q))
    D=H-Cr
    pp=H*H*D**3*(6*D*D-15*bb*D*H+10*bb*bb*H*H)
    E=j*BN**2*S-U*pp/30 # r9=J BN²S/H⁵U, reflected primitive homogeneous degree5
    # Correct homogeneous primitive without extra H².
    E=j*BN**2*S-U*D**3*(6*D*D-15*bb*D*H+10*bb*bb*H*H)/30
    return gcdgeo(E,G+[K])

def lowdeg():
 pp,qq,H,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,G,zD,zN=width_rows()
 j3=-1+9*s-21*s*s+14*s**3
 assert all(it(s*(1-s)*j3,k).is_zero() for k in range(3))
 Z=qp([0,1]);M=Z*Z-21
 roots=[qp([F(1,2)]),qp([F(1,2),F(1,14)]),qp([F(1,2),F(-1,14)])]
 def ev(q,a,b):
  r=qp()
  for (i,j),c in q.to_dict().items():r=(r+c*powq(a,i)*powq(b,j))%M
  return r
 def powq(a,k):
  r=qp([1])
  for _ in range(k):r=(r*a)%M
  return r
 V=[]
 for i,j,k in permutations(range(3)):
  av,dv0,sv=(roots[ix] for ix in (i,j,k))
  w=(ev(Cr,av,1-dv0)-sv*ev(H,av,1-dv0))%M
  assert not w.is_zero()
  V.append((i,j,k,w))
 print('six simple Jacobi root allocations: all exact C2−sH nonzero',flush=True)
 for v in V:print(v,flush=True)

def shape(C,a,b):
  data,dp,beta,u,Ls=measure(C,a,b)
  a,b,d,s,z,v,J,_,_,Rs,D0,Da,E0,Ed,*_=data
  X=C.gen();Y=1-X;z0=C([0])[0]
  Bs=(1-s)*(s-d)
  ef=C([z0]+[210*Bs*sum((N[i][j]*Rs[j] for j in range(5)),z0) for i in range(5)])
  if ef(a)!=0:return ('E0 normalization',)
  q,rem=divmod(ef,X-a)
  assert rem.is_zero() and q(0)==0
  if q[1]==0 or q(1)==0 or q(s)==0 or q(z)==0:return ('Q read',)
  if q.degree()!=4:return ('Q degree',q.degree())
  l0,l1=dp(D0,Rs),dp(Da,Rs)
  L7=[l0*t-l1*r for r,t in zip(D0,Da)]
  r0,r1=dp(L7,E0),dp(L7,Ed)
  if any(c==0 for c in (l0,l1,r0,r1)):return ('slopes',)
  VL=inv_shape(C,a,(l0,l1),q)
  VR=inv_shape(C,b,(r0,r1),q(Y))
  if VL[3]!=0 or VL[4]!=0:return ('left A/B',)
  ir=interpret(C,b,VR)
  if ir is None:return ('right t/P pivot',)
  tr,Pr=ir
  h=a/2;fc=a*a/8
  Pr=Pr(Y)
  if Pr(h)==0 or q(h)==0:return ('half calibration',)
  P=Pr*q(h)/(fc*Pr(h))
  dl=P[1]/a+VL[1]
  if dl==0 or VL[2]==0:return ('left t pivot',)
  tl=VL[2]/dl
  assert P(h)==a*VL[0] and tl!=0
  B1=(X-h)*(a*l0-(l0-l1)*X)
  BL=(X-h)*X*(X-a)+tl*B1
  h=b/2
  BR=(X-h)*(X*(X-b)+tr*(b*r0-(r0-r1)*X))
  return ('shape',P,q,BL,BR,(a,b,d,s,z,u,v,J,tl,tr))

def compact(C,a,b):
    ss=shape(C,a,b)
    if ss[0]!='shape':return ss
    _,P,Q,BL,BR,vals=ss
    a,b,d,s,z,u,v,J,tl,tr=vals
    X=C.gen();Y=1-X;z0=C([0])[0]
    D=-BL*BR(Y)*(X-s)*(X-z)
    r=Q//X
    assert r.degree()==3 and (Q%X).is_zero()
    rho=J/(u*v)
    assert rho*Q(s)==s*(1-s)*(s-d)
    rr=Bs_v=(1-s)*(s-d)*v
    Pr=lambda y:y**3*(6*y**2-15*b*y+10*b*b)/30
    eta=(rr-Pr(1-s))/Pr(b)
    Om=X*(X-1)*(X-a)*(X-d)
    # Use R=X(X−1)(X−d)k_L to avoid any (X−a) quotient.
    R=Om*Q
    M=C([sum((R[i]/(i-j) for i in range(j+1,R.degree()+1)),z0) for j in range(R.degree())])
    assert M[0]==-(1-s)*(s-d)
    assert M(d)==-s*(1-s)-eta*b*d
    hom=lambda g,k:sum((g[i]*(-P[0])**i*P[1]**(k-i) for i in range(k+1)),z0)
    DD=hom(D,8);LL=-hom(Q,4)**2
    ep=1-b/2
    if DD==0 or LL==0 or P(ep)==0 or d==0 or eta==0:return ('right anchor units',)
    fd=-4*Q(ep)/P(ep)
    p,q=P(d),Q(d)
    delta=q-fd*p
    if any(c==0 for c in [fd,p,delta]):return ('plateau normalization',)
    U=-eta*fd*(DD*q*delta+LL*D(d))
    V=LL*p*delta
    assert V!=0
    AA=D*M-rho*Q(s)*(D//(X-s))
    assert AA[0]==0
    AA=AA//X
    BB=P*P*(X-1)
    if BB.gcd(r).degree()!=0:return ('ghost inverse guard',)
    rem=(V*AA-U*BB)%r
    return 'mark',list(map(int,rem.coeffs())),list(map(int,[U,V,eta,DD,LL,fd,p,q,tl,tr])),[list(map(int,t.coeffs())) for t in (P,Q,BL,BR)]

def new_guard_rows(q):
 p,pR,H,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,gr,zD,zN=width_rows()
 dl=[one0,zero0,zero0,zero0,zero0];da=[(i+1)*aa**i for i in range(5)]
 l0,l1=rowdot(dl,Rhat),rowdot(da,Rhat)
 gg=l0.gcd(l1);l0,l1=l0//gg,l1//gg
 L7=[l0*x-l1*y for x,y in zip(da,dl)]
 g=L7[0]
 for x in L7[1:]:g=g.gcd(x)
 L7=[x//g for x in L7]
 r0=rowdot(L7,[one0]*5)
 r1=rowdot(L7,[dcol(d**i-((1-d)*i*d**(i-1) if i else zero)) for i in range(5)])
 bases=gr+[K,l0,l1,r0,r1]
 at=lambda x:dcol(q.compose(a,b,x))
 qe,qd,q1,qh=map(at,[1-b/2,d,one,a/2])
 q4,q3=dcol(q,4),dcol(q,3)
 qs=fs(q,Cr,H,4)
 qz=fs(q,zN,zD,4)
 i0=bb**3*r0*r1
 At=i0*(-q3+(3*bb/2-4)*q4)+8*r0*r1*qe+2*(r0-r1)*(r0*qd+r1*q1)
 Bt=-2*bb*r1*q1
 Ut=8*r0*r1*qe
 Tt=2*(r0*qd+r1*q1)
 Wt=i0*q4
 Ht=Bt*Ut+(Tt*At-Bt*Wt)*(1-aa/2-bb/2)
 RR1=Tt*At-Bt*Wt
 RR0=Bt*Ut-bb/2*RR1
 pp00=(RR0+RR1)//RR0.gcd(RR1)
 extras={
    'eta':ep_eta(),
    'a-1':aa-1, 'b-1':bb-1,
    'Q1':q1,'Qh':qh,'Qe':qe,'Qs':qs,'Qz':qz,'Qprime0':dcol(q,1),
    'A_R':At,'P_R_at_left_half':Ht,'P0':pp00,
 }
 return {k:gcdgeo(v,bases) for k,v in extras.items()}

def v_fmt(f,m):return f'{f.degree()}^{m}'

def guards_simple(G):
 names=['a','b','a-d','H','J','zD','U','S','1-s','s','s-a','s-d','z-a','z-d','BN','alpha','beta','K','l0','l1','r0','r1']
 return dict(zip(names,G))

def linear_fibers(A,B,G,fac):
    cs=[(8,2,'b',17,14,0),(8,3,'H',19,12,9),
        (12,3,'zD',23,20,5),(12,3,'U',29,28,23),
        (12,4,'J',17,3,2),(20,3,'s-d',41,26,31)]
    passed=[]
    for dg,m,key,p,aa,bb in cs:
       r=dv(A.resultant(G[key],'b'))
       cc=[]
       C,a,b,red,ev,spec=residue(p,aa,bb)
       AA,BB,GG=map(spec,(A,B,G[key]))
       h,j=AA.gcd(BB),AA.gcd(GG)
       print('small guard b competitor',dg,m,key,h,j,'der',AA.derivative()(b),flush=True)
       for F,n in fac:
         if F.degree()!=dg or n!=m or not (r%F).is_zero():continue
         f=C([red(q) for q in monic(F).coeffs()])
         if f.degree()!=dg or f(a)!=0 or f.derivative()(a)==0:continue
         cc.append(F)
       print('width guard candidates count',len(cc),flush=True)
       if len(cc)==1 and AA.degree()==14 and h==j==C([-bb,1]) and AA.derivative()(b)!=0:
          passed.append(cc[0])
          print('EXACT guard exit',dg,m,key,(p,aa,bb),r.degree(),flush=True)
    return passed

def wide_fiber(A,B,H,fac):
    ff=next(u for u,m in fac if (u.degree(),m)==(8,56))
    F=monic(ff)
    ax,bx=sy.symbols('a b')
    def sym(f):
        return sy.Poly.from_dict({(i,j):sy.Rational(int(q.numerator),int(q.denominator))
                   for (i,j),q in f.to_dict().items()},ax,bx,domain='QQ').as_expr()
    def toq(f):
        return qp([flint.fmpq(int(q.p),int(q.q)) for q in sy.Poly(f,ax).all_coeffs()[::-1]])
    S=sy.subresultants(sym(A),sym(H),bx)
    sub=next(x for x in S if sy.degree(x,bx)==1)
    L,M=[toq(x)%F for x in sy.Poly(sub,bx).all_coeffs()]
    g,y,z=L.xgcd(F);assert g==qp([1])
    b0=(-M*y)%F
    bf,ev,gcd=number_field(ff)
    assert ev(A,b0).is_zero() and ev(H,b0).is_zero()
    def div_lin(rows):
        cc=rows[:];out=[]
        for k in range(len(cc)-1,0,-1):
            t=cc.pop()
            out.append(t)
            cc[-1]=(cc[-1]+t*b0)%F
        assert len(cc)==1
        return out[::-1],cc[0]
    sat=bf(A)
    k=0
    while len(sat)>1:
        p,r=div_lin(sat)
        if not r.is_zero():break
        sat=p
        k+=1
    print('wide exact H-zero b-root',b0,'multiplicity in A',k,flush=True)
    for p,aa,bb in [(19,13,14),(37,13,3),(37,33,7)]:
        C,a,b,red,ev,spec=residue(p,aa,bb)
        def r(q):return C([red(c) for c in q.coeffs()])(a)
        f=C([red(t) for t in F.coeffs()])
        assert f.degree()==8 and f(a)==0 and f.derivative()(a)!=0
        assert r(b0)==b
        AA=C([r(c) for c in sat])
        BB=spec(B)
        g=AA.gcd(BB)
        print('wide after exact removed guard fiber',p,aa,bb,AA.degree(),g,flush=True)
        if AA.degree()==len(sat)-1 and g.degree()==0:
            print('EXACT octic^56 full b fiber closed by removing H-zero factors before reduction',flush=True)
            return True
    return False

def leading_review(A,B):
    for aa0,bb0 in [(1,None),(None,1)]:
        def axis(P):
            if aa0 is None:
                return sum(A_polys(P),qp())
            D=P.to_dict()
            return qp([sum((c for (i,j),c in D.items() if j==k),F(0))
                       for k in range(P.degrees()[1]+1)])
        assert axis(A).gcd(axis(B))==qp([1])
    print('a=1 and d=0 exact univariate joint gcd 1',flush=True)
    LC=A_polys(A)[-1]
    factors=LC.factor()[1]
    assert sorted((f.degree(),m) for f,m in factors)==[(2,2),(4,1),(8,1)]
    for f,m in factors:
        if f.degree()==2:
            assert monic(f)==monic(qp([2,-9,12])) and f[1]**2-4*f[0]*f[2]<0
            continue
        p,aa,bd=(19,15,44) if f.degree()==4 else (17,10,43)
        bf,ev,gcd=number_field(f)
        assert (len(bf(A))-1,len(bf(B))-1)==(13,bd)
        C,a,b,red,ev,spec=residue(p,aa,0)
        Fa=C([red(z) for z in monic(f).coeffs()])
        assert Fa.degree()==f.degree() and Fa(a)==0 and Fa.derivative()(a)!=0
        AA,BB=map(spec,(A,B))
        assert AA.degree()==13 and AA.gcd(BB).degree()==0
        print('leading loss finite field degree',f.degree(),'at',(p,aa),
              'exact b-degrees',(13,bd),'whole residue gcd 1',flush=True)
    return LC

def place(F,A,B,p,aa,bb):
    C,a,b,red,ev,spec=residue(p,aa,bb)
    fa=C([red(v) for v in monic(F).coeffs()])
    sa,sb=[spec(w) for w in (A,B)]
    assert fa.degree()==F.degree() and fa(a)==0 and fa.derivative()(a)!=0 and sa.degree()==14
    assert sa.gcd(sb)==C([-bb,1])
    return C,a,b,ev,spec,sa

def replay():
    E,T,G,q,_=laws()
    A,B=E[0],T[0]
    assert A.degrees()==(16,14) and B.degrees()==(48,44)
    LC=leading_review(A,B)
    lowdeg()
    R=reconstruct(A,B)
    assert R.degree()==1294
    R0=R//R.content()
    fac=[(qp(f.coeffs()),m) for u,m in R0.factor_squarefree()[1] for f,k in u.factor()[1] if k==1]
    assert sum(f.degree()*m for f,m in fac)==R.degree()
    assert sorted((g.degree(),m) for g,m in fac)==[
        (1,24),(2,8),(2,16),(8,1),(8,2),(8,3),(8,56),(12,3),(12,3),(12,4),(20,3),(258,1),(288,1)]
    print('exact width resultant degree',R.degree(),'irreducibles',
          sorted((g.degree(),m) for g,m in fac),flush=True)
    outs=[]
    for f,m in fac:
        if f.degree()==1:
            assert monic(f)==qp([0,1])
        elif f.degree()==2:
            assert f[1]**2-4*f[0]*f[2]<0
        elif (LC%f).is_zero():
            assert (f.degree(),m)==(8,1)
        else:
            continue
        outs.append(f)
    gs=guards_simple(G)
    small=linear_fibers(A,B,gs,fac)
    assert len(small)==6
    outs+=small
    assert wide_fiber(A,B,gs['H'],fac)
    outs.append(next(f for f,m in fac if (f.degree(),m)==(8,56)))

    # The degree-258 projection is an exact forbidden physical P(0) guard.
    F258=next(f for f,m in fac if f.degree()==258)
    gg=new_guard_rows(q)['P0']
    assert gg.degrees()==(68,67)
    C,a,b,ev,spec,sa=place(F258,A,B,41,10,28)
    assert sa.gcd(spec(gg))==C([-28,1]) and sa.derivative()(b)==35
    gR=reconstruct(A,gg)
    fR=qp(gR.coeffs())
    assert fR.degree()==1864 and (fR%F258).is_zero()
    outs.append(F258)
    print('degree258 guard norm degree 1864; entire common simple b branch forces exact P(0)=0',flush=True)

    F288=next(f for f,m in fac if f.degree()==288)
    C,a,b,ev,spec,sa=place(F288,A,B,47,12,9)
    assert all(ev(g)!=0 for g in G)
    hit=compact(C,a,b)
    assert hit[0]=='mark' and hit[1:]==(
        [7,31,30],[7,4,29,13,38,8,37,13,44,5],
        [[46,7],[0,18,38,0,4],[27,35,7,1],[30,3,36,1]])
    print('degree288: (47,12,9) product/residue units; reduced right-plateau ghost mark [7,31,30]',flush=True)
    outs.append(F288)
    assert len(outs)==len(fac) and all(sum(monic(f)==monic(g) for g in outs)==1 for f,m in fac)
    print('sole left Q(0)=0 excluded in the neighboring s=c8 chart; other roots or masks not claimed',flush=True)
if __name__=='__main__':
    replay()
