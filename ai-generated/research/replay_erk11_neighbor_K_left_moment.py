#!/usr/bin/env python3
"""Exact left fixed-moment exit on the neighboring singular derivative chart.
Requires python-flint 0.9.0. No external data or random search.
"""
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

def fit(C,w,c,x0,sc,vr,side,J,v,u,D0,Da,E0,Ed,f):
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
   if det==0:return ('moment',)
   vv=[[-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in M]) for i in range(3)]
       for j in (3,4)]
   Oo=[w*x0*(x0-w)*E[0],x0*S0(x0),x0*S1(x0),S0(x0),S1(x0)]
   g0,g1=[sum((u*v for u,v in zip(col,Oo[:3])),z)+det*Oo[3+i] for i,col in enumerate(vv)]
   if g1==0:return ('affine',)
   t=-g0/g1
   if t==0:return ('t=0',)
   U,W,T=[(c0+t*c1)/det for c0,c1 in zip(*vv)]
   P=w*(U+(X-h)*(T-t*W)/t)
   Q=U*phi+W*X*B0+T*X*B1+B0+t*B1
   BL=B0+t*B1
   if any(g==0 for g in (BL(x0),P(x0),Q(x0),P(h),Q(h))):return ('shape guard',)
   return 'fit',P,Q,t,(l0,l1,det,g0,g1)
def eqs():
    det,guards,names=form()
    K=gcdgeo(det[0],guards)
    p=prim(W);q=it(V)-prim(V)
    H=it(p*V);C1=it(p*V,1);C2=it(W*q,1);J=it(p*q)
    I0,I1,I2=[it(W*V,k) for k in range(3)]
    Hd,Cl,Cr,Jd,i0,i1,i2=map(dcol,(H,C1,C2,J,I0,I1,I2))
    zd=Hd*i1-Cr*i0; zn=Hd*i2-Cr*i1
    U=Cl*zd-Hd*zn
    S=Cr*zd-Hd*zn
    BN=(Hd-Cr)*(Cr-(1-bb)*Hd)
    AN=Cr*(Cr-aa*Hd)
    Ah=s*(s-a);Bh=(1-s)*(s-d)
    Rhat=[U*fs(qdiv(b**5*f-30*q*g,Bh),Cr,Hd,3)+30*Jd*BN*S*dcol(g) for f,g in zip(R(s),R(d))]
    Lhat=[fs(qdiv(a**5*f-30*p*g,Ah),Cr,Hd,3) for f,g in zip(L(s),L(a))]
    la=[dcol(g) for g in L(a)]
    beta=30*rowdot(la,Rhat)-aa**5*bb**5*BN*S
    alpha=rowdot(Lhat,Rhat)
    Tz=zd*zd*i2-2*zn*zd*i1+zn*zn*i0
    gap=U*AN*S
    Z=alpha*Tz+beta*gap
    M=[Tz*t+30*gap*r for t,r in zip(Lhat,la)]
    m0=rowdot(M,[one0]*5)
    Md0=[dcol(d**j-((1-d)*j*d**(j-1) if j else zero)) for j in range(5)]
    m1=rowdot(M,Md0)
    return [K,Z,m0,m1],guards+[Tz],names+['Tz']
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

def project():
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
 l0=rowdot([one0,zero0,zero0,zero0,zero0],Rhat)
 l1=rowdot([(i+1)*aa**i for i in range(5)],Rhat)
 def toC(v):return C.from_dict({(j,k,0):x for (j,k),x in v.to_dict().items()})
 l0=C.from_dict({(0,0,0):1});l1=toC(sum((N[i][j]*(i+1)*aa**i for i in range(5) for j in range(5)),zero0))
 hx=a/2
 B0=s*(s-a)*(s-hx);B1=(s-hx)*(a*l0-(l0-l1)*s)
 cols=[s**2*(a-s),s*B0,s*B1]
 wt=s*(1-s)*(s-a)*(s-d)
 M=[[it(wt*g,j) for g in cols] for j in range(3)]
 base=dcol(det3(M))
 adj=sum((s**j*det3([row if i!=j else cols for i,row in enumerate(M)]) for j in range(3)),zero)
 hAdj=fs(adj,Cr,Hd,6)
 F=alpha*BN*S*base+U*beta*hAdj
 Rs,Guards,_=form()
 K=gcdgeo(Rs[0],Guards)
 P=F
 print('moment raw bideg',P.degrees(),flush=True)
 Q=gcdgeo(P,Guards+[BN,alpha,beta])
 print('deflated bideg',Q.degrees(),'remaining factor shapes',[(g.degrees(),m) for g,m in Q.factor()[1]],flush=True)
 r=dv(K.resultant(Q,'b'))
 print('exact left moment projection on K',r.degree(),[(g.degree(),m) for g,m in r.factor()[1]],flush=True)
 return K,Q,r.factor()[1],Guards+[BN,alpha,beta]
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
   BL=B0+t*B1
   if any(g==0 for g in (BL(x0),P(x0),Q(x0),P(h),Q(h))):return ('shape guard',)
   return 'fit',P,Q,t,(l0,l1,det,g0,g1),js
from itertools import combinations
from math import isqrt
def lost_left(C,a,d,s,R9,P,Q,f0):
  X=C.gen(); z=C([0])[0]; h=a/2
  P=P(1-X); Q=Q(1-X)
  ca=X*X*(a-X)/a
  if any(t==0 for t in (P(h),Q(h),P(s),Q(s))):return None
  Q=Q*(P(h)*ca(h)/Q(h))
  v0=[C([1])[0]]+[z]*4
  va=[(j+1)*a**j for j in range(5)]
  l0,l1=f0(v0,R9),f0(va,R9)
  e0=C([0]+[sum((N[i][j]*R9[j] for j in range(5)),z) for i in range(5)])
  E,r=divmod(a**5*e0-X**3*(6*X**2-15*a*X+10*a*a)*e0(a),X*(X-a));assert r.is_zero()
  B0=X*(X-a)*(X-h)
  B1=(X-h)*(a*l0-(l0-l1)*X)
  S0=-a*E[0]*(X-a)*(X-h)
  S1,r=divmod(a*(E*B1(0)-E[0]*B1),X);assert r.is_zero()
  k0=Q(s)*S0(s)
  k1=P(s)*s*(s-a)*E(s)*B1(0)+Q(s)*S1(s)
  if k1==0:return None
  t=-k0/k1
  B=B0+t*B1
  quo,rr=divmod(Q-P*ca,B)
  return k0,k1,t,rr,P,Q,B,quo
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

def replay():
    K,Q,fac,guards=project()
    assert K.degrees()==(3,3) and Q.degrees()==(40,34)
    assert sorted((f.degree(),n) for f,n in fac)==[(12,2),(12,2),(66,1),(108,1)]
    for F,n in fac:
        if F.degree()==12:
            bf,ev,gcd=number_field(F)
            g=gcd(bf(K),bf(Q))
            assert len(g)==2 and g[1]==qp([1])
            b0=-g[0]
            assert all(ev(w,b0).is_zero() for w in (K,Q))
            assert ev(guards[6],b0).is_zero()
    print('both degree12 branches have exact linear b gcd with live U lost')
    F=next(f for f,m in fac if f.degree()==108)
    C,a,b=place(F,K,Q,guards,19,9,6)
    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
    Lf=full_fit(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
    Rf=full_fit(C,b,1-a,1-z,1-s,L9,False,J,v,u,D0,Da,E0,Ed,dp)
    assert Lf[0]==Rf[0]=='fit' and Lf[4][2]==0 and Rf[4][2]!=0
    assert Lf[5]==(0,1,3) and Rf[5]==(0,1,2)
    l,r=Lf[1],Rf[1]
    mk=l[0]*r[1]+l[1]*(r[0]+r[1])
    assert mk==7
    print('degree108: (19,9,6), actual left temporal row restores rank; first-pool mark 7',
          'left/right lines',list(map(int,l.coeffs())),list(map(int,r.coeffs())))

    F=next(f for f,m in fac if f.degree()==66)
    C,a,b=place(F,K,Q,guards,41,33,22)
    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
    Lf=full_fit(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
    Rf=full_fit(C,b,1-a,1-z,1-s,L9,False,J,v,u,D0,Da,E0,Ed,dp)
    assert Lf[0]=='affine' and Rf[0]=='fit'
    k0,k1,t,rem,P,Q,B,quot=lost_left(C,a,d,s,R9,Rf[1],Rf[2],dp)
    assert (k0,k1,t)==(2,33,31) and list(map(int,rem.coeffs()))==[29,28,18]
    print('degree66: (41,33,22), live right profile and actual original left outer',
          'k0/k1=(2,33), t=31, remainder 18X^2+28X+29')
    print('  right transfer to left P/Q/B/quotient',
          *[list(map(int,q.coeffs())) for q in (P,Q,B,quot)])
    print('left fixed moment loss excluded on K only; other curve masks remain')

if __name__=='__main__':
    replay()
