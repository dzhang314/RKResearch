#!/usr/bin/env python3
"""Exhaustive finite-width mask atlas, neighboring ordered ERK11. Requires python-flint 0.9.0."""
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

def raw_masks(side):
    p,q,Hd,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,guards,zD,zN=width_rows()
    dl=[one0,zero0,zero0,zero0,zero0];da=[(i+1)*aa**i for i in range(5)]
    L0,L1=rowdot(dl,Rhat),rowdot(da,Rhat)
    gl0=L0.gcd(L1)
    L0,L1=L0//gl0,L1//gl0
    actual=[L0*u-L1*v for u,v in zip(da,dl)]
    gL=actual[0]
    for v in actual[1:]:gL=gL.gcd(v)
    actual=[v//gL for v in actual]
    if side:
        w,c,ns,ds=a,d,Cr,Hd
        hull0,hull1=map(toC,(L0,L1))
        e=sum((toC(Rhat[j])*N[i][j]*s**(i+1) for i in range(5) for j in range(5)),zero)
        xx,xd=Cr,Hd
    else:
        w,c,ns,ds=b,1-a,Hd-Cr,Hd
        Ed=[dcol(d**i-((1-d)*i*d**(i-1) if i else zero)) for i in range(5)]
        rs0,rs1=rowdot(actual,[one0]*5),rowdot(actual,Ed)
        gt=rs0.gcd(rs1)
        hull0,hull1=map(toC,(rs0//gt,rs1//gt))
        e=sum((toC(actual[i])*N[i][j]*s*(1-s)**j for i in range(5) for j in range(5)),zero)
        xx,xd=zD-zN,zD
    h=w/2
    P=prim(s*s*(s-w)**2)
    E=qdiv(w**5*e-30*P*e.compose(a,b,w),s*(s-w))
    E0=toC(dcol(E))
    B0=s*(s-w)*(s-h)
    B1=(s-h)*(w*hull0-(hull0-hull1)*s)
    S0=-w*E0*(s-w)*(s-h)
    S1=qdiv(w*(E*toC(dcol(B1))-E0*B1),s)
    cols=[s**2*(w-s),s*B0,s*B1,B0,B1]
    O=[w*s*(s-w)*E0,s*S0,s*S1,S0,S1]
    O=[fs(v,xx,xd,3) for v in O]
    wt=s*(1-s)*(s-w)*(s-c)
    M=[[it(wt*g,j) for g in cols] for j in range(3)]
    def dt(columns):
        Mj=[[r[k] for k in columns] for r in M]
        base=dcol(det3(Mj))
        evals=[cols[k] for k in columns]
        adj=sum((s**j*det3([row if i!=j else evals for i,row in enumerate(Mj)]) for j in range(3)),zero)
        assert adj.degrees()[2]<=6
        return alpha*BN*S*base+U*beta*fs(adj,ns,ds,6)
    D=dt([0,1,2])
    c0,c1=[[ -dt([i if k==j else k for k in range(3)]) for j in range(3)] for i in (3,4)]
    live=guards+[K,L0,L1]+([] if side else [rs0,rs1])
    # A common factor in the whole outer row is live even when the raw affine pivot vanishes.
    go=O[0]
    for z in O[1:]:go=go.gcd(z)
    O=[r//go for r in O]
    g0,g1=[D*O[3+i]+sum((u*v for u,v in zip(cc,O[:3])),zero0) for i,cc in enumerate([c0,c1])]
    return K,live,D,g0,g1

def mat(C,w,c,x0,sc,vr,side,J,v,u,D0,Da,E0,Ed,f):
   if side:
     l0,l1=f(D0,vr),f(Da,vr)
   else:
     l0,l1=f(vr,E0),f(vr,Ed)
   if l0==0 or l1==0:return None
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
   return M+[ [w*x0*(x0-w)*E[0],x0*S0(x0),x0*S1(x0),S0(x0),S1(x0)] ],Cc,(l0,l1)

def cofactors(C,A):
  z=C([0])[0]
  def d4(rows):
    return sum((v*(-1)**j*det3([r[:j]+r[j+1:] for r in rows[1:]]) for j,v in enumerate(rows[0])),z)
  return [(-1)**i*d4([r[:i]+r[i+1:] for r in A]) for i in range(5)]

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

def site(C,a,b,opp):
  data,dp,beta,u,L9=measure(C,a,b)
  a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
  l0,l1=dp(D0,R9),dp(Da,R9)
  L7=[l0*q-l1*p for p,q in zip(D0,Da)]
  l=mat(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
  r=mat(C,b,1-a,1-z,1-s,L7,False,J,v,u,D0,Da,E0,Ed,dp)
  if l is None or r is None:return None
  ls,rs=map(lambda q:cofactors(C,q[0]),[l,r])
  X=C.gen();z=C([0])[0]
  if opp==0:
    if all(t==0 for t in ls):return None
    Q=sum((c*p for c,p in zip(ls,l[1])),C([]))
  else:
    if all(t==0 for t in rs):return None
    Q=sum((c*p(1-X) for c,p in zip(rs,r[1])),C([]))
  if Q(0)==0 or Q(1)==0:return None
  U,V=inv_shape(C,a,l[2],Q),inv_shape(C,b,r[2],Q(1-X))
  # Rank-free raw temporal check in the opposite orientation.
  Ol=sum((c*p for c,p in zip(U,l[0][-1])),z)
  Or=sum((c*p for c,p in zip(V,r[0][-1])),z)
  L,R=interpret(C,a,U),interpret(C,b,V)
  if L is None or R is None:return None
  tl,p=L;tr,q=R
  mark=p[0]*q[1]+p[1]*(q[0]+q[1])
  if not any(j!=0 for j in [Ol,Or,mark]):return None
  def ints(v):return list(map(int,v))
  return [ints(ls),ints(rs),ints(Q.coeffs()),ints(p.coeffs()),ints(q.coeffs()),ints([tl,tr,Ol,Or,mark])]

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

def replay():
    E,T,gr,*_=laws()
    assert [v.degrees() for v in E]==[(16,14),(21,21)]
    assert [v.degrees() for v in T]==[(48,44),(58,55)]
    assert all(f.gcd(g).total_degree()==0 for f,g in zip(E,T))
    print('single endpoint width and actual opposite temporal equations exact bivariate gcd 1 on both sides')
    expected={
      (True,(16,14)):(19,6,18,1,12),
      (True,(36,34)):(17,12,3,0,14),
      (False,(21,21)):(17,14,1,0,9),
      (False,(23,20)):(17,6,8,0,10),
    }
    seen=[]
    for side in (True,False):
      K,G,D,g0,g1=raw_masks(side)
      raw=[p.degrees() for p in [D,g0,g1]]
      D,g0,g1=map(lambda p:gcdgeo(p,G),[D,g0,g1])
      fs=D.factor()[1]
      assert len(fs)==2 and all(m==1 for f,m in fs)
      print('side',side,'raw degrees',raw,'deflated',[p.degrees() for p in [D,g0,g1]],
            'fixed irreducibles',[f.degrees() for f,m in fs],flush=True)
      g=g0.gcd(g1)
      h=E[0 if side else 1]
      assert g.degrees()==h.degrees() and (g%h).is_zero() and (h%g).is_zero()
      assert (D%h).is_zero() and (g0//g).gcd(g1//g).total_degree()==0
      print('shared affine factor exactly own endpoint-width factor; affine residual pair coprime',g.degrees(),flush=True)
      for f,m in fs:
         key=(side,f.degrees())
         p,a0,b0,ch,mark=expected[key]
         C,a,b,r,ev,spec=residue(p,a0,b0)
         assert compact_spec(f,p,a0).degree()>0 and ev(f)==0
         assert all(ev(q)!=0 for q in G)
         q=site(C,a,b,ch)
         assert q is not None and q[-1][2:]==[0,0,mark]
         assert any(q[ch]) and q[2][0]!=0 and sum(q[2])%p!=0
         seen.append(key)
         print('fixed factor',f.degrees(),'at',(p,a0,b0),'cofactor side',ch,
               'physical P mark',mark,'oriented P lines',q[3:5],flush=True)
    assert set(seen)==set(expected) and len(seen)==4
    print('all K-nonzero neighboring fixed/affine masks finite; no stage-count exclusion',flush=True)
if __name__=='__main__':
    replay()
