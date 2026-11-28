#!/usr/bin/env python3
"""Exact nonshared-right temporal rank-loss replay. Requires python-flint 0.9.0."""
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


def nonshared():
    ends,_,G,_,_=laws()
    K,live,D,_,_=raw_masks(False)
    D=gcdgeo(D,live)
    facs=sorted(D.factor()[1],key=lambda q:q[0].degrees())
    assert [(f.degrees(),m) for f,m in facs]==[((21,21),1),((23,20),1)]
    ER,A=[f for f,_ in facs]
    assert ER.gcd(ends[1]).degrees()==(21,21)
    assert all(A.gcd(x).total_degree()==0 for x in ends)
    return A,ends,G

def axis(f,k):
    sums={}
    for (i,j),u in f.to_dict().items():
        n=(j,i,i+j)[k]
        sums[n]=sums.get(n,0)+u
    return qp([sums.get(i,0) for i in range(max(sums,default=-1)+1)])

def good_A(F,p,a0):
    assert flint.fmpz(p).is_prime()
    C,a,b,red,ev,spec=residue(p,a0,0)
    f=C([red(q) for q in monic(F).coeffs()])
    assert f.degree()==F.degree() and f(a)==0 and f.derivative()(a)!=0
    return int(f.derivative()(a))

def projective(p,a0,b0,E,G,p0,p1,mark):
    C,a,b,red,ev,spec=residue(p,a0,b0)
    assert all(ev(g)!=0 for g in E+G)
    q=site(C,a,b,0)
    assert q is not None and any(q[0]) and q[2][0]!=0 and sum(q[2])%p!=0
    assert q[3:5]==[p0,p1] and q[-1][2:]==[0,0,mark] and mark!=0
    return q[3:5]

def verify_axes(A,E,G):
    f0=axis(A,0)
    assert f0.degree()==20
    fs={u.degree():(u,m) for u,m in f0.factor()[1]}
    assert set(fs)=={6,14} and all(m==1 for _,m in fs.values())
    assert (axis(G[19],0)%fs[14][0]).is_zero()
    assert (axis(G[7],0)%fs[6][0]).is_zero()
    print('a=1: exact degree 14 -> left second slope, degree 6 -> s-z')
    f1=axis(A,1)
    (q,m),=f1.factor()[1]
    assert m==1 and f1.degree()==q.degree()==23
    da=good_A(q,17,8)
    print('b=1: degree 23, good place (17,8,1), projectivity',
          projective(17,8,1,E,G,[11,1],[8,16],13),13)
    f2=axis(A,2)
    fs={u.degree():(u,m) for u,m in f2.factor()[1]}
    assert set(fs)=={1,41} and f2.degree()==42
    assert all(m==1 for _,m in fs.values()) and (axis(G[0],2)%fs[1][0]).is_zero()
    da=good_A(fs[41][0],19,7)
    print('a=b: forbidden a=0 and degree 41; good place (19,7,7), projectivity',
          projective(19,7,7,E,G,[1,3],[14,7],13),13)

def divide_monic(R,H,F):
    assert H and H[-1]==qp([1])
    n=len(R)-len(H)
    assert n>=0
    r=R[:]
    out=[qp() for _ in range(n+1)]
    while len(r)>=len(H):
        k=len(r)-len(H)
        q=r.pop()
        out[k]=q
        for j in range(len(H)-1):
            r[j+k]=(r[j+k]-q*H[j])%F
        while r and r[-1].is_zero():r.pop()
    assert not r
    return out

def exhaust(F,A,B,g,expected_degree,expected_steps):
    F=monic(F)
    bf,ev,gcd=number_field(F)
    R=gcd(bf(A),bf(B))
    assert len(R)-1==expected_degree
    steps=[]
    while len(R)>1:
        H=gcd(R,bf(g))
        assert len(H)>1
        steps.append(len(H)-1)
        R=divide_monic(R,H,F)
    assert steps==expected_steps and len(R)==1
    return steps

def whole_place(F,A,B,G,E,p,a0,b0):
    da=good_A(F,p,a0)
    C,a,b,red,ev,spec=residue(p,a0,b0)
    R,S=map(spec,(A,B))
    assert R.degree()==20 and R.gcd(S)==C([-b0,1])
    assert R.derivative()(b)!=0 and all(ev(g)!=0 for g in G+E)
    return C,a,b,da,int(R.derivative()(b))

def right_origin(C,a,b):
    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
    l0,l1=dp(D0,R9),dp(Da,R9)
    L7=[l0*q-l1*p for p,q in zip(D0,Da)]
    assert z==1
    m,cols,pairs=mat(C,b,1-a,1-z,1-s,L7,False,J,v,u,D0,Da,E0,Ed,dp)
    assert m[-1][:3]==[0,0,0] and det3([v[:3] for v in m[:3]])==0
    c=cofactors(C,m)
    assert any(t!=0 for t in c[:3]) and c[3:]==[0,0]
    return list(map(int,m[-1])),list(map(int,c))

def verify_outer(A,E,G):
    *_,zD,zN=width_rows()
    for k,BB in enumerate([zN,zN-zD]):
        B=gcdgeo(BB,G)
        assert B.degrees()==[(4,4),(4,2)][k]
        norm=dv(A.resultant(B,'b'))
        exp=[{1:4,8:6,12:1,104:1},{1:4,4:1,8:6,12:1,56:1}][k]
        facs=norm.factor()[1]
        assert norm.degree()==[168,124][k]
        assert len(facs)==len(exp) and {f.degree():m for f,m in facs}==exp
        allF={f.degree():f for f,m in facs}
        sm=[[(1,0,2,[2]),(8,3,1,[1]),(12,5,1,[1])],
            [(1,0,2,[2]),(4,7,1,[1]),(8,3,2,[1,1]),(12,5,1,[1])]][k]
        print('outer',k,'exact resultant',norm.degree(),exp)
        for dg,gi,gcd_deg,expect_steps in sm:
            steps=exhaust(allF[dg],A,B,G[gi],gcd_deg,expect_steps)
            print('  guard fiber',dg,'gcd degree',gcd_deg,'index',gi,'saturation',steps)
        if k==0:
            C,a,b,da,db=whole_place(allF[104],A,B,G,E,37,7,7)
            assert da!=0 and db!=0
            print('  degree 104: (37,7,7), derivatives',da,db,'projectivity',
                  projective(37,7,7,E,G,[32,12],[17,17],27),27)
        else:
            C,a,b,da,db=whole_place(allF[56],A,B,G,E,23,6,13)
            print('  degree 56: (23,6,13), derivatives',da,db,
                  'actual right temporal row / cofactors',right_origin(C,a,b))


# Temporal-rank-loss receipt, independent of the larger shape-live projection.
from itertools import count
from math import gcd as igcd, lcm as ilcm
from time import monotonic

def primitive_dict(R):
    D=R.to_dict()
    dd=ilcm(*(int(v.denominator) for v in D.values()))
    zz={k:int(v.numerator)*(dd//int(v.denominator)) for k,v in D.items()}
    g=igcd(*[abs(c) for c in zz.values()])
    return {k:v//g for k,v in zz.items()}

def reconstruct(A,B,label):
    Aa,Bb=primitive_dict(A),primitive_dict(B)
    m,n=A.degrees()[1],B.degrees()[1]
    bound=sum(abs(v) for v in Aa.values())**n*sum(abs(v) for v in Bb.values())**m
    degree=A.degrees()[0]*n+B.degrees()[0]*m
    M=1; coeffs=[0]*(degree+1); used=0
    for p in count((1<<60)+39,2):
        if not flint.fmpz(p).is_prime():continue
        K=flint.nmod_mpoly_ctx.get(('a','b'),modulus=p)
        A0=K.from_dict({k:c%p for k,c in Aa.items()})
        B0=K.from_dict({k:c%p for k,c in Bb.items()})
        if A0.degrees()[1]!=m or B0.degrees()[1]!=n:continue
        r=A0.resultant(B0,'b')
        assert r.is_zero() or r.degrees()[1]==0
        dd=r.to_dict();inv=pow(M,-1,p)
        coeffs=[u+M*((dd.get((i,0),0)-u)*inv%p) for i,u in enumerate(coeffs)]
        M*=p;used+=1
        if M>2*bound:break
    c=[u-M if 2*u>M else u for u in coeffs]
    assert all(abs(u)<=bound for u in c)
    out=flint.fmpz_poly(c)
    print(label,'degree',out.degree(),'CRT count',used,'bound bits',bound.bit_length(),
          'modulus bits',M.bit_length(),flush=True)
    return out

def constraints():
    A,E,G=nonshared()
    K,live,D,g0,g1=raw_masks(False)
    rr=[gcdgeo(t,live) for t in (g0,g1)]
    assert all((x%E[1]).is_zero() for x in rr)
    BB=[t//E[1] for t in rr]
    assert [x.degrees() for x in BB]==[(22,22),(34,35)]
    return A,BB,G,E

def pair_of_factors(N):
    fs=N.factor()[1]
    expected={(1,44):1,(3,1):4,(20,1):1,(56,1):1,(60,1):1,(114,1):1,
        (124,1):1,(8,2):2,(12,2):2,(12,3):1,(8,4):1,(2,8):1,(1,14):1,(2,14):1,(8,36):1}
    dd={}
    for f,m in fs:dd.setdefault((f.degree(),m),[]).append(f)
    assert {k:len(v) for k,v in dd.items()}==expected
    def pick(d,m,lc=None):
        ll=dd[d,m]
        if lc is not None:ll=[f for f in ll if int(f[f.degree()])==lc]
        f,=ll
        return f,monic(qp([int(z) for z in f.coeffs()]))
    return pick

def powerset_saturate(Q,guard,F,gcd):
    loops=[]
    while len(Q)>1:
        H=gcd(Q,guard)
        if len(H)==1:break
        loops.append(len(H)-1)
        Q=divide_monic(Q,H,F)
    return Q,loops

def small_exact(F,A,B,C,guard,edegs,gdeg,steps):
    bs,ev,gcd=number_field(F)
    Pol=[bs(f) for f in (A,B,C)]
    assert [len(f)-1 for f in Pol]==edegs
    Z=gcd(gcd(Pol[0],Pol[1]),Pol[2])
    assert len(Z)-1==gdeg
    if guard is not None:Z,actual=powerset_saturate(Z,bs(guard),F,gcd)
    else:actual=[]
    assert actual==steps and len(Z)==1
    print('exact small fiber',F.degree(),'true b degrees',edegs,'gcd degree',gdeg,
          'guard removals',steps,flush=True)

def cf_spec(f,K,z,p):
    def red(c):return int(c.numerator)*pow(int(c.denominator),-1,p)%p
    return K([K([red(c) for c in v.coeffs()])(z) for v in f])

def small_saturated(F,A,B,C,guard,p,a0,deg,removals,key):
    da=good_A(F,p,a0)
    bs,ev,gcd=number_field(F)
    first=bs(A)
    if guard is not None:first,removed=powerset_saturate(first,bs(guard),F,gcd)
    else:removed=[]
    assert removed==removals and len(first)-1==deg
    K=flint.fmpz_mod_poly_ctx(p);a=K([a0])[0]
    X,Y,Z=[cf_spec(x,K,a,p) for x in (first,bs(B),bs(C))]
    assert X.degree()==deg and X.gcd(Y).gcd(Z).degree()==0
    print('saturated fiber',key,'whole unit after',removed,
          'at',p,a0,'simple derivative',da,'b degrees',
          [i.degree() for i in (X,Y,Z)],flush=True)

def large_unit(F,A,B,C,p,a0):
    da=good_A(F,p,a0)
    K,a,b,red,ev,spec=residue(p,a0,0)
    X,Y,Z=map(spec,(A,B,C))
    assert X.degree()==20 and X.gcd(Y).gcd(Z).degree()==0
    print('large empty fiber',F.degree(),p,a0,'simple derivative',da,
          'retained b degrees',[i.degree() for i in (X,Y,Z)],flush=True)

def large_linear(F,A,B,C,p,a0,b0,g=None):
    da=good_A(F,p,a0)
    K,a,b,red,ev,spec=residue(p,a0,b0)
    X,Y,Z=map(spec,(A,B,C))
    root=K([-b0,1])
    assert X.degree()==20 and X.gcd(Y).gcd(Z)==root
    db=int(X.derivative()(b))
    assert db!=0
    if g is not None:assert X.gcd(spec(g))==root
    print('large whole simple width',F.degree(),p,a0,b0,'derivatives',da,db,
          'b degrees',[i.degree() for i in (X,Y,Z)],flush=True)
    return K,a,b,ev

def replay_temporal(secondary=False):
    A,(B,C),G,E=constraints()
    N=reconstruct(A,B,'first affine norm')
    assert N.degree()==924
    get=pair_of_factors(N)
    assert list(get(1,44)[0].coeffs())==[0,1] and list(get(1,14)[0].coeffs())==[-1,1]
    ax=axis(A,0);ff={t.degree():t for t,m in ax.factor()[1] if m==1}
    assert ax.degree()==20 and set(ff)=={6,14}
    assert (axis(G[19],0)%ff[14]).is_zero() and (axis(G[7],0)%ff[6]).is_zero()
    print('a=0 and a=1 excluded by exact width guards',flush=True)
    for coeffs,lead,gdeg in [([-2,21,-56,42],42,0),([-1,12,-36,30],30,0),
                            ([-3,39,-125,110],110,1),([-4,54,-180,165],165,1)]:
        raw,F=get(3,1,lead)
        assert list(raw.coeffs())==coeffs
        degs=[19,21,34] if gdeg==0 else [20,22,35]
        small_exact(F,A,B,C,None if gdeg==0 else G[1],degs,gdeg,[1] if gdeg else [])
    raw,F=get(2,8)
    assert list(raw.coeffs())==[2,-9,12]
    small_exact(F,A,B,C,None,[17,20,32],0,[])
    raw,F=get(2,14)
    assert list(raw.coeffs())==[6,-33,55]
    small_exact(F,A,B,C,G[1],[20,22,35],2,[1,1])
    for d,m,lc,gi,p,a0,deg,rs in [
       (8,2,6300,3,31,9,18,[1,1]),
       (8,2,22680,None,19,8,19,[]),
       (12,2,12251250,17,23,20,19,[1]),
       (12,2,948062981250,8,17,6,19,[1]),
       (12,3,None,4,37,7,18,[1,1]),
       (8,4,None,1,17,14,19,[1]),
       (8,36,None,3,19,13,14,[1,1,1,1,1,1])]:
       _,F=get(d,m,lc)
       small_saturated(F,A,B,C,None if gi is None else G[gi],p,a0,deg,rs,(d,m,lc))
    for d,p,a0 in [(114,17,11),(124,23,13)]:
       _,F=get(d,1)
       large_unit(F,A,B,C,p,a0)
    for d,gi,p,a0,b0,Ndeg in [(20,6,23,20,5,250),(60,16,31,10,5,694)]:
       raw,F=get(d,1)
       large_linear(F,A,B,C,p,a0,b0,G[gi])
       n=reconstruct(A,G[gi],'exact guard norm %s'%gi)
       assert n.degree()==Ndeg and (n%raw).is_zero()
    _,F=get(56,1)
    K,a,b,ev=large_linear(F,A,B,C,23,6,13)
    assert all(ev(g)!=0 for g in E+G)
    row,cof=right_origin(K,a,b)
    assert row==[0,0,0,16,14] and cof==[18,7,11,0,0]
    print('degree 56 actual right temporal row and unit cofactors',row,cof,flush=True)
    if secondary:
       other=reconstruct(A,C,'second affine norm')
       assert other.degree()==1455
       target=N.gcd(other)
       assert target.degree()==686
       expected=N//(int(N.content())*(1 if N[N.degree()]>0 else -1))
       assert target//int(target.content())==expected//(get(114,1)[0]*get(124,1)[0])
    print('entire actual temporal rank-loss / right raw affine loss excluded on F_R',flush=True)

if __name__=='__main__':
    import sys
    assert all(s=='--secondary-norm' for s in sys.argv[1:])
    t=monotonic()
    replay_temporal('--secondary-norm' in sys.argv)
    print('seconds %.3f'%(monotonic()-t))
