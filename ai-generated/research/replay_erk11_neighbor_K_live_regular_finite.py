#!/usr/bin/env python3
"""Independent first-pool and plateau width conditions, K nonzero. Requires python-flint 0.9.0."""
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
def minor_data(side):
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
    # Factor out global common formal row scalars; true pivots make these live.
    gr=D
    for z in c0+c1:gr=gr.gcd(z)
    D,c0,c1=D//gr,[z//gr for z in c0],[z//gr for z in c1]
    gr=O[0]
    for z in O[1:]:gr=gr.gcd(z)
    O=[v//gr for v in O]
    g0,g1=[D*O[3+i]+sum((u*v for u,v in zip(cc,O[:3])),zero0) for i,cc in enumerate([c0,c1])]
    assert not g0.is_zero() and not g1.is_zero()
    return K,guards+[L0,rs0] if not side else guards+[L0],D,c0,c1,g0,g1,cols,w,h,O
def rawline(side):
    K,guards,D,c0,c1,g0,g1,cols,w,h,O=minor_data(side)
    print('rawline slopes/pivots',side,[(f.degrees(),len(f.to_dict())) for f in [D,g0,g1]],flush=True)
    U,E,T=[i*g1-j*g0 for i,j in zip(c0,c1)]
    Z=-g1*T-g0*E
    p0=g0*U-dcol(h)*Z;p1=Z
    if not side:p0,p1=p0+p1,-p1
    dd=p0.gcd(p1)
    p0,p1=p0//dd,p1//dd
    print('line bidegrees',side,p0.degrees(),p1.degrees(),'removed common factor',dd.degrees(),flush=True)
    return K,guards,(p0,p1),[D,g0,g1]
def project1():
    K,guards,l,gl=rawline(True)
    K,guards2,r,gr=rawline(False)
    F=l[0]*r[1]-l[1]*r[0]
    print('raw determinant',F.degrees(),len(F.to_dict()),flush=True)
    # Gcd of normalized first-pool coordinate entries is live since P nonzero.
    # Smaller fixed pivots and real width denominators are live.
    guards=guards2+gl+gr+[K]
    G=gcdgeo(F,guards)
    print('first determinant deflated',G.degrees(),len(G.to_dict()),flush=True)
    fs=G.factor()[1]
    print('bivariate factors',[(q.degrees(),q.total_degree(),m) for q,m in fs],flush=True)
    return K,fs,guards
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

def both(C,a,b):
    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,Sp,K,H,I0,I1,I2=data
    l0,l1=dp(D0,R9),dp(Da,R9)
    L7=[l0*q-l1*p for p,q in zip(D0,Da)]
    LF=full_fit(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
    RF=full_fit(C,b,1-a,1-z,1-s,L7,False,J,v,u,D0,Da,E0,Ed,dp)
    if LF[0]!=RF[0] or LF[0]!='fit':return LF[0],RF[0]
    X=C.gen()
    def response(w,f):
        _,p,q,t,(l0,l1,delta,g0,g1),_=f
        if delta==0:return None
        h=w/2
        bl=(X-h)*(X*(X-w)+t*(w*l0-(l0-l1)*X))
        return p,q,bl,t
    l,r=response(a,LF),response(b,RF)
    if l is None or r is None:return 'moment'
    return (a,b,d,s,z,v,J,u,H,I0,I1,I2),l,r

def routine(K,data,L,R):
 a,b,d,s,z,v,J,u,H,I0,I1,I2=data
 P,Q,BL,tl=L
 Pr,Qr,BR,tr=R
 X=K.gen();Y=1-X;c0=K([0])[0]
 mm=P[0]*Pr[1]+P[1]*(Pr[0]+Pr[1])
 if mm!=0:return 'alternate-P mark',mm
 Q1=Qr(Y)
 if any(Q[i]*Q1[j]-Q[j]*Q1[i]!=0 for i in range(5) for j in range(i+1,5)):return 'Q compatibility fails'
 if Q.degree()!=4:return 'Q degree loss',Q.degree()
 Ds=-BL*BR(Y)*(X-s)*(X-z)
 assert Ds.degree()==8 and Ds[8]==1
 Om=X*(X-1)*(X-a)*(X-d)
 f=Om*Q
 Mr=K([sum((f[i]/(i-j) for i in range(j+1, f.degree()+1)),c0) for j in range(f.degree())])
 V0=(Ds*Mr-(J/(u*v))*Q(s)*(Ds//(X-s)))%Q
 V1=(P*P*X*(X-1))%Q
 cc=[(i,j) for i,j in combinations(range(4),2) if V0[i]*V1[j]-V0[j]*V1[i]!=0]
 if cc:return 'ghost minors',cc
 idx=0
 if V1[idx]==0:return 'fixed ghost scale pivot zero',V0
 scale=-V0[idx]/V1[idx]
 if scale==0:return 'zero scale impossible?', V0
 if P.degree()!=1:return 'linear P lost'
 A=s*(s-a);B=(1-s)*(s-d)
 b9=J/(A*B*u*v)
 xi=-P[0]/P[1]
 if Ds(xi)==0:return 'shape root guard'
 Pa=scale*P;Qa=scale*Q
 lam=-Qa(xi)**2/Ds(xi)
 B3,rem=divmod(Qa**2+lam*Ds,Pa)
 assert rem.is_zero()
 ell=(Om//(X-a))/Om.derivative()(a)
 gg,ip,_=((X-a)*Q).xgcd(Ds)
 if gg.degree()!=0:return 'scalar pair weight inverse guard'
 pp=(P*P*X*(X-1)*ip)%Ds
 Ba=sum((ell[i]/(i+1) for i in range(len(ell))),c0)-scale*pp[7]/(gg[0]*Om.derivative()(a))-b9*ell(s)
 Ds_a=(a-d)*Ds(a)
 if Ds_a==0:return 'pair clock denominator'
 nu,mu,tau=[w(a)/Ds_a for w in (Pa,Qa,B3)]
 f=-a*a/2
 mk=(mu-f*nu)**2-(nu-f*Ba)*(tau-f*mu)
 return ('pair mark',mk,(Ba,nu,mu,tau,f,scale),
         (V0,V1,xi,Ds(xi),Ds.derivative()(s),Om.derivative()(a),gg[0]))

def replay():
 K,fs,guards=project1()
 assert len(fs)==1 and fs[0][1]==1
 F=fs[0][0]
 assert F.degrees()==(111,107) and F.total_degree()==218
 p,a0,b0=17,7,7
 C,a,b,red,ev,spec=residue(p,a0,b0)
 Fb=compact_spec(F,p,a0)
 assert Fb.degree()==97 and Fb(b)==0
 assert all(ev(g)!=0 for g in guards) and ev(K)==12
 data=both(C,a,b)
 assert len(data)==3
 vals,l,r=data
 P,Q,BL,tl=l;Pr,Qr,BR,tr=r
 assert (tl,tr)==(5,13)
 assert [list(map(int,v.coeffs())) for v in (P,Q,BL,Pr,Qr,BR)]==[
    [5,9],[11,16,13,6,10],[11,6,1,1],[5,15],[4,5,15,4,8],[4,13,2,1]]
 hit=routine(C,*data)
 assert hit[0]=='pair mark' and hit[1]==13
 assert list(map(int,hit[2]))==[0,0,8,11,1,14]
 V0,V1,xi,Dxi,Ds_s,Om_a,g=hit[3]
 assert list(map(int,V0.coeffs()))==[3,2,11,7]
 assert list(map(int,V1.coeffs()))==[1,12,15,8]
 assert (xi,Dxi,Ds_s,Om_a,g)==(7,14,0,2,1)
 print('F vanishes at (17,7,7), K residue 12; both ordinary actual fits and both pool projectivities pass')
 print('fixed ghost scale coefficient 0 is live: V0[0]=3, V1[0]=1, scale 14')
 print("unit weight-sum inverse modulo monic Ds, although Ds'(s) reduces to zero")
 print('actual left plateau mark 13 from B,nu,mu,tau,f,scale =',list(map(int,hit[2])))
 print('transverse coefficient witness proves finite regular widths including first auxiliary denominator failures')
if __name__=='__main__':
 replay()
