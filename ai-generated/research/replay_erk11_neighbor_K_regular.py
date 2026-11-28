#!/usr/bin/env python3
"""Exact fully pivotable neighboring K-curve exit. Requires python-flint 0.9.0."""
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
from functools import lru_cache

def minor_data(side):
    p,q,Hd,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,guards,zD,zN=width_rows()
    if side:
        w,c,ns,ds=a,d,Cr,Hd
        hull0=one
        hull1=sum(((i+1)*a**i*N[i][j] for i in range(5) for j in range(5)),zero)
        e=sum((toC(Rhat[j])*N[i][j]*s**(i+1) for i in range(5) for j in range(5)),zero)
        xx,xd=Cr,Hd
    else:
        w,c,ns,ds=b,1-a,Hd-Cr,Hd
        Ed=[dcol(d**i-((1-d)*i*d**(i-1) if i else zero)) for i in range(5)]
        rs0,rs1=rowdot(L9,[one0]*5),rowdot(L9,Ed)
        gt=rs0.gcd(rs1)
        hull0,hull1=map(toC,(rs0//gt,rs1//gt))
        gr=L9[0]
        for term in L9[1:]:gr=gr.gcd(term)
        L9=[term//gr for term in L9]
        e=sum((toC(L9[i])*N[i][j]*s*(1-s)**j for i in range(5) for j in range(5)),zero)
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
    return K,guards,D,c0,c1,g0,g1,cols,w,h

def A_polys(R):
    ngh=R.degrees()[1]
    tab=[{} for _ in range(ngh+1)]
    for (i,j),c in R.to_dict().items():tab[j][i]=c
    return [qp([row.get(i,0) for i in range(max(row,default=-1)+1)]) for row in tab]

def fromA(v):
    return C2d.from_dict({(i,j):p[i] for j,p in enumerate(v) for i in range(len(p)) if p[i]})

def qring(K):
    ks=A_polys(K)
    assert len(ks)==4
    lam=ks.pop()
    z=qp()
    @lru_cache(None)
    def powl(n):
        return lam**n
    def trim(v):
        while v and v[-1].is_zero():v.pop()
        return v
    def collapse(v,e=0):
        v=trim(v)
        while len(v)>3:
            k=len(v)-4
            t=v.pop()
            v=[r*lam for r in v]
            for j in range(3):v[k+j]-=t*ks[j]
            e+=1
            trim(v)
        if not v:return [],0
        while e:
            qr=[divmod(p,lam) for p in v]
            if any(not r.is_zero() for q,r in qr):break
            v=[q for q,r in qr]
            e-=1
        return v,e
    def add(f,g):
        p,e=f;q,d=g
        if not p:return g
        if not q:return f
        E=max(e,d)
        vv=[t*powl(E-e) for t in p]+[z]*max(0,len(q)-len(p))
        for i in range(len(q)):vv[i]+=q[i]*powl(E-d)
        return collapse(vv,E)
    def mul(f,g):
        p,e=f;q,d=g
        if not p or not q:return [],0
        vv=[qp() for _ in range(len(p)+len(q)-1)]
        for i,x in enumerate(p):
            for j,y in enumerate(q):vv[i+j]+=x*y
        return collapse(vv,e+d)
    class R:
        def __init__(self,p,raw=None):
            self.v=raw if raw is not None else collapse(A_polys(p))
        def __add__(f,g):
            return R(None,add(f.v,g.v))
        def __sub__(f,g):
            return f + -g
        def __neg__(f):return R(None,([-v for v in f.v[0]],f.v[1]))
        def __mul__(f,g):
            return R(None,mul(f.v,g.v))
        def lift(f):
            p=fromA(f.v[0])
            return p
    return R,lam

def reg_shapes(side,R):
    K,guards,D,c0,c1,g0,g1,cols,w,h=minor_data(side)
    ds,cs,ct,v0,v1=R(D),list(map(R,c0)),list(map(R,c1)),R(g0),R(g1)
    print('pivots',side,D.degrees(),g0.degrees(),g1.degrees(),
          [g.v[1] for g in (ds,v0,v1)],flush=True)
    U,V,T=[x*v1-y*v0 for x,y in zip(cs,ct)]
    sl=-v1*T-v0*V
    p0=v0*U - R(dcol(h))*sl
    qp=[R(zero0) for _ in range(5)]
    for k,v in enumerate(cols):
        coeff=[U,V,T,ds*v1,-ds*v0][k]
        for j in range(5):
            cv=dcol(v,j)
            if not cv.is_zero():qp[j]=qp[j]+coeff*R(cv)
    if not side:
        # Move the polynomial in Y=1-X back to physical X.
        from math import comb
        op=list(qp)
        qp=[sum((op[j]*R(one0*((-1)**k*comb(j,k))) for j in range(k,5)),R(zero0)) for k in range(5)]
        p0=p0+sl
        sl=-sl
    print('shape ready',side,flush=True)
    return (p0,sl),qp,[D,g0,g1]
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
 idx=next((i for i in range(4) if V1[i]!=0),None)
 if idx is None:return 'ghost scale all zero',V0
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
 return 'pair mark',mk,(Ba,nu,mu,tau,f,scale)

def ordinary(C,a,b):
    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,Sp,K,H,I0,I1,I2=data
    LF=full_fit(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
    RF=full_fit(C,b,1-a,1-z,1-s,L9,False,J,v,u,D0,Da,E0,Ed,dp)
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
    return routine(C,(a,b,d,s,z,v,J,u,H,I0,I1,I2),l,r)

def compact_spec(f,p,a):
    xs=A_polys(f)
    r=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    C=flint.fmpz_mod_poly_ctx(p)
    return C([C([r(c) for c in f.coeffs()])(a) for f in xs])

def test_place(C,a,b):
  data,dp,beta,u,L9=measure(C,a,b)
  a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
  Lf=full_fit(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
  Rf=full_fit(C,b,1-a,1-z,1-s,L9,False,J,v,u,D0,Da,E0,Ed,dp)
  if Lf[0]!=Rf[0] or Lf[0]!='fit':return (Lf[0],Rf[0])
  lp,rp=Lf[1],Rf[1]
  mark=lp[0]*rp[1]+lp[1]*(rp[0]+rp[1])
  ql,qr=Lf[2],Rf[2](1-C.gen())
  qmark=[ql[i]*qr[j]-ql[j]*qr[i] for i,j in [(4,3),(4,2),(0,1),(0,4)]]
  return ('fit',int(mark),list(map(int,qmark)), list(map(int,lp.coeffs())),list(map(int,rp.coeffs())))

def project():
    *_,K,guards,zD,zN=width_rows()
    R,lam=qring(K)
    pl,ql,gl=reg_shapes(True,R)
    pr,qr,gr=reg_shapes(False,R)
    cuts=[(ql[i]*qr[j]-ql[j]*qr[i]).lift() for i,j in combinations(range(5),2)]
    assert all(p.is_zero() for p in cuts)
    print('all ten physical second-pool projectivity minors vanish identically on K, not independent',flush=True)
    p=pl[0]*pr[1]-pl[1]*pr[0]
    raw=p.lift()
    assert raw.degrees()==(1216,2) and p.v[1]==297
    w=gcdgeo(raw,guards+[fromA([lam])])
    r=dv(K.resultant(w,'b'))
    assert r.degree()==3642
    fs=r.factor()[1]
    assert sorted((f.degree(),m) for f,m in fs)==[(3,9),(3,594),(12,3),(12,18),(12,18),(15,2),(54,2),(66,3),(87,1),(102,3),(105,2),(108,1),(318,1)]
    print('first-pool projection degree 3642, factors',sorted((f.degree(),m) for f,m in fs),flush=True)
    return K,lam,w,fs,guards+gl+gr

def leading_exit(K,lam,guards):
    pairs=lam.factor()[1]
    assert len(pairs)==1 and pairs[0][0].degree()==3 and pairs[0][1]==1
    assert monic(lam)==monic(qp([-1,12,-36,30]))
    C,a,b,red,ev,spec=residue(37,11,0)
    aa=C([red(c) for c in monic(lam).coeffs()])
    assert aa.degree()==3 and aa(a)==0 and aa.derivative()(a)!=0
    kk=spec(K)
    assert kk.degree()==2 and kk/kk[2]==C([-24,1])*C([-26,1])
    for b0,mark,lp,rp in [(24,13,[14,25],[14,35]),(26,4,[9,15],[22,8])]:
        C,a,b,red,ev,spec=residue(37,11,b0)
        assert all(ev(g)!=0 for g in guards[:17])
        got=test_place(C,a,b)
        assert got==('fit',mark,[0,0,0,0],lp,rp)
        print('leading loss (37,11,'+str(b0)+') actual P lines',lp,rp,'mark',mark,flush=True)

def place(F,K,P,p,a0,b0):
    C,a,b,red,ev,spec=residue(p,a0,b0)
    aa=C([red(c) for c in monic(F).coeffs()])
    assert aa.degree()==F.degree() and aa(a)==0 and aa.derivative()(a)!=0
    kk=compact_spec(K,p,a0)
    q=compact_spec(P,p,a0)
    g=kk.gcd(q)
    assert kk.degree()==3 and g.degree()==1 and -g[0]/g[1]==b
    return C,a,b,ev,spec,kk,g

def replay():
    K,lam,P,fac,guards=project()
    leading_exit(K,lam,guards)
    fix={
      (87,1):(20,23,18,20,3), (108,1):(17,17,6,4,1),
      (15,2):(10,17,6,4,1), (54,2):(21,17,6,4,1),
      (105,2):(15,17,6,4,1), (12,3):(7,29,27,2,7),
      (66,3):(17,17,10,4,8), (102,3):(20,19,17,16,1),
      (3,9):(1,19,12,0,10),
    }
    names={20:'right fixed moment',17:'left fixed moment',10:'C2-aH',21:'right g0',
           15:'alpha prime',7:'S',1:'b',4:'J',5:'zD'}
    norms={i:dv(K.resultant(guards[i],'b')) for i in names}
    seen=[]
    for F,m in fac:
        d=F.degree()
        if monic(F)==monic(lam):
            assert (d,m)==(3,594)
            continue
        if d==318:
            C,a,b,ev,spec,kk,g=place(F,K,P,29,5,20)
            assert all(ev(w)!=0 for w in guards)
            hit=ordinary(C,a,b)
            assert hit[0]=='pair mark' and hit[1]==23
            assert list(map(int,hit[2]))==[17,15,20,10,2,5]
            print('degree318: (29,5,20), actual left plateau mark 23 from B,nu,mu,tau,f,scale =',
                   list(map(int,hit[2])),flush=True)
            continue
        if (d,m)==(12,18):
            i,p,a0,b0,kd=(4,17,3,2,16) if (norms[4]%F).is_zero() else (5,17,12,11,7)
        else:
            i,p,a0,b0,kd=fix[d,m]
        assert not norms[i].is_zero() and (norms[i]%F).is_zero()
        C,a,b,ev,spec,kk,g=place(F,K,P,p,a0,b0)
        assert kk.gcd(compact_spec(guards[i],p,a0))==g
        assert kk.derivative()(b)==kd and kd%p!=0
        seen.append((d,m,i))
        print('degree',d,'mult',m,'exact live guard lost',names[i],
               'at unique simple K place',(p,a0,b0),'derivative',kd,flush=True)
    assert sorted(seen)==sorted(
        [(d,m,t[0]) for (d,m),t in fix.items()]+[(12,18,4),(12,18,5)])
    assert len(seen)==11 and (12,18,4) in seen and (12,18,5) in seen
    print('all regular K widths, including b-leading loss, excluded; other neighboring widths not covered',flush=True)

if __name__=='__main__':
    replay()
