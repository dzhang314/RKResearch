#!/usr/bin/env python3
"""Full rank of the actual neighboring moment operator; python-flint 0.9.0, SymPy 1.14.0."""
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
import sympy as sy

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

def pols():
    p,q,Hd,Cl,Cr,U,S,BN,Rhat,L9,alpha,beta,K,guards,zD,zN=width_rows()
    j4=1-14*s+56*s**2-84*s**3+42*s**4
    j5=-1+20*s-120*s**2+300*s**3-330*s**4+132*s**5
    assert all(it(s*(1-s)*j4,k).is_zero() for k in range(4))
    assert all(it(s*(1-s)*j5,k).is_zero() for k in range(5))
    ai,di=[dcol(w.compose(a,b,a)) for w in (j4,j5)],[dcol(w.compose(a,b,d)) for w in (j4,j5)]
    si=[fs(w,Cr,Hd,5) for w in (j4,j5)]
    dt=lambda x,y:x[0]*y[1]-x[1]*y[0]
    M0,M1,M2=dt(ai,di),dt(ai,si),dt(di,si)
    P=gcdgeo(M0,guards)
    Q=gcdgeo(M1,guards)
    R=gcdgeo(M2,guards)
    print('raw and cleaned degs',*[u.degrees() for u in (M0,M1,M2,P,Q,R)],flush=True)
    rs1=dv(P.resultant(Q,'b'))
    rs2=dv(P.resultant(R,'b'))
    g=rs1.gcd(rs2)
    print('a resultants',rs1.degree(),rs2.degree(),'common',g.degree(),
        [(F.degree(),m) for F,m in g.factor()[1]],flush=True)
    return (P,Q,R),g.factor()[1],guards

def exact_b():
    pol,fac,guards=pols()
    assert len(fac)==1 and fac[0][0].degree()==60
    F=monic(fac[0][0])
    A,B=sy.symbols('A B')
    def sym(f):
        return sy.Poly.from_dict({(i,j):sy.Rational(int(q.numerator),int(q.denominator))
                for (i,j),q in f.to_dict().items()},A,B,domain='QQ').as_expr()
    def qq(f):
        return qp([F0(int(u.p),int(u.q)) for u in sy.Poly(f,A).all_coeffs()[::-1]])
    F0=flint.fmpq
    S=sy.subresultants(sym(pol[0]),sym(pol[1]),B)
    print('exact PRS degrees',[(sy.degree(g,B),sy.degree(g,A)) for g in S],flush=True)
    G=next(g for g in S if sy.degree(g,B)==1)
    coeff=[qq(w)%F for w in sy.Poly(G,B).all_coeffs()]
    LL,MM=coeff
    gg,l,r=LL.xgcd(F)
    assert gg==qp([1])
    t=(-MM*l)%F
    print('b polynomial degree',t.degree(),'denom bits',int(t.denom()).bit_length(),flush=True)
    def ev(f):
        ss=qp()
        for x in reversed(A_polys(f)):
           ss=(ss*t+x)%F
        return ss
    assert all(ev(w).is_zero() for w in pol)
    assert all(not ev(w).is_zero() for w in guards)
    C,a,b,r,*_=residue(31,7,19)
    def rd(z):
       return C([r(g) for g in z.coeffs()])(a)
    assert rd(LL)!=0 and rd(t)==b
    print('exact simple b reconstruction from subresultant b=−M/L; selected (31,7,19)',flush=True)
    return pol,F,LL,MM,t,ev,guards

def temporal(side):
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
    M0,M1=[r[:3] for r in M[:2]]
    O3=[toC(p) for p in O[:3]]
    base=dcol(det3([M0,M1,O3]))
    adj=det3([cols[:3],M1,O3])+s*det3([M0,cols[:3],O3])
    assert adj.degrees()[2]<=5
    raw=alpha*BN*S*base+U*beta*fs(adj,ns,ds,6)
    print('raw temporal degs',side, raw.degrees(),flush=True)
    return gcdgeo(raw,guards+[L0,K] +([] if side else [rs0]))

def kernel4(C,A):
    z=C([0])[0];one=C([1])[0]
    M=[row[:] for row in A]; p=0;piv=[]
    n=len(A[0])
    for j in range(n):
        i=next((i for i in range(p,len(M)) if M[i][j]!=0),None)
        if i is None:continue
        M[p],M[i]=M[i],M[p]
        q=M[p][j];M[p]=[x/q for x in M[p]]
        for r in range(len(M)):
           if r!=p:
               v=M[r][j];M[r]=[x-v*y for x,y in zip(M[r],M[p])]
        p+=1;piv.append(j)
    if p!=n-1:return p,None
    free=next(j for j in range(n) if j not in piv)
    res=[z]*n;res[free]=one
    for i,j in enumerate(piv):res[j]=-M[i][free]
    return p,res

def branch(C,w,c,x0,sc,vr,side,J,v,u,D0,Da,E0,Ed,f):
    if side:
        l0,l1=f(D0,vr),f(Da,vr)
    else:
        l0,l1=f(vr,E0),f(vr,Ed)
    assert l0!=0 and l1!=0
    X=C.gen();Y=1-X;z=C([0])[0]
    if side:
       en=C([z]+[sum((N[i][j]*vr[j] for j in range(5)),z) for i in range(5)])
    else:
       en=sum((sum((vr[i]*N[i][j] for i in range(5)),z)*X*Y**j for j in range(5)),C([]))
    h=w/2;phi=X*X*(w-X)
    B0=X*(X-w)*(X-h);B1=(X-h)*(w*l0-(l0-l1)*X)
    E,R=divmod(w**5*en-X**3*(6*X**2-15*w*X+10*w*w)*en(w),X*(X-w));assert R.is_zero()
    S0=-w*E[0]*(X-w)*(X-h)
    S1,R=divmod(w*(E*B1(0)-E[0]*B1),X);assert R.is_zero()
    Cc=[phi,X*B0,X*B1,B0,B1]
    wt=X*Y*(X-w)*(X-c)
    def it(p,j):return sum((p[i]/(i+j+1) for i in range(len(p))),z)
    rho=J/(u*v)
    M=[[it(wt*p,j)-rho*sc**j*p(sc) for p in Cc] for j in range(3)]
    Oo=[w*x0*(x0-w)*E[0],x0*S0(x0),x0*S1(x0),S0(x0),S1(x0)]
    if det3([r[:3] for r in M])!=0:return 'not rank2'
    A,B=M[0],M[1]
    det=A[0]*B[1]-A[1]*B[0]
    if det==0:return 'bad 2 pivot'
    def ux(a,b):return (a*B[1]-A[1]*b)/det
    def wx(a,b):return (A[0]*b-a*B[0])/det
    ucoef=[ux(-A[k],-B[k]) for k in (2,3,4)]
    wcoef=[wx(-A[k],-B[k]) for k in (2,3,4)]
    assert all(row[k]+row[0]*ucoef[k-2]+row[1]*wcoef[k-2]==0 for row in M for k in (2,3,4))
    lack=[Oo[k]+Oo[0]*ucoef[k-2]+Oo[1]*wcoef[k-2] for k in (2,3,4)]
    assert lack[0]==0
    assert lack[1]!=0 and lack[2]!=0
    t=-lack[1]/lack[2]
    Qs=[U*phi+W*X*B0+C for U,W,C in zip(ucoef,wcoef,[X*B1,B0,B1])]
    def P(T,A,t):
       U=ucoef[0]*T+(ucoef[1]+ucoef[2]*t)*A
       W=wcoef[0]*T+(wcoef[1]+wcoef[2]*t)*A
       return w*(U+(X-h)*(T/t-W))
    print('flank restored / endpoint separate',int(det),list(map(int,lack)),int(t),flush=True)
    return 'fit',Qs,P,t

def replay():
    pol,F,LL,MM,bb,at,guards=exact_b()
    assert [f.degrees() for f in pol]==[(4,4),(12,8),(8,12)]
    assert bb.degree()==59
    C,a,b,red,ev,spec=residue(31,7,19)
    FA=C([red(c) for c in F.coeffs()])
    ps=[spec(p) for p in pol]
    assert FA.degree()==60 and FA(a)==0 and FA.derivative()(a)==1
    assert ps[0].degree()==4 and ps[0][4]==16 and ps[0].derivative()(b)==27
    G=ps[0].gcd(ps[1]).gcd(ps[2])
    assert G==C([-19,1]) and all(ev(w)!=0 for w in guards)
    K0=width_rows()[12]
    assert ev(K0)==16
    print('simple exact width place (31,7,19), full b-degree4 and whole joint gcd b-19',flush=True)
    for side,ds,nd in [(True,(32,29),244),(False,(44,39),332)]:
        eq=temporal(side)
        assert eq.degrees()==ds
        norm=dv(pol[0].resultant(eq,'b'))
        assert norm.degree()==nd and (norm%F).is_zero()
        assert at(eq).is_zero()
        print('actual first-three temporal determinant exactly zero',side,ds,nd,flush=True)

    data,dp,beta,u,L9=measure(C,a,b)
    a,b,d,s,z,v,J,_,_,R9,D0,Da,E0,Ed,*_=data
    l0,l1=dp(D0,R9),dp(Da,R9)
    L7=[l0*q-l1*p for p,q in zip(D0,Da)]
    LL=branch(C,a,d,s,s,R9,True,J,v,u,D0,Da,E0,Ed,dp)
    RR=branch(C,b,1-a,1-z,1-s,L7,False,J,v,u,D0,Da,E0,Ed,dp)
    assert LL[0]==RR[0]=='fit'
    assert (LL[3],RR[3])==(1,25)
    X=C.gen()
    LQ=[LL[1][0],LL[1][1]+LL[3]*LL[1][2]]
    RQ=[RR[1][0](1-X),(RR[1][1]+RR[3]*RR[1][2])(1-X)]
    assert [list(map(int,q.coeffs())) for q in LQ+RQ]==[
       [0,1,22,21,12],[1,22,21,12],[18,9,22,14,30],[16,24,16,25]]
    for lv,rv,wanted in [(0,0,2),(1,0,3),(0,1,3),(1,1,3)]:
        mat=[[l[i] for l in LQ[:1+lv]]+[-r[i] for r in RQ[:1+rv]] for i in range(5)]
        rank,ker=kernel4(C,mat)
        assert rank==wanted
        if lv and rv:
            assert list(map(int,ker))==[24,9,22,1]
            p=LL[2](ker[0],ker[1],LL[3])
            q=RR[2](ker[2],ker[3],RR[3])
            assert [list(map(int,g.coeffs())) for g in (p,q)]==[[20,12],[29,28]]
            assert p[0]*q[1]+p[1]*(q[0]+q[1])==4
        else:
            assert rank==len(mat[0]) and ker is None
    print('all four endpoint masks excluded: Q ranks 2/3/3; both-live P determinant 4',flush=True)
    print('full corrected moment rank loss excluded; individual fixed/affine losses not excluded')
if __name__=='__main__':
    replay()
