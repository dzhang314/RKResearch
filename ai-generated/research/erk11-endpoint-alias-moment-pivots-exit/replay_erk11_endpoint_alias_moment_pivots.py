#!/usr/bin/env python3
"""Both endpoint-alias fixed moment masks: exact projections and guarded exits.
Requires python-flint 0.9+; no separate coefficient checkpoint.
"""
from itertools import combinations
from math import comb
import flint
from fractions import Fraction
from itertools import permutations
from functools import reduce
A=flint.fmpq_mpoly_ctx.get(('a','d','X'))
R=flint.fmpq_mpoly_ctx.get(('a','d'))
a,d,X=A.gens(); aa,dd=R.gens(); bb=1-dd
one=R.from_dict({(0,0):1});zero=R.from_dict({})
W=X**2*(X-a)**2;V=(1-X)**2*(X-d)**2
def prim(f):
 return A.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in f.to_dict().items()})
def int_(f,s=0):
 r={}
 for (i,j,k),c in f.to_dict().items(): r[(i,j)]=r.get((i,j),0)+c/(k+s+1)
 return R.from_dict(r)
def intoA(f):
 return A.from_dict({(i,j,0):c for (i,j),c in f.to_dict().items()})
def at(f,y):
 return sum((R.from_dict({(i,j):c})*y**k for (i,j,k),c in f.to_dict().items()),zero)
P=prim(W);QQ=prim(V);Q=intoA(at(QQ,one))-QQ
H=int_(P*V);C1=int_(P*V,1);C2=int_(W*Q,1);J=int_(P*Q)
assert H==int_(W*Q) and J==C1-C2
I0,I1,I2=(int_(W*V,k) for k in range(3))
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
def dot(l,r):
 return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
EL=lambda t:[t**(i+1) for i in range(5)]
ER=lambda t:[(1-t)*t**i for i in range(5)]
L0=[one,zero,zero,zero,zero];La=[(i+1)*aa**i for i in range(5)]
R1=[one]*5;Rd=[dd**i-(bb*i*dd**(i-1) if i else zero) for i in range(5)]
def detGate(Lhat,Rhat):
 u,v=[dot(x,Rhat) for x in (L0,La)]
 w,z=[dot(Lhat,y) for y in (R1,Rd)]
 return dot([v*x-u*y for x,y in zip(L0,La)],[z*x-w*y for x,y in zip(R1,Rd)])
def atD():
 ZN=C1;ZD=H
 XN=I2*ZD-ZN*I1;XD=I1*ZD-ZN*I0
 U=C2*XD-XN*H
 pt=at(P,aa);pv=at(P,dd);vv=at(W,dd)
 DA=U*pt;NA=J*(dd*XD-XN)*vv-U*pv
 Lhat=[DA*x+NA*y for x,y in zip(EL(dd),EL(aa))]
 Rhat=ER(dd)
 return detGate(Lhat,Rhat),XN,XD,U,Lhat,Rhat
def atZero():
 ZN=I2*H-C2*I1;ZD=I1*H-C2*I0
 U=C1*ZD-ZN*H
 qt=at(Q,dd);qv=at(Q,zero);vv=at(V,zero)
 DA=U*qt;NA=-J*ZN*vv-U*qv
 Lhat=EL(aa)
 Rhat=[DA*x+NA*y for x,y in zip(ER(zero),ER(dd))]
 return detGate(Lhat,Rhat),ZN,ZD,U,Lhat,Rhat
def toQ(f,shape):
 qa=flint.fmpq_poly([0,1])
 out=flint.fmpq_poly([])
 for (i,j),c in f.to_dict().items():
  out += c*qa**i*shape(qa)**j
 return out
def diagonal_width(which):
    _,xn,xd,U,L,Rv=dict(d=atD,o=atZero)[which]()
    nz=(dd*xd-xn)*at(W,dd) if which=='d' else -xn*at(V,zero)
    raw=210*dot(L,Rv)-nz*at(P,aa)*at(Q,dd)
    dropped=[]
    for g in (aa,dd,dd-1,aa-dd):
        n=0
        while (raw%g).is_zero():
            raw=raw//g;n+=1
        dropped.append(n)
    expected=(8,13) if which=='d' else (10,8)
    assert raw.degrees()==expected
    return raw,tuple(dropped)


from time import monotonic

def col_gcd(vals):
    return reduce(lambda f,g:f.gcd(g),vals,zero)
def reduce_cols(l):
    g=col_gcd(l)
    assert g
    return [v//g for v in l],g
def coords(p,degree=None):
    n=p.degrees()[2] if degree is None else degree
    out=[{} for _ in range(n+1)]
    for (i,j,k),v in p.to_dict().items():out[k][(i,j)]=v
    return [R.from_dict(v) for v in out]
def hom3(p,n,d):
    assert p.degrees()[2]<=3
    return sum((v*n**j*d**(3-j) for j,v in enumerate(coords(p,3))),zero)
def det3(M):
    x,y,z=M
    return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])

def base(which):
    if which=='d':
        _,xn,xd,u,lh,rh=atD()
        zn,zd=C1,H
    else:
        _,zn,zd,u,lh,rh=atZero()
        xn,xd=C2,H
    if which=='d':
        T,RG=reduce_cols(rh)
        ls,LG2=reduce_cols([dot(v,T) for v in (L0,La)])
        Lx=[ls[1]*u-ls[0]*v for u,v in zip(L0,La)]
        L,LG=reduce_cols(Lx)
        rs,RG2=reduce_cols([dot(L,v) for v in (R1,Rd)])
    else:
        L,LG=reduce_cols(lh)
        rs,RG2=reduce_cols([dot(L,v) for v in (R1,Rd)])
        Tx=[rs[1]*u-rs[0]*v for u,v in zip(R1,Rd)]
        T,RG=reduce_cols(Tx)
        ls,LG2=reduce_cols([dot(v,T) for v in (L0,La)])
    print('Alias',which,'row divisors',LG.degrees(),RG.degrees(),
          'slope divisors',LG2.degrees(),RG2.degrees(),flush=True)
    return L,T,ls,rs,xn,xd,zn,zd,(LG,RG,LG2,RG2)

def rp(R0):
    assert R0.degrees()[1]==0
    a=R0.to_dict()
    return flint.fmpq_poly([a.get((k,0),0) for k in range(R0.degrees()[0]+1)])

def evp(f,av,prime=19):
    K=flint.fmpz_mod_poly_ctx(prime)
    c=[0]*(f.degrees()[1]+1)
    for (i,j),v in f.to_dict().items():
        c[j]=(c[j]+int(v.numerator)*pow(int(v.denominator),-1,prime)*pow(av,i,prime))%prime
    return K(c)

def geometry(a):
    assert not a.is_zero()
    for x in (aa,dd,dd-1,aa-dd):
        while (a%x).is_zero():a=a//x
    return a


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

def detm(ls):
    a,b,c=ls
    return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])

def local(C,a,d,ev,bys,side):
    X=C.gen();Y=1-X;z=C([0])[0]
    L,T,ls,rs,xn,xd,zn,zd,sc=bys
    if side:
        w,c=a,d
        l0,l1=map(ev,ls)
        x=ev(xn)/ev(xd)
        vec=[sum((N[i][j]*ev(T[j]) for j in range(5)),z) for i in range(5)]
        E0=C([0]+vec)
    else:
        w,c=1-d,1-a
        l0,l1=map(ev,rs)
        x=1-ev(zn)/ev(zd)
        vec=[sum((ev(L[i])*N[i][j] for i in range(5)),z) for j in range(5)]
        E0=sum((vec[j]*X*Y**j for j in range(5)),C([]))
    h=w/2
    num=w**5*E0-X**3*(6*X**2-15*w*X+10*w**2)*E0(w)
    E,r=divmod(num,X*(X-w));assert r.is_zero()
    B0=X*(X-w)*(X-h)
    B1=(X-h)*(w*l0-(l0-l1)*X)
    phi=X**2*(w-X)
    wt=X*(1-X)*(X-w)*(X-c)
    s0=(-w*E[0]*B0)//X
    s1=(w*(E*B1(0)-E[0]*B1))//X
    columns=[phi,X*B0,X*B1,B0,B1]
    mm=[]
    for j in range(3):
        row=[]
        for q in columns:
            f=wt*q
            row.append(sum((f[i]/(i+j+1) for i in range(len(f))),z))
        mm.append(row)
    mom_det=detm([v[:3] for v in mm])
    mm.append([w*x*(x-w)*E[0], x*s0(x),x*s1(x),s0(x),s1(x)])
    CC=[]
    guards=[]
    for j in (3,4):
        u=mm[:3];sc=[-detm([[r[k] if k!=i else r[j] for k in range(3)] for r in u]) for i in range(3)]
        CC.append(sum((c*v for c,v in zip(sc,mm[3][:3])),z)+mom_det*mm[3][j])
    if CC[1]==0:return 'affine slope zero',mom_det,CC
    t=-CC[0]/CC[1]
    if t==0:return 'zero t',mom_det,CC
    jjs=None
    for jj in combinations(range(4),3):
        dd=detm([mm[i][:3] for i in jj])
        if dd!=0:jjs=jj;break
    if jjs is None:return 'full first block rank loss',mom_det,CC
    sm=[mm[i][:3]+[mm[i][3]+t*mm[i][4]] for i in jjs]
    U,W,T=[-detm([[r[k] if k!=i else r[3] for k in range(3)] for r in sm])/dd for i in range(3)]
    assert all(r[0]*U+r[1]*W+r[2]*T+r[3]+t*r[4]==0 for r in mm)
    BB=B0+t*B1
    QQ=U*phi+W*X*B0+T*X*B1+BB
    p1=T-t*W
    PP=w*(t*U+(X-h)*p1)/t
    assert PP.degree()<=1 and QQ.degree()<=4
    assert ((QQ-PP*phi/w)%BB).is_zero()
    return 'live',mom_det,(PP,QQ,BB,t,jjs)

def place(F,D,G,p,a0,d0):
    C=flint.fmpz_mod_poly_ctx(p)
    red=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    FH=C([red(q) for q in monic(F).coeffs()])
    assert FH.degree()==F.degree() and FH(a0)==0 and FH.derivative()(a0)!=0
    DD=evp(D,a0,p)
    assert DD.degree()==8
    gd=DD.gcd(evp(G,a0,p))
    assert gd.degree()==1 and -gd[0]/gd[1]==d0
    a=C([a0])[0]
    d=C([d0])[0]
    z=C([0])[0]
    def ev(f):
        return sum((red(q)*a**i*d**j for (i,j),q in f.to_dict().items()),z)
    return C,a,d,ev

def recover(C,a,d,ev,b,side):
    measured=local(C,a,d,ev,b,not side)
    if measured[0]!='live':return ('other not live',measured[0])
    P,Q,B,t,jj=measured[2]
    X=C.gen()
    Y=1-X
    zer=C([0])[0]
    P=P(Y);Q=Q(Y)
    L,T,ls,rs,xn,xd,zn,zd,sc=b
    if side:
       w=a
       l0,l1=map(ev,ls)
       x=ev(xn)/ev(xd)
       Ebase=C([0]+[sum((N[i][j]*ev(T[j]) for j in range(5)),zer) for i in range(5)])
    else:
       w=1-d
       l0,l1=map(ev,rs)
       x=1-ev(zn)/ev(zd)
       vv=[sum((ev(L[i])*N[i][j] for i in range(5)),zer) for j in range(5)]
       Ebase=sum((vv[j]*X*Y**j for j in range(5)),C([]))
    h=w/2
    f=X**2*(w-X)/w
    if any(z==0 for z in (P(h),Q(h),f(h),P(x),Q(x))):return ('sample zero',)
    Q=Q*(P(h)*f(h)/Q(h))
    E,rr=divmod(w**5*Ebase-X**3*(6*X**2-15*w*X+10*w**2)*Ebase(w),X*(X-w))
    assert rr.is_zero()
    B0=X*(X-w)*(X-h)
    B1=(X-h)*(w*l0-(l0-l1)*X)
    S0=-w*E[0]*(X-w)*(X-h)
    S1,rr=divmod(w*(E*B1(0)-E[0]*B1),X);assert rr.is_zero()
    k0=Q(x)*S0(x)
    k1=P(x)*x*(x-w)*E(x)*B1(0)+Q(x)*S1(x)
    if k1==0:return ('outer residue zero slope',int(k0))
    t=-k0/k1
    BB=B0+t*B1
    quo,rr=divmod(Q-P*f,BB)
    return ('mark',rr,int(k0),int(k1),int(t), list(map(int,P.coeffs())),list(map(int,Q.coeffs())),
        list(map(int,BB.coeffs())),list(map(int,quo.coeffs())))

F_PURE=[1,-14,56,-84,42]
F_RHO=[1,-16,72,-120,66]
F_D0=[35,-420,1512,-2100,990]

def fixed_mask(b,side):
    if side:
        w,c=aa,dd
        l0,l1=b[2]
    else:
        w,c=1-dd,1-aa
        l0,l1=b[3]
    w,c,l0,l1=map(intoA,(w,c,l0,l1))
    h=w/2
    B0=X*(X-w)*(X-h)
    B1=(X-h)*(w*l0-(l0-l1)*X)
    wt=X*(1-X)*(X-w)*(X-c)
    return geometry(det3([[int_(wt*p,j) for p in (X**2*(w-X), X*B0, X*B1)] for j in range(3)]))

def ingress(F,D,M,b,witness):
    C,a,d,ev=place(F,D,M,*witness)
    _,zn,zd,u,_,_=atZero()
    S=-zn*at(V,zero)
    guards=(aa,dd,dd-1,aa-dd,H,J,zn,zd,u,S,b[2][0],b[3][0],*b[-1])
    assert all(ev(f)!=0 for f in guards)
    return C,a,d,ev

def show_root(F,D,M,extra):
    c,e,gcd=number_field(F)
    q=gcd(c(D),c(M))
    assert len(q)==2 and q[1]==qp([1])
    d=-q[0]
    assert all(e(z,d).is_zero() for z in (D,M,*extra))

def right_proof(D,b):
    M=fixed_mask(b,False)
    assert M.degrees()==(7,7)
    r=rp(D.resultant(M,'d'))
    fs=r.factor()[1]
    assert r.degree()==126 and sorted((f.degree(),m) for f,m in fs)==[(4,1),(4,5),(42,1),(60,1)]
    fs={(f.degree(),m):monic(f) for f,m in fs}
    assert fs[(4,1)]==monic(qp(F_PURE)) and fs[(4,5)]==monic(qp(F_RHO))
    bv,_,gg=number_field(fs[(4,1)])
    assert gg(bv(D),bv(M))==[qp([1])]
    bv,_,_=number_field(fs[(4,5)])
    assert not bv(b[3][0]*b[-1][3])
    print('right moment mask: exact degree 126, quartic (exact d gcd 1), '
          'quartic power5 (old right slope), degrees 42 and 60')
    C,a,d,ev=ingress(fs[(42,1)],D,M,b,(29,9,15))
    A=local(C,a,d,ev,b,True)
    B=local(C,a,d,ev,b,False)
    assert A[0]==B[0]=='live' and A[1]!=0 and B[1]==0
    P,Q,BL,t,jj=A[2]
    Pr,Qr,BR,tr,jr=B[2]
    assert (t,tr)==(17,10) and jj==(0,1,2) and jr==(0,1,3)
    assert list(map(int,P.coeffs()))==[0,1]
    assert list(map(int,Pr.coeffs()))==[8,8]
    assert P[0]*Pr[1]+P[1]*(Pr[0]+Pr[1])==16
    print('right 42: place (29,9,15), right actual temporal pivot, first-pool mark 16')
    C,a,d,ev=ingress(fs[(60,1)],D,M,b,(19,11,12))
    tag,rem,k0,k1,t,P,Q,B,U=recover(C,a,d,ev,b,False)
    assert tag=='mark' and (k0,k1,t)==(2,12,3)
    assert list(map(int,rem.coeffs()))==[8,16,5]
    assert (P,Q,B,U)==([11,1],[15,17,9,16,1],[15,5,14,1],[3,13])
    print('right 60: place (19,11,12), measured left profile/true right outer affine (2,12), '
          't_R=3, right calibration remainder 5Y^2+16Y+8')

def left_proof(D,b):
    M=fixed_mask(b,True)
    assert M.degrees()==(8,6)
    r=rp(D.resultant(M,'d'))
    fs=r.factor()[1]
    assert r.degree()==115 and sorted((f.degree(),m) for f,m in fs)==[
        (1,15),(4,1),(4,1),(4,5),(12,1),(24,1),(36,1)]
    ff=[monic(f) for f,m in fs]
    assert all(monic(qp(f)) in ff for f in ([0,1],F_PURE,F_D0,F_RHO))
    bv,_,gg=number_field(qp(F_PURE))
    assert gg(bv(D),bv(M))==[qp([1])]
    bv,_,_=number_field(qp(F_RHO))
    assert not bv(b[3][0]*b[-1][3])
    show_root(qp(F_D0),D,M,(dd,))
    _,zn,zd,u,_,_=atZero()
    show_root(next(f for f in ff if f.degree()==12),D,M,(zn,zd,u,-zn*at(V,zero)))
    print('left moment mask: exact degree 115; a=0, d=0, no d, old right slope, '
          'and z_N=z_D=S=U=0 small exits')

    F=next(f for f in ff if f.degree()==24)
    C,a,d,ev=ingress(F,D,M,b,(31,25,7))
    A=local(C,a,d,ev,b,True)
    B=local(C,a,d,ev,b,False)
    assert A[0]==B[0]=='live' and A[1]==B[1]==0
    P,Q,BL,t,jj=A[2]
    Pr,Qr,BR,tr,jr=B[2]
    assert (t,tr)==(28,1) and jj==jr==(0,1,3)
    assert list(map(int,P.coeffs()))==[7,18]
    assert list(map(int,Pr.coeffs()))==[22,19]
    assert P[0]*Pr[1]+P[1]*(Pr[0]+Pr[1])==3
    print('left 24: place (31,25,7), both actual temporal pivots, first-pool mark 3')

    F=next(f for f in ff if f.degree()==36)
    c,e,gcd=number_field(F)
    G=gcd(c(D),c(zn))
    assert len(G)==2 and G[1]==qp([1])
    d=-G[0]
    assert all(e(q,d).is_zero() for q in (D,M,zn))
    place(F,D,M,23,2,6)
    print('left 36: exact d root with z_N=0, entire residue gcd linear at full degree8 (23,2,6)')

def replay():
    D,geo=diagonal_width('o')
    assert D.degrees()==(10,8) and geo==(1,1,3,0)
    b=base('o')
    right_proof(D,b)
    left_proof(D,b)
    print('both fixed moment masks excluded; two raw affine masks remain separate')

if __name__=='__main__':
    replay()
