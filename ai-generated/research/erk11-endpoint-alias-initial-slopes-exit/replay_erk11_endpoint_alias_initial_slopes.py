#!/usr/bin/env python3
"""Exact exclusions of the two central endpoint initial-slope masks.
Requires python-flint 0.9+; no separate coefficient data.
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

def alternate():
    _,zn,zd,_,_,r9=atZero()
    T,RG=reduce_cols(r9)
    ls,SG=reduce_cols([dot(u,T) for u in (L0,La)])
    V0=[ls[1]*u-ls[0]*v for u,v in zip(L0,La)]
    L,LG=reduce_cols(V0)
    rs,RG2=reduce_cols([dot(L,v) for v in (R1,Rd)])
    return L,T,ls,rs,C2,H,zn,zd,(LG,RG,SG,RG2)

def divide_d_minus_one(F,Q):
    out=[Q[-1]]
    for e in reversed(Q[1:-1]):
        out.append((e+out[-1])%F)
    assert (Q[0]+out[-1]).is_zero()
    return out[::-1]

def right_proof(D,b):
    r0,r1=[p*b[-1][3] for p in b[3]]
    F=monic(rp(geometry(r0)))
    assert F==monic(qp([1,-16,72,-120,66]))
    assert len(F.factor()[1])==1 and F.factor()[1][0][0].degree()==4
    bv,e,gcd=number_field(F)
    assert not bv(r0)
    Q=gcd(bv(D),bv(r1))
    assert len(Q)==5 and Q[-1]==qp([1])
    g=divide_d_minus_one(F,Q)
    assert len(g)==4 and g[-1]==qp([1])
    print('right raw slopes: F4=66a^4-120a^3+72a^2-16a+1 irreducible; '
          'exact common d-gcd degree 4; remove only d-1')

    C=flint.fmpz_mod_poly_ctx(23)
    red=lambda c:int(c.numerator)*pow(int(c.denominator),-1,23)%23
    FR=C([red(c) for c in F.coeffs()])
    A0=15
    assert FR(A0)==0 and FR.derivative()(A0)!=0
    cm=C([sum(red(c)*pow(A0,j,23) for j,c in enumerate(v.coeffs())) for v in g])
    assert cm==C([5,17,2,1])
    assert cm.factor()[1]==[(cm,1)]
    FF=flint.fq_default_ctx(modulus=cm,fq_type='FQ_NMOD')
    BP=flint.fq_default_poly_ctx(FF)
    a=FF(A0); d=FF.gen(); z0=FF.zero()
    ev=lambda f:sum((FF(red(c))*a**i*d**j for (i,j),c in f.to_dict().items()),z0)
    assert ev(D)==0 and ev(r0)==0 and ev(r1)==0
    _,zn,zd,u,_,_=atZero()
    S=-zn*at(V,zero)
    bys=alternate()
    guards=(aa,dd,dd-1,aa-dd,H,J,zn,zd,u,S,C2-aa*H,zn-dd*zd,*bys[2],*bys[3],*bys[-1])
    assert all(ev(f)!=0 for f in guards)
    left=local(BP,a,d,ev,bys,True)
    right=local(BP,a,d,ev,bys,False)
    assert left[0]==right[0]=='live' and left[1]!=0 and right[1]!=0
    P,Q,B,t,jj=left[2]
    Pr,Qr,Br,tr,jr=right[2]
    assert jj==jr==(0,1,2)
    assert t==6*d**2+16*d+21 and tr==2*d+18
    mark=P[0]*Pr[1]+P[1]*(Pr[0]+Pr[1])
    assert mark==2*d**2+15*d+1 and mark!=0
    print('right fallback: (p,a)=(23,15), all d roots in cubic d^3+2d^2+17d+5; '
          'live actual R9/L7 fits; first-pool mark 2d^2+15d+1 nonzero')
    return F

def left_proof(D,b,FR):
    raw=[p*b[-1][2] for p in b[2]]
    l0,l1=map(geometry,raw)
    z0,z1=map(lambda g:rp(D.resultant(g,'d')),(l0,l1))
    assert z0.degree()==51 and z1.degree()==75
    h=monic(z0.gcd(z1))
    fs=h.factor()[1]
    assert h.degree()==27 and sorted((f.degree(),m) for f,m in fs)==[(1,3),(4,3),(12,1)]
    assert monic(next(f for f,m in fs if f.degree()==1))==qp([0,1])
    assert monic(next(f for f,m in fs if f.degree()==4))==FR
    bv,_,_=number_field(FR)
    assert not bv(b[3][0]*b[-1][3])
    F=monic(next(f for f,m in fs if f.degree()==12))
    bv,ev,gcd=number_field(F)
    G=gcd(bv(D),gcd(bv(l0),bv(l1)))
    assert len(G)==2 and G[1]==qp([1])
    d=-G[0]
    _,zn,zd,u,_,_=atZero()
    assert all(ev(f,d).is_zero() for f in (D,l0,l1,zn,zd,u,-zn*at(V,zero)))
    print('left raw slopes: projections 51,75 and joint 27; a^3, F4^3, degree12.')
    print('left degree12: exact common d-gcd linear, z_D=z_N=S=U=0.')

def replay():
    D,geo=diagonal_width('o')
    assert D.degrees()==(10,8) and geo==(1,1,3,0)
    b=base('o')
    F=right_proof(D,b)
    left_proof(D,b,F)
    print('both initial-slope masks excluded; remaining fixed-moment and affine masks separate')

if __name__=='__main__':
    replay()
