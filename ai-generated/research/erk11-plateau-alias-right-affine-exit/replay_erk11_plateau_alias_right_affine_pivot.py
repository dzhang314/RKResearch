#!/usr/bin/env python3
"""Both raw right-affine-pivot branches, exact rational replay. Requires python-flint 0.9+."""
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

def raw_affine(which,left,base0):
    L,T,ls,rs,xn,xd,zn,zd,g0=base0
    if left:
        a0,c0=aa,dd
        l0,l1=ls;xn,xd=xn,xd
        mat=[sum((N[i][j]*T[j] for j in range(5)),zero) for i in range(5)]
        es=sum((intoA(mat[i])*X**(i+1) for i in range(5)),A.from_dict({}))
    else:
        a0,c0=1-dd,1-aa
        l0,l1=rs;xn,xd=zd-zn,zd
        mat=[sum((L[i]*N[i][j] for i in range(5)),zero) for j in range(5)]
        es=sum((intoA(mat[i])*X*(1-X)**i for i in range(5)),A.from_dict({}))
    aA=intoA(a0); cA=intoA(c0)
    es_a=at(es,a0)
    num=aA**5*es-X**3*(6*X**2-15*aA*X+10*aA**2)*intoA(es_a)
    E,r=divmod(num,X*(X-aA));assert r.is_zero()
    Eco,Egc=reduce_cols(coords(E,3))
    E=sum((intoA(c)*X**j for j,c in enumerate(Eco)),A.from_dict({}))
    E0=Eco[0]
    h=aA/2
    B0=X*(X-aA)*(X-h)
    B1=(X-h)*(aA*intoA(l0)-intoA(l0-l1)*X)
    S0,r=divmod(-aA*intoA(E0)*B0,X);assert r.is_zero()
    S1,r=divmod(aA*(E*intoA(at(B1,zero))-intoA(E0)*B1),X);assert r.is_zero()
    phi=X**2*(aA-X)
    p=[phi,X*B0,X*B1,B0,B1]
    weight=X*(1-X)*(X-aA)*(X-cA)
    ms=[[int_(weight*z,j) for z in p] for j in range(3)]
    N0=[r[:3] for r in ms]
    DT=det3(N0)
    nn=[]
    for j in (3,4):
        cont=[]
        for i in range(3):
            cont.append(-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in ms]))
        nn.append(cont)
    oo=[hom3(v,xn,xd) for v in (aA*X*(X-aA)*intoA(E0),X*S0,X*S1,S0,S1)]
    GG=[sum((u*v for u,v in zip(C,oo[:3])),zero)+DT*oo[j] for C,j in zip(nn,(3,4))]
    return DT,GG

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

LEFT=[72,-3456,71496,-841392,6277059,-31362048,108028376,-259591392,
      433718388,-493307520,363884400,-156816000,29947500]
RIGHT=[144,-7344,163296,-2084400,16964631,-92707335,349502948,-918969660,
       1679022735,-2086868850,1680998550,-790614000,164711250]
CUBIC=[-4,54,-180,165]

def replay():
    D,geo=diagonal_width('d')
    assert D.degrees()==(8,13) and geo==(3,1,1,1)
    bs=base('d')
    delta,raw=raw_affine('d',False,bs)
    reduced,gamma=reduce_cols(raw)
    assert raw==[gamma*r for r in reduced]
    assert [f.degrees() for f in raw]==[(15,22),(18,27)]
    assert [f.degrees() for f in reduced]==[(10,13),(13,18)]
    G=geometry(gamma)
    assert G.degrees()==(5,6)
    ratio=gamma//G
    assert ratio==(dd-1)**3 or ratio==(1-dd)**3
    fs=G.factor()[1]
    assert sorted((f.degrees(),p) for f,p in fs)==[((2,3),1),((3,3),1)]
    f23=next(f for f,m in fs if f.degrees()==(2,3))
    f33=next(f for f,m in fs if f.degrees()==(3,3))
    assert (bs[3][0]%f33).is_zero()
    assert ((C1-dd*H)%f23).is_zero()
    print('common factor: live (d-1)^3 times two distinct factors (2,3),(3,3)')
    print('each factor directly forces C1=d*H (forbidden actual clock alias c10=d) or the right initial slope zero')
    S0,S1=[rp(D.resultant(g,'d')) for g in reduced]
    H0=monic(S0.gcd(S1))
    assert S0.degree()==230 and S1.degree()==309 and H0.degree()==54
    factors=H0.factor()[1]
    assert sorted((q.degree(),i) for q,i in factors)==[(1,8),(3,2),(8,2),(12,1),(12,1)]
    assert monic(next(f for f,m in factors if f.degree()==1))==qp([0,1])
    assert monic(next(f for f,m in factors if f.degree()==3))==monic(qp(CUBIC))
    Fleft=monic(qp(LEFT))
    assert any(monic(f)==Fleft for f,m in factors)
    _,xn,xd,u,_,_=atD()
    for F,m in sorted(factors,key=lambda pair:(pair[0].degree(),pair[1])):
        if F.degree()==1:
            print('reduced degree 1 (power 8): a=0')
            continue
        bv,atv,gcd=number_field(F)
        G=gcd(bv(D),gcd(bv(reduced[0]),bv(reduced[1])))
        assert len(G)==2 and G[1]==qp([1])
        d=-G[0]
        z=lambda q:atv(q,d).is_zero()
        assert z(D) and all(z(r) for r in reduced)
        if F.degree()==3:
            assert z(dd-1)
            print('reduced degree 3 (power 2): exact linear d gcd, d=1')
        elif F.degree()==8:
            assert z(H) and z(xd)
            print('reduced degree 8 (power 2): exact linear d gcd, H=x_D=0')
        elif monic(F)==Fleft:
            assert all(z(g) for g in bs[2])
            print('reduced first degree 12: exact linear d gcd, both left slopes zero')
        else:
            assert z(xd) and z(xn) and z(I0*I2-I1**2)
            print('reduced other degree 12: exact linear d gcd, x_D=x_N=variance=0')
    print('all raw right affine slopes excluded; no flank fit or finite place used')

if __name__=='__main__':
    replay()
