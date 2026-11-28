#!/usr/bin/env python3
"""Exact rational right-initial-slope mask replay. Requires python-flint 0.9+."""
import flint

A=flint.fmpq_mpoly_ctx.get(('a','d','X'))
R=flint.fmpq_mpoly_ctx.get(('a','d'))
a,d,X=A.gens()
aa,dd=R.gens()
one=R.from_dict({(0,0):1})
zero=R.from_dict({})
azero=A.from_dict({})
qp=flint.fmpq_poly

def prim(f):
    return A.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in f.to_dict().items()})

def integrate(f,s=0):
    out={}
    for (i,j,k),v in f.to_dict().items():
        out[(i,j)]=out.get((i,j),0)+v/(k+s+1)
    return R.from_dict(out)

def embed(f):
    return A.from_dict({(i,j,0):c for (i,j),c in f.to_dict().items()})

def at(f,y):
    return sum((R.from_dict({(i,j):c})*y**k for (i,j,k),c in f.to_dict().items()),zero)

def dot(l,r):
    return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)

N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]

geometry=(aa,dd,dd-1,aa-dd)

def deflate(f):
    assert not f.is_zero()
    powers=[]
    for g in geometry:
        n=0
        while (f%g).is_zero():
            f=f//g
            n+=1
        powers.append(n)
    return f,tuple(powers)

def univariate(f):
    assert f.degrees()[1]==0
    c=f.to_dict()
    return qp([c.get((i,0),0) for i in range(f.degrees()[0]+1)])

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
    W=X**2*(X-a)**2
    V=(1-X)**2*(X-d)**2
    P=prim(W)
    Q=embed(at(prim(V),one))-prim(V)
    H=integrate(P*V)
    C1=integrate(P*V,1)
    C2=integrate(W*Q,1)
    J=integrate(P*Q)
    assert H==integrate(W*Q) and J==C1-C2
    I0,I1,I2=[integrate(W*V,j) for j in range(3)]
    xD=H*I1-C1*I0
    xN=H*I2-C1*I1
    S=(dd*xD-xN)*at(W,dd)
    U=C2*xD-H*xN
    p0=at(P,aa)
    q0=at(Q,dd)
    L9hat=[U*p0*dd**(j+1)+(J*S-U*at(P,dd))*aa**(j+1) for j in range(5)]
    Rdorm=[(1-dd)*dd**j for j in range(5)]
    D, dp=deflate(210*dot(L9hat,Rdorm)-S*p0*q0)
    assert D.degrees()==(8,13) and dp==(3,1,1,1)
    L0=[one,zero,zero,zero,zero]
    La=[(j+1)*aa**j for j in range(5)]
    # The removed R9 factor is 1-d, already live (the right plateau width).
    dr=[dd**j for j in range(5)]
    l0,l1=[dot(u,dr) for u in (L0,La)]
    L7hat=[l1*u-l0*v for u,v in zip(L0,La)]
    R1=[one]*5
    Rd=[dd**j-((1-dd)*j*dd**(j-1) if j else zero) for j in range(5)]
    s0,f0=deflate(dot(L7hat,R1))
    s1,f1=deflate(dot(L7hat,Rd))
    r0=univariate(D.resultant(s0,'d'))
    r1=univariate(D.resultant(s1,'d'))
    assert [r0.degree(),r1.degree()]==[63,87]
    h=monic(r0.gcd(r1))
    expect=[monic(qp(hh)) for hh in (CUBIC,LEFT,RIGHT)]
    factors=[(monic(g),m) for g,m in h.factor()[1]]
    assert h==expect[0]*expect[1]*expect[2]
    assert len(factors)==3 and all((u,1) in factors for u in expect)
    print('exact geometry deflation powers (a,d,d-1,a-d)',dp,f0,f1)
    print('right slope resultants degrees',r0.degree(),r1.degree(),
          'common exact irreducible degrees', [f.degree() for f in expect])
    for k,F in enumerate(expect):
        bv,av,gcd=number_field(F)
        G=gcd(bv(D),gcd(bv(s0),bv(s1)))
        assert len(G)==2 and G[1]==qp([1])
        dv=-G[0]
        z=lambda f:av(f,dv).is_zero()
        assert all(z(f) for f in (D,s0,s1))
        if k==0:
            assert z(dd-1)
            print('cubic: linear d gcd, d=1')
        if k==1:
            assert z(l0) and z(l1)
            print('first degree 12: linear d gcd, both left slopes zero')
        if k==2:
            assert not any(z(f) for f in (aa,dd,dd-1,aa-dd,l0,l1,H,J))
            assert all(z(f) for f in (xD,xN,S,U))
            assert z(I0*I2-I1**2)
            print('second degree 12: linear d gcd, x_D=x_N=S=U=0 and variance zero')
    print('all 3 right-initial-slope fibers excluded by live geometry, left mask, or nonzero variance')

if __name__=='__main__':
    replay()
