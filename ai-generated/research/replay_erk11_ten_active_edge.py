"""Exact q10 n10 ERK11 edge elimination. Requires python-flint only."""
import flint
from functools import reduce
R=flint.fmpq_mpoly_ctx.get(('a','d','X'))
S=flint.fmpq_mpoly_ctx.get(('a','d'))
a,d,X=R.gens()
h=a/2;e=(1+d)/2;b=1-d
W=X*(1-X)
A=(X-d)*(X-e)*(4*(h-d)*(h-e)*(X-h)+(a-d)*(a-e)*(X-a))
B=(X-a)*(X-h)*(4*(e-a)*(e-h)*(X-e)+(d-a)*(d-h)*(X-d))
fac=(X-a)*(X-d)
V=X**2*(X-a)**2;Vr=(1-X)**2*(X-d)**2
P=R.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in V.to_dict().items()})
Q_=R.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in Vr.to_dict().items()})
Q=R.from_dict({(i,j,0):sum(c for (ii,jj,k),c in Q_.to_dict().items() if (ii,jj)==(i,j)) for (i,j,_) in Q_.to_dict()})-Q_
# repeated (i,j,0) keys have the same complete sum.
def integ(p):
 out={}
 for (i,j,k),c in p.to_dict().items():out[(i,j)]=out.get((i,j),0)+c/(k+1)
 return S.from_dict(out)
def ev(p,U):
 out={}
 for (i,j,k),c in p.to_dict().items():out[(i,j,k)]=c
 T=sum(R.from_dict({(i,j,0):c})*U**k for (i,j,k),c in out.items())
 assert T.degrees()[2]<=0
 return S.from_dict({(i,j):c for (i,j,k),c in T.to_dict().items()})
ss,dd=S.gens();bb=1-dd
Ta=1-32*ss+216*ss**2-480*ss**3+330*ss**4
Tb=1-32*bb+216*bb**2-480*bb**3+330*bb**4
UU=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],
    [216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],
    [330,-9240,55440,-110880,69300]]
U=sum(c*ss**i*bb**j for i,r in enumerate(UU) for j,c in enumerate(r))
m=[tuple(integ(W*fac*K*X**j) for K in (A,B)) for j in range(4)]
L=tuple(integ((1-X)*(X-d)*P*K) for K in (A,B))
RR=tuple(integ(X*(X-a)*Q*K) for K in (A,B))
K00=ev(A,R.from_dict({}));K01=ev(B,R.from_dict({}))
K10=ev(A,R.from_dict({(0,0,0):1}));K11=ev(B,R.from_dict({(0,0,0):1}))
Kaa=ev(A,a);Kdd=ev(B,d)
assert ev(B,a).is_zero() and ev(A,d).is_zero()
def contact(u,v):
    # cubic K=u*A+v*B
    k0=u*K00+v*K01;k1=u*K10+v*K11
    ka=u*Kaa;kd=v*Kdd
    return ka*kd+Ta*k0*kd+Tb*ka*k1+U*k0*k1
def center(u,v):
    IL=u*L[0]+v*L[1];IR=u*RR[0]+v*RR[1]
    j0=integ(P*Q)
    return IL*IR-j0*(u*u*integ(W*fac*A*A)+2*u*v*integ(W*fac*A*B)+v*v*integ(W*fac*B*B))

from time import monotonic
r=ss-dd;s=2*ss-dd-1;t=ss-2*dd;v=ss-dd-1
G=r*s*t*v
# h-e=(a-d-1)/2. the four calibration cross differences are G/8.
u,v0=L[1],-L[0]
N=[(u*p+v0*q)//G for p,q in m]
assert all((u*p+v0*q) % G==0 for p,q in m)
ff=N[0]*N[2]-N[1]**2
gg=N[0]*N[3]-N[1]*N[2]
hh=contact(u,v0)//(ss*(dd-1)*G**2)
assert not contact(u,v0)%(ss*(dd-1)*G**2)

def rp(f,n=0):
 Z=flint.fmpq_poly([f.to_dict().get((i,0) if n==0 else (0,i),0) for i in range(f.degrees()[n]+1)])
 return Z

P=flint.fmpq_poly
from itertools import combinations

def exactfield(H):
    H=H/H[H.degree()]
    unit=P([1]);zero=P();av=P([0,1])
    def trim(w):
        while w and w[-1].is_zero():w.pop()
        return w
    def inv(x):
        s,t=x,H;u,v=unit,zero
        while t:
            q,r=divmod(s,t);s,t=t,r;u,v=v,(u-q*v)%H
        assert s.degree()==0 and s[0]!=0
        return (u/s[0])%H
    def monic(g):
        if not g:return g
        v=inv(g[-1]);return [(t*v)%H for t in g]
    def rem(f,g):
        f=f[:];w=inv(g[-1])
        while len(f)>=len(g):
            s=len(f)-len(g);c=(f[-1]*w)%H
            for i in range(len(g)-1):f[i+s]=(f[i+s]-c*g[i])%H
            f.pop();trim(f)
        return f
    def gcd(f,g):
        while g:f,g=g,rem(f,g)
        return monic(f)
    def at(f):
        B=f.to_dict();ad,bd=f.degrees()
        return trim([P([B.get((i,j),0) for i in range(ad+1)])%H for j in range(bd+1)])
    def linear(g):
        assert len(g)==2 and g[1]==unit
        return -g[0]
    def spec(f,dv):
        r=zero
        for t in reversed(at(f)):r=(r*dv+t)%H
        return r
    return at,gcd,inv,linear,spec

def replay():
    Aprojection=rp(ff.resultant(gg,'d'));Bprojection=rp(ff.resultant(hh,'d'))
    assert Aprojection.degree()==228 and Bprojection.degree()==250
    factors=Aprojection.gcd(Bprojection).factor()[1]
    assert [(q.degree(),k) for q,k in factors]==[(19,4)]
    H=factors[0][0]
    at,gcd,inv,linear,spec=exactfield(H)
    F=reduce(gcd,[at(p) for p in (ff,gg,hh)])
    zero_pair=gcd(at(L[0]),at(L[1]))
    dv=linear(zero_pair)
    assert F==[dv*dv%H,-2*dv,flint.fmpq_poly([1])]
    print('Live edge coefficient: exact projections 228/250; gcd H19^4, second-width gcd is the forbidden zero-pair square.',flush=True)

    projection=rp(L[0].resultant(L[1],'d'))
    assert projection.degree()==44
    pfs=projection.factor()[1]
    assert sorted((h.degree(),m) for h,m in pfs)==[(1,1),(6,1),(6,1),(6,1),(6,1),(19,1)]
    guards=(ss,dd-1,ss-dd,2*ss-dd-1,ss-2*dd,ss-dd-1)
    sought=None
    for H0,_ in pfs:
        at,gcd,_,linear,spec=exactfield(H0)
        Z=gcd(at(L[0]),at(L[1]))
        dv=linear(Z)
        if H0.degree()!=19:
            assert any(spec(g,dv).is_zero() for g in guards)
        else:
            assert H0/H0[19]==H/H[19]
            sought=H0
    assert sought is not None
    print('Zero edge coefficients: exact projection degree 44; five smaller factors violate literal calibration distinctness.',flush=True)
    p=31;C=flint.fmpz_mod_poly_ctx(p)
    modq=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
    Hp=C([modq(c) for c in sought.coeffs()])
    assert Hp.degree()==19 and Hp.is_irreducible()
    K=flint.fq_default_ctx(modulus=Hp/Hp[19],fq_type='FQ_NMOD')
    F=flint.fq_default_poly_ctx(K);D=F.gen();a0=K.gen()
    lift=lambda p:sum((K(modq(c))*a0**i*D**j for (i,j),c in p.to_dict().items()),F.zero())
    LL=[lift(x) for x in L]
    assert any(f.degree()==v.degrees()[1] for f,v in zip(LL,L))
    d0=LL[0].gcd(LL[1])
    assert d0.degree()==1
    dv=-d0[0]/d0[1]
    E=lambda v:lift(v)(dv)
    assert all(E(f)!=0 for f in guards)
    T=D
    mv=[E(x)+T*E(y) for x,y in m]
    F0=mv[0]*mv[2]-mv[1]**2
    F1=mv[0]*mv[3]-mv[1]*mv[2]
    k0=E(K00)+T*E(K01);k1=E(K10)+T*E(K11)
    ka=E(Kaa);kd=T*E(Kdd)
    F2=ka*kd+E(Ta)*k0*kd+E(Tb)*ka*k1+E(U)*k0*k1
    assert [f.degree() for f in (F0,F1,F2)]==[2,2,2]
    assert F0.gcd(F1).gcd(F2).degree()==0
    print('Degree-19 exceptional width retains degree at 31; its exact linear second width and three full quadratics give gcd 1.',flush=True)
    print('Both physical edge positions excluded by reflection.',flush=True)

if __name__=='__main__':
    replay()
