"""Exact coefficient-lift replay for the q10 n10 central dormant chart."""
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

from itertools import combinations
one=S.from_dict({(0,0):1});zero=S.from_dict({})
def quad(fn):
 x=fn(one,zero);z=fn(zero,one);y=fn(one,one)-x-z;return [x,y,z]
B0,B1,CEN=quad(lambda u,v:
 (u*m[0][0]+v*m[0][1])*(u*m[2][0]+v*m[2][1])-(u*m[1][0]+v*m[1][1])**2),quad(lambda u,v:
 (u*m[0][0]+v*m[0][1])*(u*m[3][0]+v*m[3][1])-(u*m[1][0]+v*m[1][1])*(u*m[2][0]+v*m[2][1])),quad(center)
CC=quad(contact)
assert all(t%(ss*(dd-1))==0 for t in CC)
CC=[t//(ss*(dd-1)) for t in CC]
def det3(x,y,z):
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])
def res2(x,y):
 a,b,c=x;d,e,f=y
 return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
GS=[ss,dd-1,ss-dd,2*ss-dd-1,ss-2*dd,ss-dd-1]
def clean(f):
 assert not f.is_zero()
 for g in GS:
  while (f%g).is_zero():
   f=f//g
 return f
M=[clean(det3(*v)) for v in combinations([B0,B1,CC,CEN],3)]
R01=clean(res2(B0,B1))
def project(f,g):
    r=f.resultant(g,'d')
    assert r.degrees()[1]==0
    co=r.to_dict()
    return flint.fmpq_poly([co.get((i,0),0) for i in range(r.degrees()[0]+1)])

def replay():
    assert R01.degrees()==(20,20)
    assert [f.degrees() for f in M]==[(16,16),(16,16),(17,17),(17,17)]
    P=[project(R01,M[j]) for j in (0,1,2)]
    assert [f.degree() for f in P]==[602,602,640]
    G=reduce(lambda f,g:f.gcd(g),P)
    fs=G.factor()[1]
    assert G.degree()==18 and [(h.degree(),k) for h,k in fs]==[(9,2)]
    H=fs[0][0]
    print('Exact width projections 602,602,640; gcd H9^2.',flush=True)
    p=61;C=flint.fmpz_mod_poly_ctx(p)
    red=lambda c:int(c.numerator)*pow(int(c.denominator),-1,p)%p
    Hg=C([red(c) for c in H.coeffs()])
    assert Hg.degree()==9 and Hg.is_irreducible()
    K=flint.fq_default_ctx(modulus=Hg/Hg[9],fq_type='FQ_NMOD')
    F=flint.fq_default_poly_ctx(K);D=F.gen();a0=K.gen()
    lift=lambda p:sum((K(red(c))*a0**i*D**j for (i,j),c in p.to_dict().items()),F.zero())
    tests=list(map(lift,[R01]+M))
    assert tests[0].degree()==20
    d0=reduce(lambda u,v:u.gcd(v),tests)
    assert d0.degree()==1
    dv=-d0[0]/d0[1]
    E=lambda f:lift(f)(dv)
    assert all(E(g)!=0 for g in GS)
    T=D
    pol=[sum((E(x)*T**j for j,x in enumerate(rr)),F.zero())
         for rr in (B0,B1,CC,CEN)]
    assert any(f.degree()==2 for f in pol)
    assert reduce(lambda x,y:x.gcd(y),pol).degree()==0
    print('Degree-9 width is irreducible at 61; second width has linear residue gcd; full quadratic profile gcd is 1.',flush=True)
    print('Physical 9 excluded.',flush=True)

if __name__=='__main__':
    replay()
