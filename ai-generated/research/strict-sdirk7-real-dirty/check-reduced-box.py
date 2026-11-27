#!/usr/bin/env python3
"""Independent three-variable elimination and real-tableau enclosure replay."""
from fractions import Fraction as Q
from math import isqrt, prod
from functools import lru_cache
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path

spec=spec_from_file_location("outer_box",Path(__file__).with_name("check-real-box.py"))
m=module_from_spec(spec)
spec.loader.exec_module(m)
I,Jet,center=m.I,m.Jet,m.CENTER
base=(center[0],center[3],center[1]+center[2])
radius=Q(1,10**35)


def sqroot(v):
    assert v.v.l>0
    s=m.S
    b=I(isqrt(s*v.v.l),1+isqrt(s*v.v.u),raw=True)
    return Jet(b,[d/(2*b) for d in v.g])


def rational_chart(X):
    z,c,s=X
    moment=[z**i/(i+1) for i in range(7)]
    integrate=lambda P,k=0:sum(a*moment[j+k] for j,a in enumerate(P))
    R=m.hull([0,1,4,c])
    p=(s*integrate(R,1)-integrate(R,2))/integrate(R)
    disc=sqroot(s*s-4*p)
    a,b=(s-disc)/2,(s+disc)/2
    ys=[a,b,c,Jet(4),Jet(0),Jet(1)]
    pols=[m.hull(ys[:i]+ys[i+1:]) for i in range(6)]
    K=[integrate(f) for f in pols]
    h=(4*K[3]+2*K[5])/(K[3]+3*K[4]+2*K[5])
    h5=(z,a,b,c,h)
    W0=-h*K[4]
    W1=-(1-h)*K[5]/2
    W=lambda x:W0+(W1-W0)*x
    lam=[1/prod(yi-yj for j,yj in enumerate(ys) if i!=j) for i,yi in enumerate(ys)]
    beta=[x*y for x,y in zip(K,lam)]
    D=[l*W(y)/(y-h) for y,l in zip(ys,lam)]
    v=[W(y)/f for y,f in zip(ys,K)]
    d0=-sum(D)
    v0=-sum(x*y for x,y in zip(D,v))/d0
    w=z-h
    eta=(w+2)/(3*w-1)
    q=lambda x:(x-w)*(x-eta)
    Jq=lambda x:x**3/3-(w+eta)*x**2/2+w*eta*x
    f1=2*(c+3)*W(c)+(c**3-9*c**2+18*c-6)*(c-h)*K[2]
    f2=sum(l*W(y)**2/f for y,l,f in zip(ys,lam,K))
    f3=(q(z-a)-Jq(z-a))*v0+Jq(w)*v[0]
    out=(z,ys,beta,D,v,v0,w,eta)
    return (f1,f2,f3),h5,out


def verify_box():
    make=lambda r:[Jet(I(x-r,x+r),[I(i==j) for j in range(5)]) for i,x in enumerate(base)]
    fc,_,_=rational_chart(make(0))
    fb,other,data=rational_chart(make(radius))
    inv=m.inverse([[u.mid() for u in f.g[:3]] for f in fc])
    Y=[[I(x) for x in r] for r in inv]
    P=m.matmul(Y,[f.g[:3] for f in fb])
    q=max(sum((I(i==j)-s).ub() for j,s in enumerate(r)) for i,r in enumerate(P))
    off=max(x[0].ub() for x in m.matmul(Y,[[f.v] for f in fc]))
    assert q<Q(1,10**18) and off<radius*Q(1,10**15)
    assert q*radius+off<radius
    for a,b in zip(other,center):
        assert (a.v-I(b)).ub()<m.RADIUS
    return data


def cramer(M,y):
    d=m.det(M)
    assert d.nz()
    return [m.det([r[:j]+[w]+r[j+1:] for r,w in zip(M,y)])/d for j in range(len(y))]


def tableau(data):
    z,Y,b,D,v,v0,w,eta=data
    z,Y,b,D,v,v0,w,eta=z.v,[a.v for a in Y],[a.v for a in b],[a.v for a in D], \
        [a.v for a in v],v0.v,w.v,eta.v
    x=[z-y for y in Y]
    q=lambda t:(t-w)*(t-eta)
    Jq=lambda t:t**3/3-(w+eta)*t**2/2+w*eta*t
    qx=list(map(q,x))
    goal=[Jq(t)-Jq(w)*vi/v0 for t,vi in zip(x,v)]
    rows=[b,[w*y for w,y in zip(b,Y)],[w*y*y for w,y in zip(b,Y)],D]
    target=lambda j:(b[j]*Y[j],b[j]*Y[j]**2/2-D[j],
                     b[j]*Y[j]**3/3-(1+Y[j]/3)*D[j],
                     (1+(1-Y[j])/2)*D[j])
    B=[[I(i==j) for j in range(6)] for i in range(6)]
    B[1][0]=(goal[1]-qx[1])/qx[0]
    for j in range(5):
        ks=list(range(max(j+1,2),6))
        rs=rows[:len(ks)]
        ans=cramer([[r[k] for k in ks] for r in rs],
                   [y-r[j]-(r[1]*B[1][0] if j==0 else 0) for r,y in zip(rs,target(j))])
        for k,a in zip(ks,ans):
            B[k][j]=a
    t=I(Q(1,2))
    k=w*w-4*w+2
    A=[[I(0) for _ in range(9)] for _ in range(9)]
    A[0][0]=A[1][1]=A[2][2]=I(1)
    A[1][0]=t
    A[2][0]=w-1-k
    A[2][1]=k
    g2=I(Q(7,4))
    d=A[2][0]+k*g2
    for i in range(6):
        H=cramer([[I(1),I(1),I(1)],[I(1),1+t,w],[I(1),g2,I(0)]],
            [x[i]-sum(B[i]),x[i]**2/2-sum(a*w for a,w in zip(B[i],x)),d*v[i]/v0])
        A[i+3]=H+B[i]
    return [[x/z for x in r] for r in A],[I(0)]*3+b


@lru_cache(None)
def trees(n):
    if n==1:
        return ((),)
    classes=[(k,t) for k in range(1,n) for t in trees(k)]
    def gen(left,start):
        if left==0:
            yield ()
        else:
            for j in range(start,len(classes)):
                k,t=classes[j]
                if k>left:
                    break
                for u in gen(left-k,j):
                    yield (t,)+u
    return tuple(gen(n-1,0))


@lru_cache(None)
def mass(t):
    out=[mass(u) for u in t]
    n=1+sum(a for a,b in out)
    return n,n*prod(b for a,b in out)


def check_all_trees(A,b):
    @lru_cache(None)
    def phi(t):
        return [prod(sum(w*a for w,a in zip(r,phi(u))) for u in t) for r in A]
    def residual(t):
        return mass(t)[1]*sum(a*w for a,w in zip(phi(t),b))-1
    bounds=[residual(t) for k in range(1,8) for t in trees(k)]
    assert len(bounds)==85
    assert all(r.l<=0<=r.u and r.ub()<Q(1,10**18) for r in bounds)
    bush=residual(((),)*7)
    assert bush.l>0
    return bush


def main():
    data=verify_box()
    A,b=tableau(data)
    bush=check_all_trees(A,b)
    print("independent three-coordinate exact contraction verifies the same real root")
    print("all 85 independently reconstructed tree residual enclosures contain zero with absolute bound <10^-18")
    print("independent eighth-bush residual enclosure strictly positive")
    print("enclosure replay checks the construction; exact order uses the symbolic unit-pivot proof")


if __name__=="__main__":
    main()
