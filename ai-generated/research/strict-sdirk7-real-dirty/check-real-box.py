#!/usr/bin/env python3
"""An exact outward-rounded rational contraction certificate. No numerical library."""
from fractions import Fraction as Q
from itertools import permutations
from math import prod

N = 5
S = 10**90
RADIUS = Q(1, 10**30)
CENTER = tuple(map(Q, (
    "-13.47182912965382985896954070588903942474935511356358646252600203248228",
    "-11.89349984962544281030782735828012421421779092385160761494607481816721",
    "-6.200238104922317626627154015489541320295073451133262417241371449511067",
    "4.678524214801460324276532725274503284021361216733282671013889956245341",
    "-0.8374522555317752676818774628394868868425585534354665520619860763341525",
)))


def ceil(a, b):
    return -((-a) // b)


class I:
    """Closed interval whose endpoints are integers divided by S."""
    __slots__ = ("l", "u")

    def __init__(self, a=0, b=None, raw=False):
        if raw:
            self.l, self.u = a, b
        else:
            if isinstance(a, I):
                self.l, self.u = a.l, a.u
            else:
                b = Q(a if b is None else b)
                a = Q(a)
                self.l = (S*a.numerator)//a.denominator
                self.u = ceil(S*b.numerator, b.denominator)
        assert self.l <= self.u

    def __add__(a, b):
        b = I(b)
        return I(a.l+b.l, a.u+b.u, raw=True)

    __radd__ = __add__

    def __neg__(a):
        return I(-a.u, -a.l, raw=True)

    def __sub__(a, b):
        return a + (-I(b))

    def __rsub__(a, b):
        return I(b) + (-a)

    def __mul__(a, b):
        b = I(b)
        xs = (a.l*b.l, a.l*b.u, a.u*b.l, a.u*b.u)
        return I(min(xs)//S, ceil(max(xs), S), raw=True)

    __rmul__ = __mul__

    def __truediv__(a, b):
        b = I(b)
        assert b.nz(), "division not certified"
        xs = [(S*x, y) for x in (a.l,a.u) for y in (b.l,b.u)]
        return I(min(x//y for x,y in xs), max(ceil(x,y) for x,y in xs), raw=True)

    def __rtruediv__(a, b):
        return I(b)/a

    def __pow__(a, n):
        assert n>=0
        if n==0:
            return I(1)
        return a*(a**(n-1))

    def nz(a):
        return a.l>0 or a.u<0

    def mid(a):
        return Q(a.l+a.u, 2*S)

    def ub(a):
        return Q(max(abs(a.l), abs(a.u)), S)

    def lo(a):
        """Lower bound on absolute value (zero if the interval meets zero)."""
        return Q(0 if not a.nz() else min(abs(a.l),abs(a.u)),S)


class Jet:
    """First derivatives enclosed alongside a rational interval value."""
    __slots__ = ("v","g")

    def __init__(self, v, g=None):
        if isinstance(v, Jet):
            self.v,self.g=v.v,v.g
        else:
            self.v=I(v)
            self.g=[I(0) for _ in range(N)] if g is None else g

    def __add__(a,b):
        b=Jet(b)
        return Jet(a.v+b.v,[x+y for x,y in zip(a.g,b.g)])

    __radd__=__add__

    def __neg__(a):
        return Jet(-a.v,[-x for x in a.g])

    def __sub__(a,b):
        return a+(-Jet(b))

    def __rsub__(a,b):
        return Jet(b)+(-a)

    def __mul__(a,b):
        b=Jet(b)
        return Jet(a.v*b.v,[x*b.v+a.v*y for x,y in zip(a.g,b.g)])

    __rmul__=__mul__

    def __truediv__(a,b):
        b=Jet(b)
        v=a.v/b.v
        return Jet(v,[(x-v*y)/b.v for x,y in zip(a.g,b.g)])

    def __rtruediv__(a,b):
        return Jet(b)/a

    def __pow__(a,n):
        assert n>=0
        if n==0:
            return Jet(1)
        return Jet(a.v**n,[n*(a.v**(n-1))*x for x in a.g])


def det(A):
    n=len(A)
    return sum((-1)**sum(i>j for t,i in enumerate(p) for j in p[t+1:])
               *prod(A[i][j] for i,j in enumerate(p)) for p in permutations(range(n)))


def hull(xs):
    r=[1]
    for x in xs:
        r=[-x*r[0]]+[r[j-1]-x*r[j] for j in range(1,len(r))]+[r[-1]]
    return r


def evaluate(X):
    """The five defining residuals, plus every required pivot and exactness test."""
    z,a,b,c,h=X
    y=[a,b,c,Jet(4),Jet(0),Jet(1)]
    P=lambda f:sum(z**j*g/(j+1) for j,g in enumerate(f))
    K=[P(hull(y[:i]+y[i+1:])) for i in range(6)]
    b=[k/prod(x-t for j,t in enumerate(y) if j!=i)
       for i,(x,k) in enumerate(zip(y,K))]
    U0=-h*K[4]
    U1=-(1-h)*K[5]/2
    W=lambda y:U0+(U1-U0)*y
    D=[bb*(W(yi)/ki)/(yi-h) for yi,ki,bb in zip(y,K,b)]
    d3=-sum(D)
    v=[W(yi)/ki for yi,ki in zip(y,K)]
    v3=-sum(di*vi for di,vi in zip(D,v))/d3
    w=z-h
    x2=Q(3,2)
    g2=Q(7,4)
    eta_den=(x2-w)-g2*(1-w)
    eta=((x2-w)*x2-g2*(1-w))/eta_den
    q=lambda t:(t-w)*(t-eta)
    QI=lambda t:t**3/3-(w+eta)*t*t/2+w*eta*t
    fun=[P(hull(y)), W(4)-(4-h)*K[3],
         2*(c+3)*D[2]/b[2]+c**3-9*c*c+18*c-6,
         sum(bi*vi*vi for bi,vi in zip(b,v)),
         q(z-a)-QI(z-a)+QI(w)*v[0]/v3]
    reverse_minor=det([b[2:],[t*x for t,x in zip(b[2:],y[2:])],
        [t*x*x for t,x in zip(b[2:],y[2:])],D[2:]])
    head_minor=det([[1,1,1],[1,x2,w],[1,g2,0]])
    k=w*w-4*w+2
    cubic_at_3=(w-1-k)+k*g2
    bush=8*sum(t*((z-x)/z)**7 for t,x in zip(b,y))-1
    pivots=dict(z=z,d3=d3,v3=v3,eta_den=eta_den,first_q=q(z-a),
                head_minor=head_minor,reverse_minor=reverse_minor,
                visible_v=v[0],cubic_at_3=cubic_at_3,bush=bush)
    for i in range(6):
        pivots[f"b{i}"]=b[i]
        pivots[f"h-gap{i}"]=y[i]-h
        for j in range(i):
            pivots[f"gap{j}{i}"]=y[i]-y[j]
    return fun,pivots


def inverse(A):
    n=len(A)
    a=[r[:]+[Q(j==i) for j in range(n)] for i,r in enumerate(A)]
    for i in range(n):
        j=next(j for j in range(i,n) if a[j][i])
        a[i],a[j]=a[j],a[i]
        p=a[i][i]
        a[i]=[x/p for x in a[i]]
        for j in range(n):
            if j!=i:
                v=a[j][i]
                a[j]=[s-v*t for s,t in zip(a[j],a[i])]
    return [r[n:] for r in a]


def matmul(A,B):
    return [[sum(x*y for x,y in zip(r,col)) for col in zip(*B)] for r in A]


def jets(radius):
    return [Jet(I(x-radius,x+radius),[I(j==i) for j in range(N)])
            for i,x in enumerate(CENTER)]


def main():
    value,_=evaluate(jets(Q(0)))
    enclosure,pivots=evaluate(jets(RADIUS))
    # Rational preconditioner; intervals are used only to enclose its products.
    Y=inverse([[v.mid() for v in f.g] for f in value])
    C=[[I(x) for x in r] for r in Y]
    Z=matmul(C,[f.g for f in enclosure])
    L=max(sum((I(i==j)-x).ub() for j,x in enumerate(r)) for i,r in enumerate(Z))
    off=max(r[0].ub() for r in matmul(C,[[f.v] for f in value]))
    assert L<Q(1,10**18)
    assert off<RADIUS/Q(10**18)
    assert off+L*RADIUS<RADIUS
    # These include all assembly inverses plus a specific visible defect,
    # a demonstrably unpaid axis, and the order-eight bush obstruction.
    assert all(Jet(v).v.lo()>Q(1,10**5) for v in pivots.values())
    assert Jet(pivots['bush']).v.l>0 or Jet(pivots['bush']).v.u<0
    bu=Jet(pivots['bush']).v
    print("verified: infinity-norm derivative < 10^-18")
    print("verified: preconditioned center residual < 10^-48")
    print("verified: all assembly/visibility pivots have magnitude > 10^-5")
    print("eighth bush scaled residual in", bu.l, bu.u, "times 10^-90")
    print("unique nonsingular exact real zero in the stated radius-10^-30 box")


if __name__=='__main__':
    main()
