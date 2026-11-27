#!/usr/bin/env python3
"""Exact Hensel certificates for split DIRK10 front/suffix clocks over Q_11.

The witness is only for the necessary clock equations, not an order tableau.
All ball centers are rational and all radii stand for lower bounds on the
11-adic valuation of an exact error. A Hensel point uses a simple root at
a finite chart, possibly after translating, dilating, or inverting X.
"""
from fractions import Fraction as Q
from math import prod, inf, comb

P = 11
CAP = 55


def v(x):
    x = Q(x)
    if not x:
        return inf
    a,b,n = x.numerator,x.denominator,0
    while a%P==0:
        a//=P
        n+=1
    while b%P==0:
        b//=P
        n-=1
    return n


def r(x, M=None):
    M=P if M is None else M
    x=Q(x)
    return x.numerator*pow(x.denominator,-1,M)%M


class Ball:
    def __init__(self, x=0, prec=inf):
        self.x, self.prec = Q(x),prec

    @staticmethod
    def cast(a):
        return a if isinstance(a,Ball) else Ball(a)

    def __neg__(self):
        return Ball(-self.x,self.prec)

    def __add__(self,a):
        a=self.cast(a)
        return Ball(self.x+a.x,min(self.prec,a.prec))

    __radd__=__add__

    def __sub__(self,a):
        return self+-self.cast(a)

    def __rsub__(self,a):
        return self.cast(a)+-self

    def __mul__(self,a):
        a=self.cast(a)
        return Ball(self.x*a.x,min(self.prec+v(a.x),a.prec+v(self.x),self.prec+a.prec))

    __rmul__=__mul__

    def nonzero(self):
        return v(self.x)<self.prec

    def inverse(self):
        assert self.nonzero(), ("zero not excluded",self)
        return Ball(1/self.x,self.prec-2*v(self.x))

    def __truediv__(self,a):
        return self*self.cast(a).inverse()

    def __rtruediv__(self,a):
        return self.cast(a)*self.inverse()

    def __pow__(self,n):
        if n<0:
            return self.inverse()**(-n)
        return prod((self for _ in range(n)),start=Ball(1))

    def lower(self):
        return min(self.prec,v(self.x))

    def residue(self):
        assert self.prec>=1 and v(self.x)>=0
        return r(self.x)

    def fingerprint(self):
        assert self.nonzero()
        val=v(self.x)
        return (val,r(self.x*Q(P)**(-val)))

    def __repr__(self):
        if self.nonzero():
            return str(self.fingerprint())
        return "0+"+str(P)+"^"+str(self.prec)


def polyscale(a,c):
    return [c*x for x in a]


def polyadd(a,b):
    return [(a[i]if i<len(a)else 0)+(b[i]if i<len(b)else 0)
            for i in range(max(len(a),len(b)))]


def polymul(a,b):
    q=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            q[i+j]+=x*y
    return q


def ev(a,x):
    y=0
    for c in reversed(a):
        y=x*y+c
    return y


def deriv(a):
    return [i*x for i,x in enumerate(a)if i]


def shift(a,d,b):
    return [sum(x*comb(i,j)*d**(i-j)*b**j for i,x in enumerate(a)if i>=j)
            for j in range(len(a))]


def polydiv_monic(a,b):
    # In all uses b[-1] is literally one, so no division uncertainty.
    A=a[:]
    q=[0]*(len(a)-len(b)+1)
    while len(A)>=len(b):
        j=len(A)-len(b)
        q[j]=A[-1]
        for k,c in enumerate(b[:-1]):
            A[j+k]-=q[j]*c
        A.pop()
    return q,A


def normalize(cs):
    if not any(c.nonzero()for c in cs):
        return None
    m=min(c.lower()for c in cs)
    if not any(c.lower()==m and c.nonzero()for c in cs):
        return None
    return polyscale(cs,Q(P)**(-m))


def simple_root(cs,root):
    cs=list(map(Ball.cast,cs))
    n=min(CAP,min(a.prec for a in cs))
    assert n>=1 and all(a.lower()>=0 for a in cs)
    M=P**n
    p=[r(a.x,M) for a in cs]
    d=deriv(p)
    assert ev(p,root)%P==0 and ev(d,root)%P
    i,x=1,root
    while i<n:
        i=min(2*i,n)
        M=P**i
        x=(x-ev(p,x)*pow(ev(d,x)%M,-1,M))%M
    assert ev(p,x)%M==0
    return Ball(x,n)


def finite_roots(cs, depth, only=None):
    cs=normalize(cs)
    if cs is None or min(a.prec for a in cs)<1:
        return []
    rs=[a.residue()for a in cs]
    ds=deriv(rs)
    out=[]
    for q in range(P) if only is None else [only]:
        if ev(rs,q)%P:
            continue
        if ev(ds,q)%P:
            out.append(simple_root(cs,q))
        elif depth:
            for x in finite_roots(shift(cs,q,P),depth-1):
                out.append(q+P*x)
    return out


def roots(cs):
    a=finite_roots(cs,8)
    for zz in finite_roots(cs[::-1],8,0):
        a.append(zz.inverse()) # assert the pole root is finite, not infinity
    assert len(a)==len(cs)-1
    assert all((x-y).nonzero() for i,x in enumerate(a) for y in a[:i])
    return a


def early_in_t(s):
    return [420*s**4-1008*s**3+1008*s*s-504*s+108,
            -168*s*s+252*s-108,33-28*s,-3]


def early_in_s(t):
    return [108-108*t+33*t*t-3*t**3,-504+252*t-28*t*t,
            1008-168*t,-1008,420]


def coeff(s,t):
    r0=(t-6)/s**3
    z0=2*(756*s**3+336*s*s*t-2016*s*s+56*s*t*t
          -609*s*t+1638*s+6*t**3-81*t*t+351*t-486)/(5*s**4*(2*t-3))
    e=12*(252*s**3+112*s*s*t-672*s*s+42*s*t*t-378*s*t+756*s+
          2*t**3-37*t*t+192*t-252)/(5*s**3*(2*t-3))
    f=168-4*t*z0
    return r0,z0,e,f


def front(s,t,scaled=False):
    r0,z0,e,f=coeff(s,t)
    N=s/(5*(3-2*t))
    B0=10*(3-2*t)
    # L_k=(k+4)((k-1)B-1/5), w_D=z(k+4)/5-168(k-1)B.
    if scaled:
        # variable κ=t*k, L stores t*L_k and U stores t*U_k
        L=polymul([4*t,1],[-t/B0-Q(1,5),1/B0])
        U=[-s-t*N,N]
        yd=[4*t*z0-168,z0]
        yn=[e,-r0]
        wd=[4*t*z0/5+168*t/B0,z0/5-168/B0]
        wn=polyscale(L,r0)
    else:
        r_,z,B=t*r0,t*z0,t/B0
        L=polymul([4,1],[-B-Q(1,5),B])
        U=[-s/t-N,N]
        yd=[4*z-168,z]
        yn=[e,-r_]
        wd=[4*z/5+168*B,z/5-168*B]
        wn=polyscale(L,r_)
    return polyadd(polymul(yd,U),polyscale(polymul(yn,L),-1)),(yn,yd,wn,wd),(e,f)


PHI=[1,-14,56,-84,42]
MOMENT_INV=[[300,-2100,4200,-2520],[-2100,16800,-36120,22680],
            [4200,-36120,81480,-52920],[-2520,22680,-52920,35280]]


def tail(s,t,y,w,M):
    moments=[(6-3*t)*(6-t)*(3-t),2*s*(6-t)*(3-t),3*s*s*(6-t),12*s**3]
    q=polymul([1,-1], [sum(a*b for a,b in zip(row,moments))for row in MOMENT_INV])
    mq=polymul(M,q)
    ly,lw=-ev(mq,y)/ev(PHI,y),-ev(mq,w)/ev(PHI,w)
    slope=(ly-lw)/(y-w)
    nod=polyadd(mq,polymul(PHI,[lw-slope*w,slope]))
    sf,rem=polydiv_monic(nod,polymul([-y,1],[-w,1]))
    # The exact remainder is zero by the two interpolation equations and y≠w.
    assert all(a.lower()>1 for a in rem)
    assert len(sf)==4 and sf[-1].nonzero()
    return sf


def ensure_geometry(s,t,k,forward_data,M):
    yn,yd,wn,wd=[ev(f,k)for f in forward_data]
    y,w=yn/yd,wn/wd
    u=s/t
    Q0=roots([s*s/(6-t),-s,Ball(1)])
    R=roots(tail(s,t,y,w,M))
    A=list(map(Ball.cast,[0,*Q0,u,y,w,*R,1]))
    assert len(A)==10 and all((x-z).nonzero()for i,x in enumerate(A)for z in A[:i])
    assert all(ev(M,c).nonzero()and ev(PHI,c).nonzero()for c in A)
    assert all(x.nonzero()for x in M)
    assert (M[0]+M[1]).nonzero()
    print("  (s,t,k) fingerprints",s.fingerprint(),t.fingerprint(),k.fingerprint())
    print("  exterior positions",A,"minimum absolute precision",min(x.prec for x in A))
    return A


def witness_06():
    print("class (0,6)")
    s=Ball(121)
    t=simple_root(early_in_t(s),6)
    assert (t-6).fingerprint()==(6,5)
    F,U,M=front(s,t)
    k=simple_root(F,7)
    assert (k+4).fingerprint()==(2,3)
    assert (k-1).nonzero()
    A=ensure_geometry(s,t,k,U,M)
    assert sorted(x.fingerprint()for x in A[6:9])==[(-1,1),(0,4),(0,6)]


def witness_88():
    print("class (8,8)")
    h=Ball(11)
    s=Q(2,3)+h
    t=simple_root(early_in_t(s),8)
    F,U,M=front(s,t)
    k=3+h*simple_root(polyscale(shift(F,3,h),h**(-2)),3)
    assert (k-1).nonzero()
    A=ensure_geometry(s,t,k,U,M)
    assert sorted(x.fingerprint()for x in A[6:9])==[(-2,9),(0,1),(0,4)]


def witness_90():
    print("class (9,0)")
    t=Ball(88)
    s=simple_root(early_in_s(t),9)
    F,U,M=front(s,t,scaled=True)
    kappa=simple_root(F,10)
    assert ((kappa/t)-1).nonzero()
    A=ensure_geometry(s,t,kappa,U,M) # tap polynomials in κ, not k
    assert sorted(x.fingerprint()for x in A[6:9])==[(0,2),(0,6),(0,6)]



def fourth_unit(x):
    assert x.nonzero()
    l=v(x.x)
    if l%4:
        return False
    u=x*Q(P)**(-l)
    if P==2:
        assert u.prec>=4
        return r(u.x,16)==1
    from math import gcd
    return pow(u.residue(),(P-1)//gcd(P-1,4),P)==1


def some_roots(cs,depth=9):
    cs=list(map(Ball.cast,cs))
    out=finite_roots(cs,depth)
    for z in finite_roots(cs[::-1],depth,0):
        if z.nonzero():
            out.append(z.inverse())
    return out


def ensure_positive_class(A,t):
    ratio=A[1]/A[2]
    assert fourth_unit(ratio/3) or fourth_unit(1/(3*ratio))
    assert fourth_unit((5*t-3)/27)


def witness_bad_prime(p,x):
    global P,CAP
    P,CAP=p,80
    print("positive-class local witness at", p)
    ratio=3*x**4
    t=Ball(4-ratio-1/ratio)
    assert fourth_unit((5*t-3)/27)
    for s in some_roots(early_in_s(t),7):
        if not all(z.nonzero()for z in [s,t,t-6,2*t-3,s-t]):
            continue
        F,U,M=front(s,t)
        for k in some_roots(F,9):
            if not k.nonzero() or not (k-1).nonzero():
                continue
            try:
                A=ensure_geometry(s,t,k,U,M)
                ensure_positive_class(A,t)
            except (AssertionError,ValueError):
                continue
            return
    raise AssertionError("no witness recovered")


def witness_five():
    global P,CAP
    P,CAP=5,80
    print("positive-class local witness at", P)
    s=Ball(Q(2,3)+50)
    t=simple_root(early_in_t(s),4)
    F,U,M=front(s,t)
    k=simple_root(normalize(F),1)
    assert (k-1).nonzero()
    A=ensure_geometry(s,t,k,U,M)
    ensure_positive_class(A,t)


if __name__=="__main__":
    witness_06()
    witness_88()
    witness_90()
    print("Three exact Q_11 split-clock Hensel witnesses PASS (not tableaux)")
    witness_bad_prime(2,Q(13,19))
    witness_bad_prime(3,Q(1,2))
    witness_five()
    witness_bad_prime(7,Q(1,3))
    print("Exact positive-coset split-clock witnesses at 2,3,5,7 PASS")
