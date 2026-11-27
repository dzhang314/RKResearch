#!/usr/bin/env python3
"""Exact Laurent jets with tracked precision for the singular clock limits."""
from fractions import Fraction as Q
from math import inf, prod

MAX = 20


class Jet:
    def __init__(self, a=0, prec=inf):
        if isinstance(a,Jet):
            self.a,self.prec=a.a,a.prec
            return
        self.prec=prec
        d=a if isinstance(a,dict) else {0:a}
        self.a={i:Q(c) for i,c in d.items() if c and i<prec}

    def order(self):
        return min(self.a,default=self.prec)

    def c(self,i):
        assert i<self.prec, (i,self.prec)
        return self.a.get(i,Q(0))

    def __neg__(self):
        return Jet({i:-x for i,x in self.a.items()},self.prec)

    def __add__(self,a):
        a=Jet(a)
        p=min(self.prec,a.prec)
        return Jet({i:self.c(i)+a.c(i) for i in self.a.keys()|a.a.keys() if i<p},p)

    __radd__=__add__

    def __sub__(self,a):
        return self+-Jet(a)

    def __rsub__(self,a):
        return Jet(a)+-self

    def __mul__(self,a):
        a=Jet(a)
        p=min(self.prec+a.order(),a.prec+self.order(),MAX)
        d={}
        for i,x in self.a.items():
            for j,y in a.a.items():
                if i+j<p:
                    d[i+j]=d.get(i+j,0)+x*y
        return Jet(d,p)

    __rmul__=__mul__

    def inverse(self):
        assert self.a, (self.a,self.prec)
        j=self.order()
        p=min(int(self.prec-2*j) if self.prec!=inf else MAX,MAX)
        d={}
        for i in range(-j,p):
            d[i]=(int(i==-j)-sum(x*d.get(i+j-u,0) for u,x in self.a.items()if u>j))/self.a[j]
        return Jet(d,p)

    def __truediv__(self,a):
        return self*Jet(a).inverse()

    def __rtruediv__(self,a):
        return Jet(a)*self.inverse()

    def __pow__(self,n):
        if n<0:return self.inverse()**(-n)
        return prod((self for _ in range(n)),start=Jet(1))

    def match(self, coeff, upto):
        assert self.prec>=upto
        assert {i:c for i,c in self.a.items()if i<upto}=={i:Q(c)for i,c in coeff.items()if c}, (
            self.prec,upto,{i:c for i,c in self.a.items()if i<upto},coeff)


H = Jet({1:1})
PHI=[1,-14,56,-84,42]
MI=[[300,-2100,4200,-2520],[-2100,16800,-36120,22680],
    [4200,-36120,81480,-52920],[-2520,22680,-52920,35280]]


def early(s,t):
    return 420*s**4-1008*s**3+1008*s*s-504*s+108+(-168*s*s+252*s-108)*t+(33-28*s)*t*t-3*t**3


def front(s,t,k):
    r=t*(t-6)/s**3
    z=2*t*(756*s**3+336*s*s*t-2016*s*s+56*s*t*t-609*s*t+1638*s+6*t**3-81*t*t+351*t-486)/(5*s**4*(2*t-3))
    e=12*(252*s**3+112*s*s*t-672*s*s+42*s*t*t-378*s*t+756*s+2*t**3-37*t*t+192*t-252)/(5*s**3*(2*t-3))
    f=168-4*z
    B=t/(10*(3-2*t));N=s/(5*(3-2*t))
    L=(k+4)*((k-1)*B-Q(1,5))
    yn=e-r*k;yd=z*(k+4)-168
    wn=r*L;wd=z*(k+4)/5-168*(k-1)*B
    return yd*(-s/t+(k-1)*N)-yn*L,yn,yd,wn,wd,r,z,e,f,L


def lift(f,constant,derivative,n):
    y=Jet(constant)
    for i in range(1,n+1):
        y+=Jet({i:-f(y).c(i)/Q(derivative)})
    f(y).match({},n+1)
    return Jet(y.a,n+1)


def ev(a,x):
    d=0
    for c in a[::-1]:d=c+x*d
    return d


def mul(a,b):
    z=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):z[i+j]+=x*y
    return z


def add(a,b):
    return [(a[j]if j<len(a)else 0)+(b[j]if j<len(b)else 0)
            for j in range(max(len(a),len(b)))]


def q_pol(mom):
    return mul([1,-1],[sum(x*y for x,y in zip(row,mom))for row in MI])


def q_data(s,t):
    return [(6-3*t)*(6-t)*(3-t),2*s*(6-t)*(3-t),3*s*s*(6-t),12*s**3]


def poly_der(a):
    return [i*x for i,x in enumerate(a)if i]


def div_X(a,w):
    z=[0]*(len(a)-1)
    for j in range(len(z)-1,-1,-1):
        z[j]=a[j+1]+(w*z[j+1] if j+1<len(z) else 0)
    return z,a[0]+w*z[0]


def limit_tail(mom,e,f,y,w):
    m=mul([e,f],q_pol(mom))
    fw=-Q(ev(m,w))/ev(PHI,w)
    if y is None:
        c1=-Q(m[5],42)
    elif y==w:
        c1=-(Q(ev(poly_der(m),w))+fw*ev(poly_der(PHI),w))/ev(PHI,w)
    else:
        c1=(-Q(ev(m,y))/ev(PHI,y)-fw)/(y-w)
    a=add(m,mul(PHI,[fw-c1*w,c1]))
    aa,rr=div_X(a,w);assert rr==0
    if y is not None:
        aa,rr=div_X(aa,y);assert rr==0
    else:
        assert aa[-1]==0
        aa=aa[:-1]
    return aa


def origin_two():
    s=H;t=lift(lambda t:early(s,t),2,-12,12)
    t.match({0:2,1:-Q(28,3)},2)
    K=lambda k:s**3*front(s,t,k)[0]
    for k in range(4):
        assert K(k).c(0)==Q(8,5)*(k+4)*(k+3)**2
    K(-4).match({4:-84},5)
    k=lift(K,-4,Q(8,5),6)
    k.match({0:-4,4:Q(105,2)},5)
    _,yn,yd,wn,wd,_,_,e,f,_=front(s,t,k)
    yn.match({-3:-32},-2);yd.match({0:-2688},1)
    wn.match({1:-336},2);wd.match({0:-672},1)
    assert (s**4*e).c(0)==0 and (s**4*f).c(0)==192
    for i,j in enumerate([112,8,0,0]):
        assert (q_data(s,t)[i]/s).c(0)==j
    a=[112,8,0,0]
    assert limit_tail(a,0,192,0,0)==[645120*c for c in [35,-196,336,-180]]
    assert limit_tail(a,0,192,None,0)==[92160*c for c in [30,-175,308,-168]]


def six_limits():
    s=H;t=lift(lambda t:early(s,t),6,-36,15)
    t.match({0:6,3:-28,4:77},5)
    for k in range(4):
        F=front(s,t,k)
        F[0].match({0:Q(168,15)*(k+2)**2*(k+4)},1)
        assert [x.c(0) for x in F[5:9]]==[-168,84,336,-168]
    for k in range(4):
        F=front(s,t,-2+s*k)
        F[0].match({2:Q(14,5)*(8*k*k-39*k+112)},3)
        F[1].match({1:168*k-756},2)
        F[2].match({1:84*k-3136},2)
        F[3].match({1:Q(112,5)*k},2)
        F[4].match({1:28*k-Q(3136,5)},2)
    for i,j in enumerate([84,0,0,1]):
        assert (q_data(s,t)[i]/(12*s**3)).c(0)==j
    assert limit_tail([84,0,0,1],336,-168,2,0)==[423360*c for c in [-56,324,-567,308]]
    t=6+H;s0=Q(12,5)
    s=lift(lambda s:early(s,t),s0,420*s0**3,12)
    s.match({0:s0,1:Q(93,448)},2)
    for k in range(4):
        assert front(s,t,k)[0].c(0)==-Q(56,5)*(k+2)
    k=lift(lambda k:front(s,t,k)[0],-2,-Q(56,5),8)
    k.match({0:-2,1:-Q(1,12)},2)
    F=front(s,t,k)
    F[2].match({1:Q(28,9)},2);F[4].match({1:Q(14,9)},2)
    F[-1].match({1:-Q(1,90)},2)
    a=[0,0,0,1];z=Q(336,5)
    assert limit_tail(a,z,-168,None,0)==[28224*c for c in [-14,76,-124,63]]
    assert limit_tail(a,z,-168,0,0)==[84672*c for c in [-40,220,-371,196]]


def good_prime_discriminant():
    s=Q(2,3)+H
    t=lift(lambda t:early(s,t),Q(2,3),Q(4,9),15)
    t.match({0:Q(2,3),3:-252},4)
    k=lift(lambda k:front(s,t,k)[0],6,-Q(108,25),12)
    k.match({0:6,4:-Q(8505,2)},5)
    _,yn,yd,wn,wd,_,_,e,f,_=front(s,t,k)
    yd.match({3:-Q(163296,5)},4)
    wd.match({3:Q(81648,5)},4)
    wn.match({3:Q(81648,5)},4)
    yi=yd/yn
    w=wn/wd
    M=mul([e,f],q_pol(q_data(s,t)))
    fyov=-ev(M[::-1],yi)/ev(PHI[::-1],yi)
    fw=-ev(M,w)/ev(PHI,w)
    c1=(fyov-yi*fw)/(1-yi*w);c0=fw-c1*w
    S0=add(M,mul(PHI,[c0,c1]))
    a,d=div_X(S0,w);d.match({},5)
    b=[]
    for j in range(4):
        b.append(a[j]+(yi*b[-1] if j else 0))
    (a[4]+yi*b[3]).match({},5)
    assert [g.c(0)for g in b]==[14336*c for c in [6,-19,20,-7]]
    b0,b1,b2,b3=b
    disc=b2*b2*b1*b1-4*b3*b1**3-4*b2**3*b0-27*b3*b3*b0*b0+18*b3*b2*b1*b0
    disc.match({3:-(2**45)*3**3*7**5},4)
    (s/t-w).match({2:Q(63,2)},3)
    ev(b,w).match({3:-1354752},4)
    ev(b,s/t).match({3:-1354752},4)
    ev(b,Jet(1)).match({2:-32256},3)
    (c0-c1*e/f).match({4:-1693440},5)


if __name__=="__main__":
    origin_two()
    six_limits()
    good_prime_discriminant()
    print("Exact rational Laurent jets and good-prime discriminant PASS")
