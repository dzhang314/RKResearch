#!/usr/bin/env python3
"""Certified rational interval replay of all fourth DIRK11 clean rows.

SymPy supplies the exact QQ resultant and real isolators. Every subsequent
bound is computed by outward integer rounding on a fixed rational grid.
The displayed decimal values are labels only, never used in a check.
"""
from math import isqrt
import sympy as S

SCALE = 10**140

def ceiling(a,b):
    assert b>0
    return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,v=0,*,ends=None):
        if ends is not None:
            self.lo,self.hi=ends
        elif isinstance(v,I):
            self.lo,self.hi=v.lo,v.hi
        else:
            n,d=map(int,S.Rational(v).as_numer_denom())
            self.lo=n*SCALE//d
            self.hi=ceiling(n*SCALE,d)
        assert self.lo<=self.hi
    @classmethod
    def box(cls,a,b): return cls(ends=(cls(a).lo,cls(b).hi))
    def __add__(self,v):
        v=I(v); return I(ends=(self.lo+v.lo,self.hi+v.hi))
    __radd__=__add__
    def __neg__(self): return I(ends=(-self.hi,-self.lo))
    def __sub__(self,v): return self+-I(v)
    def __rsub__(self,v): return I(v)+-self
    def __mul__(self,v):
        v=I(v); c=[a*b for a in (self.lo,self.hi) for b in (v.lo,v.hi)]
        return I(ends=(min(c)//SCALE,ceiling(max(c),SCALE)))
    __rmul__=__mul__
    def inverse(self):
        assert self.sign()!=0, ('denominator enclosure meets zero', self.show())
        if self.hi<0: return -(-self).inverse()
        return I(ends=(SCALE**2//self.hi,ceiling(SCALE**2,self.lo)))
    def __truediv__(self,v): return self*I(v).inverse()
    def __rtruediv__(self,v): return I(v)*self.inverse()
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        q=I(1)
        for _ in range(n): q=q*self
        return q
    def sqrt(self):
        assert self.lo>0, ('radicand not certified positive',self.show())
        return I(ends=(isqrt(self.lo*SCALE),isqrt(self.hi*SCALE)+1))
    def sign(self): return 1 if self.lo>0 else (-1 if self.hi<0 else 0)
    def show(self): return f'{(self.lo+self.hi)/(2*SCALE):.11g}'
    def strict_abs_lb(self,digits=9):
        """Floor of `10**digits * min |x|`, entirely integral."""
        assert self.sign()!=0
        return min(abs(self.lo),abs(self.hi))*10**digits//SCALE


def J4(x): return 42*x**4-84*x**3+56*x**2-14*x+1

def J5(x): return (2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)


def exact_clocks():
    x,t=S.symbols('x t')
    d=4*t-1-t*t; n=x*t*(1+t)
    P=S.cancel((J5(x)*J4(x*t)-J5(x*t)*J4(x))/(x*(1-t)))
    J4w=42*n**4-84*n**3*d+56*n*n*d*d-14*n*d**3+d**4
    J5w=(2*n-d)*(66*n**4-132*n**3*d+84*n*n*d*d-18*n*d**3+d**4)
    Q=S.cancel((J5(x)*J4w*d-J5w*J4(x))/(x*(d-t*(1+t))))
    ss=S.subresultants(P,Q,x)
    res=S.Poly(ss[-1],t,domain=S.QQ)
    _,fac=S.factor_list(res)
    assert sorted((p.degree(),m) for p,m in fac)==[(1,8),(1,8),(1,20),(60,1)]
    assert S.rem(res.as_expr(),t**20*(t-1)**8*(t-2)**8,t)==0
    [(F,mult)]=[(p,m) for p,m in fac if p.degree()==60]
    line=S.Poly(ss[-2],x); assert line.degree()==1
    Fa=S.Poly(line.nth(1),t,domain=S.QQ).rem(F)
    Fb=S.Poly(line.nth(0),t,domain=S.QQ).rem(F)
    assert S.gcd(Fa,F).degree()==0 and F.count_roots(-S.oo,S.oo)==12
    candidates=F.intervals(eps=S.Rational(1,10**125))
    assert len(candidates)==12 and all(m==1 for _,m in candidates)
    def ev(p,x):
        z=I()
        for a in p.all_coeffs(): z=z*x+I(a)
        return z
    qpoly=S.Poly(J5(x),x)
    for interval,_ in candidates:
        t0=I.box(*interval); u=-ev(Fb,t0)/ev(Fa,t0); v=u*t0
        w=u*t0*(1+t0)/(4*t0-1-t0*t0)
        lam=-J5(u)/J4(u)
        # Obtain the two remaining clean sites from symmetric coefficients.
        l=(I(qpoly.nth(4))+42*lam)/(-132)
        m=(I(qpoly.nth(3))-84*lam)/132
        r=l-u-v-w
        q=m-u*v-u*w-v*w-(u+v+w)*r
        delta=(r*r-4*q).sqrt()
        yield t0,u,v,w,(r-delta)/2,(r+delta)/2


def product(xs):
    out=I(1)
    for x in xs: out=out*x
    return out


def dot(x,y): return sum(a*b for a,b in zip(x,y))


def lag(x,nodes,out):
    return sum(out[i]*product((x-nodes[j])/(n-nodes[j]) for j in range(len(nodes)) if j!=i)
               for i,n in enumerate(nodes))


def taps(nodes,moments):
    """Cramer formula for powers 1..len(nodes); denominators certified."""
    out=[]
    for i,c in enumerate(nodes):
        poly=[I(1)]; other=[z for j,z in enumerate(nodes) if i!=j]
        for z in other:
            poly=[-z*poly[0],*(poly[j-1]-z*poly[j] for j in range(1,len(poly))),poly[-1]]
        out.append(dot(poly,moments)/(c*product(c-z for z in other)))
    return out


def stage4_cases():
    certificate_min={'disc':10**12, 'optional':10**12, 'optional_den':10**12, 'head':10**12}
    neg,pos,optional=0,0,0
    for idx,(t,u,v,w,a0,a1) in enumerate(exact_clocks(),1):
        R=[u,v,w]; M=4*w*u*u-13*w*u*v+4*w*v*v+u*u*v+u*v*v
        L=3*w*w-5*w*(u+v)+10*u*v
        k=[-u**3/6,v**3*(2*u-v)/(6*(u-2*v)),w**3*(2*u-v)*L/(6*M)]
        f=lambda s: u/2+(u*u-4*u*v+v*v)*(s-u)/(2*(u-2*v)*(2*u-v))
        b0=lambda s: [s**2/2,s**3/3,s**4/4,s**5/5]
        b1=lambda s: [I(0),I(-1),-3*u/2,-9*u*u/5-3*(u-v)**2*(s-u)/(5*(2*u-v))]
        hs=lambda s:s*J4(s)
        pp,qq,dv=[],[],[]
        for i,s in enumerate(R):
            ti=taps(R[:i+1],[a+k[i]*b for a,b in zip(b0(s),b1(s))])
            pp.append(dot(ti,[x*h for x,h in zip(R,k)])/k[i])
            qq.append((dot(ti,[x**5 for x in R])-s**6/6)/k[i])
            dv.append(hs(s)/k[i])
        z=w+M/(6*(u-v)**2)
        sig=taps(R,b1(z))
        pz=dot(sig,[x*h for x,h in zip(R,k)])+z*(z-w)
        qz=dot(sig,[x**5 for x in R])
        head=lag(z,R,dv); assert head.sign()!=0
        theta=(lag(z,R,pp)-pz)/head
        chi=(lag(z,R,qq)-qz)/head
        certificate_min['head']=min(certificate_min['head'],head.strict_abs_lb())
        for j,(a,b) in enumerate([(a0,a1),(a1,a0)]):
            R4=R+[a]
            a0t=taps(R4,b0(a)); a1t=taps(R4,b1(a))
            P2=a1t[-1]; P1=a0t[-1]+dot(k,a1t)-f(a); P0=dot(k,a0t)
            disc=P1**2-4*P2*P0
            assert disc.sign()!=0
            certificate_min['disc']=min(certificate_min['disc'],disc.strict_abs_lb())
            if disc.sign()<0: neg+=1
            else: pos+=1
            fa=lag(a,R,pp)-theta*lag(a,R,dv)
            ga=lag(a,R,qq)-chi*lag(a,R,dv)
            den=dot(a1t,[x**5 for x in R4])-ga
            assert den.sign()!=0
            ka=(a**6/6+chi*hs(a)-dot(a0t,[x**5 for x in R4]))/den
            raw=[r+ka*s for r,s in zip(a0t,a1t)]
            eq=dot(raw,[(x-z)*y for x,y in zip(R4,k+[ka])])-(fa-z*f(a))*ka-theta*hs(a)
            assert eq.sign()!=0
            certificate_min['optional_den']=min(certificate_min['optional_den'],den.strict_abs_lb())
            certificate_min['optional']=min(certificate_min['optional'],eq.strict_abs_lb())
            optional+=1
            print(idx,j,'ratio',t.show(),'a',a.show(),'z',z.show(),
                  'disc',disc.show(), 'optional residual',eq.show())
            if disc.sign()>0:
                assert P2.sign()!=0
                for root in [(-P1-disc.sqrt())/(2*P2),(-P1+disc.sqrt())/(2*P2)]:
                    assert root.sign()!=0
                    yield R,k,a,b,f,b0,b1,hs,pp,qq,dv,root,a0t,a1t
    assert (neg,pos,optional)==(16,8,24)
    print('16 negative discriminants, 8 surviving schedules; all 24 optional stages excluded.')
    print('Strict absolute lower bounds, in exact units of 10^-9:',certificate_min)


def quad(p):
    c=p(I(0)); p1=p(I(1)); m1=p(I(-1))
    return (p1+m1)/2-c,(p1-m1)/2,c

def root_resultant(p,q):
    a,b,c=p; d,e,f=q
    # Both inputs may have vanishing quadratic leaders; at any common finite root
    # their 4x4 Sylvester matrix kills (x^3,x^2,x,1).
    return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)

def stage5_check(ctx):
    R,k,a,b,f,b0,b1,h,pp,qq,dv,ka,a0,a1=ctx
    R4=R+[a]; k4=k+[ka]; t4=[x+ka*y for x,y in zip(a0,a1)]
    p_a=dot(t4,[r*x for r,x in zip(R4,k4)])/ka
    q_a=(dot(t4,[r**5 for r in R4])-a**6/6)/ka
    dh=h(a)/ka-lag(a,R,dv)
    theta=(p_a-lag(a,R,pp))/dh
    chi=(q_a-lag(a,R,qq))/dh
    ff2=lambda s:lag(s,R,pp)-theta*lag(s,R,dv)
    rho2=lambda s:lag(s,R,qq)-chi*lag(s,R,dv)
    def P_g(z): return dot(taps(R4,b1(z)),[r**5 for r in R4])-rho2(z)
    def P_da(z): return dot(taps(R4,b1(z)),[(r-z)*x for r,x in zip(R4,k4)])-ff2(z)+z*f(z)
    ropt=root_resultant(quad(P_g),quad(P_da))
    R5=R4+[b]
    ta=taps(R5,b0(b)+[b**6/6+chi*h(b)]); tb=taps(R5,b1(b)+[rho2(b)])
    P=(tb[-1],ta[-1]+dot(k4,tb)-f(b),dot(k4,ta))
    Q=(b*tb[-1],b*ta[-1]+dot([r*x for r,x in zip(R4,k4)],tb)-ff2(b),dot([r*x for r,x in zip(R4,k4)],ta)-theta*h(b))
    rno=root_resultant(P,Q)
    assert dh.sign()!=0 and ropt.sign()!=0 and rno.sign()!=0
    return dh,rno,ropt


if __name__=='__main__':
    n=0
    smallest=[10**16]*3
    for ctx in stage4_cases():
        n+=1
        results=stage5_check(ctx)
        smallest=[min(a,b.strict_abs_lb(14)) for a,b in zip(smallest,results)]
        print('FIFTH',n,'interpolation guard / no optional / optional determinants:',*[x.show() for x in results])
    assert n==16 and min(smallest)>0
    print('All 16 remaining real fourth-tap roots fail both fifth-clean cases.')
    print('Strict abs lower bounds in 10^-14 for [guard, no optional, optional]:',smallest)
