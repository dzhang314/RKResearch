#!/usr/bin/env python3
"""Finite free QQ algebra proof by one exact good reduction at p=101.

All arithmetic below is literal in the three monic quotient bases.
The result is unit certification, never individual tableau reduction.
"""
import sympy as S

t=S.symbols('t')
class F:
    p=0; mod=(); modpoly=None; inverse_count=0
    def __init__(self,x=0):
        if isinstance(x,F): self.a=x.a
        elif isinstance(x,(int,S.Rational)):
            n,d=map(int,S.Rational(x).as_numer_denom())
            self.a=((n*pow(d,-1,self.p))%self.p,)
        else:
            a=[q%self.p for q in x]; a=a or [0]
            while len(a)>1 and a[-1]==0: a.pop()
            self.a=tuple(a)
    @classmethod
    def start(cls,p,mod):
        assert S.isprime(p) and all(S.Rational(c).q==1 for c in mod.all_coeffs())
        cls.p=p
        cls.mod=tuple(reversed([int(c)%p for c in mod.all_coeffs()]))
        inv=pow(cls.mod[-1],-1,p)
        cls.mod=tuple(c*inv%p for c in cls.mod)
        cls.modpoly=S.Poly.from_list(list(reversed(cls.mod)),t,modulus=p)
        return cls((0,1))
    def __add__(self,x):
        if isinstance(x,Q): return NotImplemented
        x=F(x).a; y=self.a
        return F([(x[i] if i<len(x) else 0)+(y[i] if i<len(y) else 0) for i in range(max(len(x),len(y)))])
    __radd__=__add__
    def __eq__(self,x):
        if isinstance(x,Q): return NotImplemented
        return self.a==F(x).a
    def __neg__(self):return F([-x for x in self.a])
    def __sub__(self,x):
        if isinstance(x,Q): return NotImplemented
        return self+-F(x)
    def __rsub__(self,x):return F(x)+-self
    def __mul__(self,x):
        if isinstance(x,Q): return NotImplemented
        a=self.a;b=F(x).a;p=self.p;m=self.mod;n=len(m)-1
        c=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b): c[i+j]+=x*y
        for r in range(len(c)-1,n-1,-1):
            k=c[r]%p
            for j in range(n):c[r-n+j]-=m[j]*k
        return F(c[:n])
    __rmul__=__mul__
    def inv(self):
        F.inverse_count+=1
        if len(self.a)==1:
            out=F(pow(self.a[0],-1,self.p))
        else:
            u=S.Poly.from_list(list(reversed(self.a)),t,modulus=self.p)
            v=S.invert(u,self.modpoly)
            out=F([int(c) for c in reversed(v.all_coeffs())])
        assert self*out==1
        return out
    def __truediv__(self,x):
        if isinstance(x,Q): return NotImplemented
        return self*F(x).inv()
    def __rtruediv__(self,x):return F(x)*self.inv()
    def __pow__(self,n):
        u=F(1)
        for _ in range(n): u=u*self
        return u

class Q:
    def __init__(self,con,x=0,y=0):
        self.con=con;self.x=x;self.y=y
    def cv(self,x):
        return x if isinstance(x,Q) and x.con is self.con else Q(self.con,x,0)
    def __add__(self,b):
        b=self.cv(b);return Q(self.con,self.x+b.x,self.y+b.y)
    __radd__=__add__
    def __eq__(self,b):
        if isinstance(b,Q) and b.con is not self.con: return NotImplemented
        b=self.cv(b)
        return self.x==b.x and self.y==b.y
    def __neg__(self):return Q(self.con,-self.x,-self.y)
    def __sub__(self,b):return self+-self.cv(b)
    def __rsub__(self,b):return -self+b
    def __mul__(self,b):
        b=self.cv(b); s,p=self.con; k=self.y*b.y
        return Q(self.con,self.x*b.x-p*k,self.x*b.y+self.y*b.x+s*k)
    __rmul__=__mul__
    def inv(self):
        s,p=self.con; n=self.x*self.x+s*self.x*self.y+p*self.y*self.y
        out=Q(self.con,(self.x+s*self.y)/n,-self.y/n)
        assert self*out==1
        return out
    def __truediv__(self,b):return self*self.cv(b).inv()
    def __rtruediv__(self,b):return self.inv()*b
    def __pow__(self,n):
        x=self.cv(1)
        for _ in range(n):x=x*self
        return x

# Explicitly coerce lower-tower values to the top level at use; this avoids
# Python choosing a lower stage's same-type reflected arithmetic unexpectedly.
def cast(z,*xs):return [z.cv(x) for x in xs]

def J4(x):return 42*x**4-84*x**3+56*x**2-14*x+1

def J5(x):return (2*x-1)*(66*x**4-132*x**3+84*x**2-18*x+1)

def receipt():
    x=S.Symbol('x'); d=4*t-1-t*t;n=x*t*(1+t)
    P=S.cancel((J5(x)*J4(x*t)-J5(x*t)*J4(x))/(x*(1-t)))
    J4w=42*n**4-84*n**3*d+56*n*n*d*d-14*n*d**3+d**4
    J5w=(2*n-d)*(66*n**4-132*n**3*d+84*n*n*d*d-18*n*d**3+d**4)
    G=S.cancel((J5(x)*J4w*d-J5w*J4(x))/(x*(d-t*(1+t))))
    seq=S.subresultants(P,G,x); rr=S.Poly(seq[-1],t,domain=S.QQ)
    assert rr.degree()==96
    unit, ff=S.factor_list(rr)
    assert sorted((p.degree(),k) for p,k in ff)==[(1,8),(1,8),(1,20),(60,1)]
    [(factor,_)]=[(p,k) for p,k in ff if p.degree()==60]
    assert rr.monic()==S.Poly(t**20*(t-1)**8*(t-2)**8,t,domain=S.QQ)*factor.monic()
    ln=S.Poly(seq[-2],x); assert ln.degree()==1
    h=[S.Poly(ln.nth(j),t,domain=S.QQ).rem(factor) for j in [0,1]]
    return factor,h,S.Poly(J5(x),x)

def ev(p,x):
    z=0
    for c in p.all_coeffs():z=z*x+F(c)
    return z

def product(xs):
    n=1
    for a in xs:n=n*a
    return n

def dot(xs,ys):return sum(x*y for x,y in zip(xs,ys))

def lag(y,R,v):
    return sum(v[i]*product((y-R[j])/(R[i]-R[j]) for j in range(len(R)) if j!=i)
        for i in range(len(R)))

def taps(R,m):
    out=[]
    for i,d in enumerate(R):
        p=[1]; other=[r for j,r in enumerate(R) if i!=j]
        for z in other:p=[-z*p[0],*(p[j-1]-z*p[j] for j in range(1,len(p))),p[-1]]
        out.append(dot(p,m)/(d*product(d-r for r in other)))
    return out

def quad(p,base):
    c=p(base*0);p1=p(base*0+1);m1=p(base*0-1)
    return (p1+m1)/2-c,(p1-m1)/2,c

def resultant(p,q):
    a,b,c=p;d,e,f=q
    return (a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)

def geometry(u,v,w):
    M=4*w*u*u-13*w*u*v+4*w*v*v+u*u*v+u*v*v
    L=3*w*w-5*w*(u+v)+10*u*v
    k=[-u**3/6,v**3*(2*u-v)/(6*(u-2*v)),w**3*(2*u-v)*L/(6*M)]
    f=lambda s:u/2+(u*u-4*u*v+v*v)*(s-u)/(2*(u-2*v)*(2*u-v))
    b0=lambda s:[s**2/2,s**3/3,s**4/4,s**5/5]
    b1=lambda s:[s*0,s*0-1,-3*u/2,-9*u*u/5-3*(u-v)**2*(s-u)/(5*(2*u-v))]
    h=lambda s:s*J4(s)
    R=[u,v,w];pp,qq,dv=[],[],[]
    for i,s in enumerate(R):
        ti=taps(R[:i+1],[r+k[i]*l for r,l in zip(b0(s),b1(s))])
        pp.append(dot(ti,[x*h for x,h in zip(R,k)])/k[i]);qq.append((dot(ti,[x**5 for x in R])-s**6/6)/k[i]);dv.append(h(s)/k[i])
    z=w+M/(6*(u-v)**2)
    return R,k,f,b0,b1,h,pp,qq,dv,z

def optional4(u,v,w,a):
    R,k,f,b0,b1,h,pp,qq,dv,z=geometry(u,v,w)
    ss=taps(R,b1(z)); pz=dot(ss,[x*g for x,g in zip(R,k)])+z*(z-w);qz=dot(ss,[x**5 for x in R]);
    theta=(lag(z,R,pp)-pz)/lag(z,R,dv);chi=(lag(z,R,qq)-qz)/lag(z,R,dv)
    R4=R+[a]; a0=taps(R4,b0(a));a1=taps(R4,b1(a)); B=[x**5 for x in R4]
    P2=a1[-1];P1=a0[-1]+dot(k,a1)-f(a);P0=dot(k,a0)
    fa=lag(a,R,pp)-theta*lag(a,R,dv);ga=lag(a,R,qq)-chi*lag(a,R,dv)
    ka=(a**6/6+chi*h(a)-dot(a0,B))/(dot(a1,B)-ga)
    lhs=dot([r+ka*s for r,s in zip(a0,a1)],[(x-z)*y for x,y in zip(R4,k+[ka])])
    res=lhs-(fa-z*f(a))*ka-theta*h(a)
    return (P2,P1,P0),res

def fifth(u,v,w,a,b,ka):
    R,k,f,b0,b1,h,pp,qq,dv,z=geometry(u,v,w)
    R4=R+[a]; k4=k+[ka];t4=taps(R4,[r+ka*l for r,l in zip(b0(a),b1(a))])
    pa=dot(t4,[r*x for r,x in zip(R4,k4)])/ka;qa=(dot(t4,[r**5 for r in R4])-a**6/6)/ka
    dh=h(a)/ka-lag(a,R,dv);theta=(pa-lag(a,R,pp))/dh;chi=(qa-lag(a,R,qq))/dh
    f2=lambda s:lag(s,R,pp)-theta*lag(s,R,dv)
    rho2=lambda s:lag(s,R,qq)-chi*lag(s,R,dv)
    G=lambda s:dot(taps(R4,b1(s)),[r**5 for r in R4])-rho2(s)
    H=lambda s:dot(taps(R4,b1(s)),[(r-s)*x for r,x in zip(R4,k4)])-f2(s)+s*f(s)
    ropt=resultant(quad(G,u),quad(H,u))
    R5=R4+[b]; aa=taps(R5,b0(b)+[b**6/6+chi*h(b)]);bb=taps(R5,b1(b)+[rho2(b)])
    P=(bb[-1],aa[-1]+dot(k4,bb)-f(b),dot(k4,aa));q4=[r*x for r,x in zip(R4,k4)]
    Qp=(b*bb[-1],b*aa[-1]+dot(q4,bb)-f2(b),dot(q4,aa)-theta*h(b))
    return ropt,resultant(P,Qp)

if __name__=='__main__':
    F60,(c0,c1),j5=receipt()
    p=101
    T=F.start(p,F60);u=-ev(c0,T)/ev(c1,T);v=u*T;w=u*T*(1+T)/(4*T-1-T*T)
    la=-J5(u)/J4(u);s=-(F(j5.nth(4))+42*la)/132-u-v-w
    q=(F(j5.nth(3))-84*la)/132-u*v-u*w-v*w-(u+v+w)*s
    print('t-clock quotient: rank 60; every required base division is a unit mod 101')
    A=Q((s,q),F(0),F(1));u,v,w,b=cast(A,u,v,w,s-A)
    poly,opt=optional4(u,v,w,A); opt.inv()
    print('Fourth clean quotient: rank 120; all guards and optional-fourth contradiction are units')
    p2,p1,p0=poly
    C=Q((-p1/p2,p0/p2),A*0,A*0+1)
    vv=fifth(*cast(C,u,v,w,A,b),C)
    vv[0].inv();vv[1].inv()
    print('Fourth tap quotient: rank 240; both fifth Sylvester determinants and all guards are units')
    print('Checked primitive residue inverses:',F.inverse_count)
