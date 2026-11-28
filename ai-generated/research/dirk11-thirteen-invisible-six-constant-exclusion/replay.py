#!/usr/bin/env python3
"""Exact good-reduction certificate for the constant-U no-late chart."""
from argparse import ArgumentParser
from fractions import Fraction
from math import isqrt
import sympy as S

x,a,b,s,p=S.symbols("x a b s p")
J3=lambda x: (2*x-1)*(7*x*x-7*x+1)
J4=lambda x: 42*x**4-84*x**3+56*x*x-14*x+1
J5=lambda x: (2*x-1)*(66*x**4-132*x**3+84*x*x-18*x+1)
F=2*(2772*p**4-5544*p**3*s+3864*p**3+3696*p*p*s*s-4872*p*p*s+1536*p*p
     -924*p*s**3+1692*p*s*s-972*p*s+172*p+66*s**4-144*s**3+108*s*s-32*s+3)
G=-28*p*p*s+63*p*p-9*p*s-3*p+s*s
assert S.expand(7*J5(x)-22*(x-S.Rational(1,2))*J4(x)+4*J3(x))==0
subst={s:a+b,p:a*b}
assert S.expand((a-b)*F.subs(subst)-J5(a)*J4(b)+J5(b)*J4(a))==0
assert S.expand((a-b)*G.subs(subst)-a*a*(2*b-a)*J3(b)+b*b*(2*a-b)*J3(a))==0
seq=S.subresultants(F,G,p)
last=S.Poly(seq[-1],s,domain=S.ZZ)
fac=last.primitive()[1]
assert last.degree()==12
assert fac.eval(S.Rational(9,4))!=0  # no drop of the terminal pair quadratic
L=S.Poly(seq[-2],p)
assert L.degree()==1
coeffs=[S.Poly(L.nth(i),s,domain=S.ZZ) for i in range(2)]

class Ring:
    def __init__(self,name,base=None,mod=None,prime=None):
        self.name,self.base,self.mod,self.prime=name,base,mod,prime
        self.d=0 if base is None else len(mod)
        self.invs=0
        self.cache={}
    def to(self,y):
        if isinstance(y,Element) and y.r is self:
            return y
        if self.base is None:
            assert not isinstance(y,Element)
            n,d=Fraction(y).as_integer_ratio()
            return Element(self,n*pow(d,-1,self.prime)%self.prime)
        return Element(self,(self.base.to(y),)+(self.base.to(0),)*(self.d-1))
    def elt(self,vs):
        assert len(vs)==self.d
        return Element(self,tuple(self.base.to(y) for y in vs))
    def gen(self):
        return self.elt([0,1]+[0]*(self.d-2))

class Element:
    def __init__(self,r,v): self.r,self.v=r,v
    def __hash__(self): return hash((id(self.r),self.v))
    def __eq__(self,y):
        return self.v==self.r.to(y).v
    def __add__(self,y):
        r=self.r; b=r.to(y).v; a=self.v
        return Element(r,(a+b)%r.prime if r.base is None else tuple(x+y for x,y in zip(a,b)))
    __radd__=__add__
    def __neg__(self):
        r=self.r
        return Element(r,(-self.v)%r.prime if r.base is None else tuple(-x for x in self.v))
    def __sub__(self,y): return self+-self.r.to(y)
    def __rsub__(self,y): return -self+y
    def __mul__(self,y):
        r=self.r; a=self.v; b=r.to(y).v
        if r.base is None:
            return Element(r,a*b%r.prime)
        d=r.d; c=[r.base.to(0)]*(2*d-1)
        for i,x in enumerate(a):
            if x==0:continue
            for j,y in enumerate(b):
                if y!=0:c[i+j]=c[i+j]+x*y
        for i in range(2*d-2,d-1,-1):
            z=c[i]
            if z!=0:
                for j,f in enumerate(r.mod):c[i-d+j]=c[i-d+j]-z*f
        return r.elt(c[:d])
    __rmul__=__mul__
    def __pow__(self,n):
        z=self.r.to(1);a=self
        while n:
            if n%2:z=z*a
            a=a*a;n//=2
        return z
    def inv(self):
        r=self.r
        if self in r.cache: return r.cache[self]
        r.invs+=1
        if r.base is None:
            y=Element(r,pow(self.v,-1,r.prime))
        elif r.base.base is None:
            m=S.Poly.from_list([1]+list(reversed([c.v for c in r.mod])),x,modulus=r.base.prime)
            u=S.Poly.from_list(list(reversed([c.v for c in self.v])),x,modulus=r.base.prime)
            v=S.invert(u,m)
            y=r.elt([int(v.nth(i)) for i in range(r.d)])
        else:
            columns=[(self*r.gen()**j).v for j in range(r.d)]
            M=list(zip(*columns))
            cof=[(-1)**j*det([[row[k] for k in range(r.d) if k!=j] for row in M[1:]])
                 for j in range(r.d)]
            d=sum(u*v for u,v in zip(M[0],cof)).inv()
            y=r.elt([u*d for u in cof])
        assert self*y==1
        r.cache[self]=y
        return y
    def __truediv__(self,y): return self*self.r.to(y).inv()
    def __rtruediv__(self,y): return self.inv()*y

def det(M):
    if len(M)==1:return M[0][0]
    return sum((-1)**j*e*det([[v for k,v in enumerate(row) if k!=j] for row in M[1:]])
               for j,e in enumerate(M[0]))

def peval(q,y):
    r=y.r; a=r.to(0)
    for c in q.all_coeffs(): a=a*y+int(c)
    return a

def quot(poly,root):
    out=[None]*(len(poly)-1);out[-1]=poly[-1]
    for k in range(len(out)-1,0,-1):out[k-1]=poly[k]+root*out[k]
    return out

def marked(v,u,w):
    rr=(v,u,w)
    h=lambda x:x*J4(x)
    Ip=lambda x:x**4/4-(u+v)*x**3/3+u*v*x*x/2
    aff=lambda x,l,r:((u-x)*l+(x-v)*r)/(u-v)
    key=v**3/(6*h(v))
    kv,ku,kw=[key*h(s) for s in rr]
    L1=lambda x:u+v-aff(x,Ip(v)/kv,Ip(u)/ku)
    m1,m2=u*u/2,u**3/3+ku
    tv=(u*m1-m2)/(v*(u-v))
    tu=(m2-v*m1)/(u*(u-v))
    Lam=lambda x:aff(x,v/2,(tv*kv+tu*ku)/ku)
    m1,m2,m3=w*w/2,w**3/3+kw,w**4/4+L1(w)*kw
    def tap(s,a,b):return (m3-(a+b)*m2+a*b*m1)/(s*(s-a)*(s-b))
    vr=[v/2, rr[0].r.to(0), rr[0].r.to(0)]
    ur=[tv,tu,rr[0].r.to(0)]
    wr=[tap(v,u,w),tap(u,v,w),tap(w,v,u)]
    cv=[kv,ku,kw]
    s0=sum(t*k for t,k in zip(wr,cv))-Lam(w)*kw
    def interp(x,ys):
        return sum(f*(x-a)*(x-b)/((s-a)*(s-b))
                   for (s,a,b),f in zip(((v,u,w),(u,v,w),(w,v,u)),ys))
    scalar4=[(sum(t*r**4 for t,r in zip(row,rr))-s**5/5)/k
             for s,k,row in zip(rr,cv,(vr,ur,wr))]
    ym=[sum(t*r*k for t,r,k in zip(row,rr,cv))/k for k,row in zip(cv,(vr,ur,wr))]
    def ghost(x):
        ll=L1(x)
        ar=[(ll-a-b)/(s*(s-a)*(s-b)) for s,a,b in ((v,u,w),(u,v,w),(w,v,u))]
        left=sum(t*r**4 for t,r in zip(ar,rr))-interp(x,scalar4)
        right=sum(t*(r-x)*k for t,r,k in zip(ar,rr,cv))-interp(x,ym)+x*Lam(x)
        return left,right
    go0=ghost(v.r.to(0)); go1=ghost(v.r.to(1)); gom=ghost(v.r.to(-1))
    qa,qb=[((j+k)/2-i,(j-k)/2,i) for i,j,k in zip(go0,go1,gom)]
    a,b,c=qa;d,e,f=qb
    delta=(a*f-c*d)**2-(a*e-b*d)*(b*f-c*e)
    return s0,delta

def run(prime):
    assert prime>11 and all(prime%d for d in range(2,isqrt(prime)+1))
    r=Ring("F",prime=prime); leading=r.to(int(fac.LC())).inv()
    B=Ring("sum",r,[r.to(int(fac.nth(i)))*leading for i in range(12)])
    ss=B.gen()
    pp=-peval(coeffs[0],ss)/peval(coeffs[1],ss)
    C=Ring("first clean pair",B,[pp,-ss])
    aa=C.gen();bb=C.to(ss)-aa
    ja=J4(aa).inv();la=-J5(aa)*ja
    polys=[(C.to(int(S.Poly(J5(x),x).nth(i)))+la*int(S.Poly(J4(x),x).nth(i)))/132
           for i in range(6)]
    cubic=quot(quot(polys,aa),bb)
    assert cubic[-1]==1
    D=Ring("first old clean",C,cubic[:-1])
    fv=D.gen()
    qq=quot([D.to(q) for q in cubic],fv)
    E=Ring("second old clean",D,qq[:-1])
    fu=E.gen()
    fw=-E.to(cubic[-2])-E.to(fv)-fu
    v,u,w=[E.to(1)-E.to(y) for y in (fv,fu,fw)]
    # Geometry guards; the distinctness and live clocks also hold by census.
    for y in (v,u,w):
        y.inv()
        J4(y).inv()
    _,delta=marked(v,u,w)  # third-clean residual is not used as an obstruction
    delta.inv()
    counts=[R.invs for R in (r,B,C,D,E)]
    print(f"mod {prime}: finite-free ranks 12, 24, 72, 144")
    print(f"Inverse products checked: {sum(counts)} (by level: {counts})")
    print("The first-ghost Sylvester residual is a unit for every ordered clock candidate")

if __name__=="__main__":
    cli=ArgumentParser()
    cli.add_argument("--prime",type=int,default=101)
    arg=cli.parse_args()
    print(f"Exact Jacobi pair resultant degree: {fac.degree()}; linear subresultant present",flush=True)
    run(arg.prime)
