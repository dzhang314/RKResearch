"""Pair equations for disjoint D labels, using exact FLINT polynomial fractions."""
from math import lcm
from flint import fmpq_mpoly_ctx,fmpz_mpoly_ctx
from collections import defaultdict
from itertools import product
Cq=fmpq_mpoly_ctx.get(('H','d'),'lex')
CZ=fmpz_mpoly_ctx.get(('H','d'),'lex')
one=Cq.constant(1)
zero=Cq.constant(0)
class F:
    def __init__(self,n=0,d=1):
        if isinstance(n,F):
            assert d==1
            self.n,self.d=n.n,n.d;return
        try:n=Cq.constant(n)
        except TypeError:pass
        try:d=Cq.constant(d)
        except TypeError:pass
        assert d
        if not n:self.n,self.d=zero,one;return
        if not d.is_constant():
            g=n.gcd(d)
            if not g.is_constant():n=n/g;d=d/g
        a=d.leading_coefficient()
        self.n,self.d=n/a,d/a
    def __add__(self,b):
        b=F(b)
        if self.d==b.d:return F(self.n+b.n,self.d)
        return F(self.n*b.d+b.n*self.d,self.d*b.d)
    __radd__=__add__
    def __neg__(self):return F(-self.n,self.d)
    def __sub__(self,b):return self+-F(b)
    def __rsub__(self,b):return F(b)+-self
    def __mul__(self,b):
        b=F(b)
        if not self or not b:return F()
        a,c=self.n,self.d
        w,x=b.n,b.d
        if not (a.is_constant() or x.is_constant()):
            g=a.gcd(x);a=a/g;x=x/g
        if not (w.is_constant() or c.is_constant()):
            g=w.gcd(c);w=w/g;c=c/g
        return F(a*w,c*x)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=F(b);return self*F(b.d,b.n)
    def __rtruediv__(self,b):return F(b)/self
    def __pow__(self,k):
        assert int(k)==k and k>=0
        return F(self.n**k,self.d**k)
    def __bool__(self):return bool(self.n)
H,d=map(F,Cq.gens())
m=(H+2)/2
def ip(p):
    vals=p.to_dict()
    M=lcm(*(int(c.denominator) for c in vals.values()))
    return CZ.from_dict({ix:int(M*c) for ix,c in vals.items()})
def strip(p,guards):
    for g in guards:
        while p and (q:=p.gcd(g)).total_degree()>0:
            p,r=divmod(p,q);assert not r
    return p
def ev(a,v):
    out=F()
    for g in reversed(a):out=out*v+g
    return out
def div_linear(a,r):
    b=a[1:]
    for i in range(len(b)-2,-1,-1):b[i]=b[i]+r*b[i+1]
    assert not (a[0]+r*b[0])
    return b
def L(y,j=4):
    z=y-H/2
    return z**3-3*m*m*z/5 if j==3 else z**4-6*m*m*z*z/7+3*m**4/35
def pairs(phase,z):
    u=z/2 if phase=='A3' else z
    k=1+2*u-u*u
    if phase=='S':return 2-z,k/2,k/2,[z,z-1,z-2,k]
    D=-2+u+4*u*u-u**3
    N=(1+4*u-4*u*u)*D+4*u*u*(3*u-2)
    if phase=='A3':return u,N/(2*D),k/2,[u,D,N,k,3*u-2]
    return 2*z,k/2,N/(2*D),[u,D,N,k,3*u-2]
def frame(front,rear):
    s,fd,fs,front_taps=pairs(front,d)
    u=d/2 if front=='A3' else d
    g={'front_taps':front_taps,'base':[m,H,d,d-H,2*d-H,u-2,L(H),L(d),s,s-d,s-H]}
    aux=sum(g.values(),[])
    assert all(aux) and all(a.d.is_constant() for a in aux)
    base=[ip(a.n) for a in aux]
    h=H/2
    L4=[L(F()),-4*h**3+12*m*m*h/7,6*h*h-6*m*m/7,-4*h,F(1)]
    L3=[L(F(),3),3*h*h-3*m*m/5,-3*h,F(1),F()]
    a1=(L(d,3)/L(d)-L(H,3)/L(H))/(d-H)
    a0=L(H,3)/L(H)-a1*H
    Q=[L3[i]-a0*L4[i]-(a1*L4[i-1] if i else F()) for i in range(5)]+[-a1]
    M=div_linear(div_linear(Q,H),d)
    l0=2*M[0];l1=(ev(M,s)/fs-l0)/s
    a=(fs-F(1)/2)/s; b=M[3]/l1
    e=-l0/l1
    E=M[2]*l1-l1*l1*a-M[3]*(l0-l1*s)
    g['slopes']=[a1,l1]
    g['paid_front_graph']=[M[0],ev(M,s),l0]
    assert all(not strip(ip(a.d),base).total_degree() for a in sum(g.values(),[]))
    base+=[ip(l1.n)]
    xg,rhod,rhot,g['rear_taps']=pairs(rear,H-e)
    t=H-xg
    R=lambda y:F(1)/2+a*y+b*y*(y-s)
    mu=R(t)
    omega=s*t*(t-s)
    l0z=2*mu*L(F())*(t-s)
    lsz=-mu*L(s)*t/fs
    ltz=L(t)*s
    Z=lambda y:l0z*(y-s)*(y-t)+lsz*y*(y-t)+ltz*y*(y-s)
    jd=mu*omega*L(d)-fd*Z(d)
    pd=fd*(fd-R(d))
    def V(r,rho):
        return pd*(rhot*rhot*omega*L(r)-rhot*rho*Z(r))-jd*rho*(mu*rho-rhot*R(r))
    if rear=='S':
        k=2*rhot
        X=pd*(omega*L(e)-Z(e))-jd*(mu-R(e))
        Y=pd*(k*k*omega*L(H)-k*Z(H))-jd*(mu-k*R(H))
    else:
        X=V(e,rhod);Y=V(H,F(1)/2)
    g['hidden_D']=[b,e,e-H,e-d,e-s,2*e-H,e+d-H,L(e)]
    g['rear_S']=[ev(M,t),t,t-s,t-H,t-d,t-e,mu]
    g['paid_D_pairs']=[pd,mu/2-rhot*R(H),mu*rhod-rhot*R(e)]
    aux=sum(g.values(),[])
    assert all(aux)
    support=base+[ip(a.n) for a in g['rear_taps']]
    assert all(strip(ip(a.d),support).total_degree()==0 for a in aux)
    guards={k:[ip(a.n) for a in z] for k,z in g.items()}
    guards['denominators']=[ip(a.d) for a in aux]
    gs=sum(guards.values(),[])
    assert all(strip(ip(a.d),gs).total_degree()==0 for a in [E,X,Y])
    eq=[strip(ip(a.n),gs) for a in [E,X,Y]]
    assert all(eq)
    return eq,guards
def project(f,r,method=None):
    eq,guards=frame(f,r)
    E,X,Y=eq
    hs=[a for a in sum(guards.values(),[]) if not a.degrees()[1]]
    if method is None:method=lambda a,b:a.resultant(b,'d')
    print(f,r,'rows',[a.degrees() for a in eq],flush=True)
    P=[strip(method(E,z),hs) for z in (X,Y)]
    assert all(P)
    q=P[0].gcd(P[1])
    assert q
    factors=q.factor()[1]
    print(f,r,'H projections',[p.total_degree() for p in P],
          'H factors',[(a.total_degree(),n) for a,n in factors],flush=True)
    return factors,eq,guards
