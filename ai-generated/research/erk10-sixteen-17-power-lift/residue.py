"""Small exact arithmetic in a modulus that is a power of 17."""
from fractions import Fraction as F
from math import prod

class M:
    __slots__=('v',)
    p=17
    def __init__(self,v):
        if isinstance(v,M):self.v=v.v
        else:
            if isinstance(v,int):self.v=v%self.p
            else:
                q=F(v);self.v=q.numerator*pow(q.denominator,-1,self.p)%self.p
    def __int__(self):return self.v
    def __bool__(self):return self.v!=0
    def __hash__(self):return hash(self.v)
    def __eq__(self,o):return self.v==M(o).v
    def __repr__(self):return str(self.v)
    def __neg__(self):return M(-self.v)
    def __add__(self,o):return M(self.v+M(o).v)
    __radd__=__add__
    def __sub__(self,o):return M(self.v-M(o).v)
    def __rsub__(self,o):return M(M(o).v-self.v)
    def __mul__(self,o):return M(self.v*M(o).v)
    __rmul__=__mul__
    def __truediv__(self,o):return M(self.v*pow(M(o).v,-1,self.p))
    def __rtruediv__(self,o):return M(M(o).v*pow(self.v,-1,self.p))
    def __pow__(self,n):return M(pow(self.v,n,self.p))

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def hull(xs):
    v=[xs[0]*0+1]
    for x in xs:
        u=[0]*(len(v)+1)
        for j,t in enumerate(v):u[j]-=t*x;u[j+1]+=t
        v=u
    return tuple(v)
def mu(p):return sum(c/(j+1)for j,c in enumerate(p))
def meanC(p):return sum(v/(j+1)for j,v in enumerate(p)if j%2==0)
def scalar(sites):
    mu0={x:mu(hull([v for v in sites if v!=x]))for x in sites}
    if not all(mu0.values()):return
    cof={x:1/prod(x-y for y in sites if y!=x)for x in sites}
    W={x:mu0[x]*cof[x]for x in sites}
    assert all(sum(w*x**k for x,w in W.items())==1/(next(iter(W))*0+k+1) for k in range(10))
    return W,cof,mu0
