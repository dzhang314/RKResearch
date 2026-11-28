"""Memory-safe exact fraction operations; physical equations unchanged."""
import disjoint_projection as core
from flint import fmpq_mpoly_ctx
Cq=fmpq_mpoly_ctx.get(('H','d'),'lex')
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
    @staticmethod
    def make(n,d):
        """Use only when numerator and denominator are known coprime."""
        out=F.__new__(F)
        if not n:
            out.n,out.d=zero,one
            return out
        a=d.leading_coefficient()
        out.n,out.d=n/a,d/a
        return out
    def __add__(self,b):
        b=F(b)
        if not self:return b
        if not b:return self
        if self.d==b.d:
            n=self.n+b.n
            if not n:return F()
            g=n.gcd(self.d)
            return F.make(n/g,self.d/g)
        g=self.d.gcd(b.d)
        u,v=self.d/g,b.d/g
        n=self.n*v+b.n*u
        if not n:return F()
        if g.is_constant():return F.make(n,u*v)
        q=n.gcd(g)
        return F.make(n/q,(g/q)*u*v)
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
        return F.make(a*w,c*x)
    __rmul__=__mul__
    def __truediv__(self,b):
        b=F(b);assert b.n;return self*F.make(b.d,b.n)
    def __rtruediv__(self,b):return F(b)/self
    def __pow__(self,k):
        assert int(k)==k and k>=0
        return F.make(self.n**k,self.d**k)
    def __bool__(self):return bool(self.n)

def frame(front,rear):
    """Evaluate the original exact physical frame with canonical fractions."""
    old=core.F,core.H,core.d,core.m
    try:
        core.F=F
        core.H,core.d=map(F,Cq.gens())
        core.m=(core.H+2)/2
        return core.frame(front,rear)
    finally:
        core.F,core.H,core.d,core.m=old

strip=core.strip
