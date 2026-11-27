"""Fast symbolic Q(t)(s), t²=1/2, and a monic binary quotient."""
from flint import fmpq_poly as P, fmpq as Q
from quadratic_poly import E
from itertools import permutations

Z=P(0);O=P(1);S=P([0,1])
H=Q(1,2)
class Rat:
    __slots__=("a","b","d")
    def __init__(self,a=0,b=0,d=1):
        a=P(a);b=P(b);d=P(d)
        assert d
        if not a and not b:
            self.a,self.b,self.d=Z,Z,O
            return
        if d.degree()>0:
            g=d.gcd(a).gcd(b)
            if g.degree()>0:
                a=a//g;b=b//g;d=d//g
        cf=d.leading_coefficient()
        self.a=a/cf;self.b=b/cf;self.d=d/cf
    @classmethod
    def of(cls,u):
        if isinstance(u,Rat):return u
        if isinstance(u,Ext):return NotImplemented
        return cls(u)
    @classmethod
    def k(cls,a):
        # Exact ANP coefficient in Q[t]/(t²-1/2).
        arr=list(a.to_list())[::-1]
        arr=[Q(int(x.numerator),int(x.denominator)) for x in arr]
        while len(arr)<2:arr.append(Q(0))
        assert len(arr)==2
        return cls(*arr)
    def __add__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        if not o:return self
        if not self:return o
        if self.d==o.d:return Rat(self.a+o.a,self.b+o.b,self.d)
        j=self.d.gcd(o.d)
        v=self.d//j;u=o.d//j
        return Rat(self.a*u+o.a*v,self.b*u+o.b*v,self.d*u)
    __radd__=__add__
    def __neg__(self):return Rat(-self.a,-self.b,self.d)
    def __sub__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        return self+-o
    def __rsub__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        return o+-self
    def __mul__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        if not o or not self:return zero
        if o.d.degree()==0 and o.a.degree()<=0 and not o.b:
            return Rat(self.a*o.a,self.b*o.a,self.d)
        v=self.d.gcd(o.a).gcd(o.b);u=o.d.gcd(self.a).gcd(self.b)
        a,b,d=self.a//u,self.b//u,self.d//v
        c,e,f=o.a//v,o.b//v,o.d//u
        return Rat(a*c+H*b*e,a*e+b*c,d*f)
    __rmul__=__mul__
    def __bool__(self):return bool(self.a) or bool(self.b)
    def __eq__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        return (self.a,self.b,self.d)==(o.a,o.b,o.d)
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        a=one;x=self
        while n:
            if n&1:a*=x
            x*=x;n>>=1
        return a
    def inv(self):
        assert self
        if not self.b:return Rat(self.d,0,self.a)
        return Rat(self.d*self.a,-self.d*self.b,self.a*self.a-H*self.b*self.b)
    def __truediv__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        return self*o.inv()
    def __rtruediv__(self,o):
        o=self.of(o)
        if o is NotImplemented:return NotImplemented
        return o*self.inv()
    def numerator(self):return E(self.a,self.b)
    def deg(self):
        return (max(self.a.degree(),self.b.degree()),self.d.degree())
    def __repr__(self):
        return f"Rat{self.deg()}"
class Ring2:
    """u^2 + c1 u + c0=0. Inversion allowed precisely at nonzero norms."""
    def __init__(self,c0,c1):self.c0,self.c1=c0,c1
    def __call__(self,x):
        if isinstance(x,Ext):
            if x.ctx is self:return x
            ctx=self
            while isinstance(ctx.c0,Ext) and ctx.c0.ctx is not x.ctx:ctx=ctx.c0.ctx
            assert isinstance(ctx.c0,Ext) and ctx.c0.ctx is x.ctx
        return Ext(x,0,self)
    def gen(self):return Ext(0,1,self)
class Ext:
    __slots__=("a","b","ctx")
    def __init__(self,a,b,ctx):
        self.a,self.b,self.ctx=a,b,ctx
    def parent_of(self,o):
        if not isinstance(o,Ext):return False
        c=o.ctx
        while isinstance(c.c0,Ext):
            c=c.c0.ctx
            if c is self.ctx:return True
        return False
    def __add__(self,o):
        if self.parent_of(o):return o.ctx(self)+o
        o=self.ctx(o);return Ext(self.a+o.a,self.b+o.b,self.ctx)
    __radd__=__add__
    def __neg__(self):return Ext(-self.a,-self.b,self.ctx)
    def __sub__(self,o):
        if self.parent_of(o):return o.ctx(self)-o
        return self+-self.ctx(o)
    def __rsub__(self,o):
        if self.parent_of(o):return NotImplemented
        return self.ctx(o)+-self
    def __mul__(self,o):
        if self.parent_of(o):return o.ctx(self)*o
        o=self.ctx(o)
        j=self.b*o.b
        return Ext(self.a*o.a-j*self.ctx.c0,self.a*o.b+self.b*o.a-j*self.ctx.c1,self.ctx)
    __rmul__=__mul__
    def __eq__(self,o):
        if self.parent_of(o):return o==self
        o=self.ctx(o)
        return (self.a,self.b)==(o.a,o.b)
    def __bool__(self):return bool(self.a) or bool(self.b)
    def __pow__(self,n):
        if n<0:return self.inv()**(-n)
        a=self.ctx(1);x=self
        while n:
            if n&1:a*=x
            x*=x;n>>=1
        return a
    def norm(self):return self.a*(self.a-self.b*self.ctx.c1)+self.b*self.b*self.ctx.c0
    def inv(self):
        n=self.norm()
        assert n
        return Ext((self.a-self.b*self.ctx.c1)/n,-self.b/n,self.ctx)
    def __truediv__(self,o):
        if self.parent_of(o):return o.ctx(self)/o
        o=self.ctx(o)
        if not o.b:return Ext(self.a/o.a,self.b/o.a,self.ctx)
        return self*o.inv()
    def __rtruediv__(self,o):
        if self.parent_of(o):return NotImplemented
        return self.ctx(o)*self.inv()
    def __repr__(self):return repr((self.a,self.b))

zero,one,s=Rat(),Rat(1),Rat(S)
def det(a):
    ds=0;n=len(a)
    for p in permutations(range(n)):
        r=1
        for i,j in enumerate(p):
            r*=a[i][j]
            if not r:break
        if sum(p[i]>p[j] for i in range(n-1) for j in range(i+1,n))%2:ds-=r
        else:ds+=r
    return ds
def cramer(a,v):
    return [det([[v[j] if i==c else x for i,x in enumerate(row)] for j,row in enumerate(a)])
            for c in range(len(a))]
def trim(v):
    v=list(v)
    while v and not v[-1]:v.pop()
    return v
def mul(a,b):
    if not a or not b:return []
    u=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):u[i+j]+=x*y
    return trim(u)
def ev(v,x):
    c=0
    for a in v[::-1]:c=c*x+a
    return c
def divmod_monic(f,g):
    assert g[-1]==1
    f=trim(f);q=[0]*max(0,len(f)-len(g)+1)
    while len(f)>=len(g):
        i=len(f)-len(g);u=f[-1];q[i]=u
        for j,y in enumerate(g):f[i+j]-=u*y
        f=trim(f)
    return trim(q),f
def lift(x2):return x2 if isinstance(x2,(Rat,Ext)) else Rat(x2)
