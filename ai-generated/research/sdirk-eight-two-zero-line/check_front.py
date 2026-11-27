"""Exact rational enclosures for all twelve directed Gauss-clock pairs.

No floating point, numerical solver, Lean runtime, or tableau is used.
The mathematical reductions in README.md explain the tested scalars.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import permutations

@dataclass(frozen=True)
class Box:
    lo: Q
    hi: Q

    @staticmethod
    def wrap(x):
        return x if isinstance(x, Box) else Box(Q(x), Q(x))

    def __add__(self, v):
        y = self.wrap(v)
        return Box(self.lo+y.lo, self.hi+y.hi)
    __radd__ = __add__

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, v):
        return self + -self.wrap(v)

    def __rsub__(self, v):
        return self.wrap(v) + -self

    def __mul__(self, v):
        y = self.wrap(v)
        t = [a*b for a in (self.lo,self.hi) for b in (y.lo,y.hi)]
        return Box(min(t),max(t))
    __rmul__ = __mul__

    def sign(self):
        if self.lo > 0: return "+"
        if self.hi < 0: return "-"
        raise ArithmeticError(f"uncertified nonzero {self}")

    def __truediv__(self, v):
        y = self.wrap(v)
        y.sign()
        return self*Box(1/y.hi,1/y.lo)

    def __rtruediv__(self, v):
        return self.wrap(v)/self

    def __pow__(self,n):
        a = self.wrap(1)
        for _ in range(n):
            a = a*self
        return a

def L4(x):
    return ((70*x-140)*x+90)*x*x-20*x+1

DEN = 10**20
LEFT = [6943184420297371238,33000947820757186759,
        66999052179242813240,93056815579702628761]
sites = [Box(Q(a,DEN), Q(a+1,DEN)) for a in LEFT]
for i,s in enumerate(sites):
    assert 0<s.lo<s.hi<1
    if i: assert sites[i-1].hi<s.lo
    assert L4(s.lo)*L4(s.hi)<0
    assert s.lo==1-sites[3-i].hi and s.hi==1-sites[3-i].lo

def test(a,b,mirror):
    k = a+b-2
    q = (a+b)*k-a*b+Q(9,7)

    def r(x): return x*x+k*x+q
    def J(x): return x*(x*x/3+k*x/2+q)
    def Jx(x): return x*x*(x*x/4+k*x/3+q/2)

    gam = (J(Q(1))-J(b))/r(b)
    D = J(a)-gam*r(a)
    N = Jx(a)-gam*a*r(a)
    if mirror:
        # D=0 exactly by reflection; no attempted enclosure or division of D.
        return "mirror " + N.sign()

    d=N/D
    R=r(gam)
    B=R+gam**2
    ud=(d-gam)/gam
    u=(2*R-gam*(2*gam+k))/B
    def kap(u): return 1+2*u-u*u
    def chart(u):
        w=2*u
        star = R*kap(u)-r(gam*(3-u))
        denom=-2+u+4*u*u-u**3
        arith = (R*kap(w)-r(gam*(1+w)))*denom + 4*R*u*u*(3*u-2)
        return star,arith
    checks=(gam,D,d-gam,R,B,*chart(ud),ud-(2-u),ud-2*u,*chart(u))
    signs="".join(x.sign() for x in checks)
    return "nonmirror " + signs

print("Gauss root brackets:", LEFT, "scale:", DEN)
print("Nonmirror columns: gamma,D,d-gamma,R,R+gamma^2,S(ud),T(ud),ud-2+u,ud-2u,S(u),T(u)")
for i,j in permutations(range(4),2):
    print(i+1,j+1,test(sites[i],sites[j],i+j==3))
