#!/usr/bin/env python3
"""Exact real-root and head-discriminant replay for the published fixed-q tuple."""
from fractions import Fraction as F
from math import comb
import sympy as S
import origin_polynomial as origin

x = origin.c
h0,f0,k0,j0,a1 = origin.coefficients()
num,_ = S.fraction(a1)
[(P,m)] = [(S.Poly(p,x),m) for p,m in S.factor_list(num,x)[1]
           if p.subs(x,2) % 29 == 0]
assert P.degree() == 10 and m == 1 and P.is_irreducible
P = P.set_domain(S.QQ)

def variations(values):
    signs = [1 if a > 0 else -1 for a in values if a]
    return sum(a != b for a,b in zip(signs,signs[1:]))

sturm = [P,P.diff()]
while sturm[-1].degree() > 0:
    q = -sturm[-2].rem(sturm[-1])
    assert not q.is_zero
    sturm.append(q)
assert [t.degree() for t in sturm] == list(range(10,-1,-1))
assert [int(S.sign(t.LC())) for t in sturm] == [1,1,1,1,1,-1,1,1,-1,-1,1]
inf = tuple(variations([t.LC()*sign**t.degree() for t in sturm]) for sign in (-1,1))
assert inf == (6,4)
print("Sturm variations at negative and positive infinity:", *inf)

# Separate transformed Descartes certificate in integer arithmetic.
pc = [int(P.nth(i)) for i in range(11)]
D = 100000
breaks = [0,19750,39500,59250,79001,79002,85314,85315,100000,200000,1000000]
def transform(a,b):
    return [sum(pc[i]*D**(10-i)*comb(i,j)*a**(i-j)*b**j*comb(10-i,k-j)
                for i in range(11) for j in range(max(0,k-(10-i)),min(i,k)+1))
            for k in range(11)]
areas = [variations(transform(a,b)) for a,b in zip(breaks,breaks[1:])]
assert areas == [0,0,0,0,1,0,1,0,0,0]
assert variations([pc[j]*(-1)**j for j in range(11)]) == 0
assert variations([sum(pc[i]*comb(i,j)*10**(i-j) for i in range(j,11))
                   for j in range(11)]) == 0
assert all(P.eval(S.Rational(a,D)) != 0 for a in breaks)
print("Descartes variations on the ten bounded intervals:", areas)

class Ivl:
    """Closed intervals with exact rational endpoints, including divisions."""
    def __init__(self,a,b=None):
        self.lo,self.hi = F(a),F(a if b is None else b)
        assert self.lo <= self.hi
    def __add__(self,o):
        o = iv(o)
        return Ivl(self.lo+o.lo,self.hi+o.hi)
    __radd__ = __add__
    def __neg__(self):
        return Ivl(-self.hi,-self.lo)
    def __sub__(self,o):
        return self + (-iv(o))
    def __rsub__(self,o):
        return iv(o) + (-self)
    def __mul__(self,o):
        o = iv(o)
        v = [a*b for a in (self.lo,self.hi) for b in (o.lo,o.hi)]
        return Ivl(min(v),max(v))
    __rmul__ = __mul__
    def __truediv__(self,o):
        o = iv(o)
        assert not (o.lo <= 0 <= o.hi)
        return self * Ivl(1/o.hi,1/o.lo)
    def __rtruediv__(self,o):
        return iv(o)/self
    def __pow__(self,n):
        r = Ivl(1)
        for _ in range(n):
            r *= self
        return r
    def box(self,D):
        return self.lo*D//1, -((-self.hi*D)//1)

def iv(a):
    return a if isinstance(a,Ivl) else Ivl(a)

def peval(cs,c):
    v = iv(0)
    for a in reversed(cs):
        v = v*c + a
    return v

def rational(fn,c):
    u,v = S.fraction(fn)
    coeff = lambda p:[F(int(a.p),int(a.q)) for a in reversed(S.Poly(p,x).all_coeffs())]
    return peval(coeff(u),c)/peval(coeff(v),c)

def mul(*polys):
    r = [iv(1)]
    for p in polys:
        h = [iv(0)]*(len(r)+len(p)-1)
        for i,a in enumerate(r):
            for j,b in enumerate(p):
                h[i+j] += a*b
        r = h
    return r

def moment(p,shift=0):
    return sum(a/(i+shift+1) for i,a in enumerate(p))

def head(c):
    g,R,d = 6,15,26
    h,f,k = (rational(e,c) for e in (h0,f0,k0))
    om = 210*c**3-336*c*c+168*c-28
    e = c*(c-d)/(c+c*om*d)
    Qc = e*d*k
    # k+l=0 at a root of P, as verified by the exact origin identity.
    Ql = -Qc
    lin = lambda a:[-a,1]
    T3 = mul(lin(f),lin(g),lin(h))
    BB = mul([0,-1,1],lin(c),lin(d),lin(e),T3)
    E0,E1 = moment(BB),moment(BB,1)
    V=[75*c**3-108*c*c+45*c-5,
       -3*(175*c**3-244*c*c+97*c-10),
       3*(350*c**3-476*c*c+183*c-18),
       -15*(42*c**3-56*c*c+21*c-2)]
    beta=V[0]/T3[0]
    Phi=mul(lin(1),lin(c),lin(d),lin(e),[a-beta*b for a,b in zip(V,T3)])
    u=E0*R*c*c-2*Qc*c
    v=-E0*R*c-E0*c*c+E1*c+2*Qc-Ql*c
    w=-E1*R*c*c+Qc*c*c
    uu,vv,ww=-moment(Phi,1),moment(Phi),moment(Phi,2)
    delta=u*vv-v*uu
    sh,ph=(v*ww-w*vv)/delta,(w*uu-u*ww)/delta
    return sh*sh-4*ph,delta

for lo,hi,witness,Hbox,Dbox in (
    (79001089317030856056,79001089317030856057,(6,5),(645172775,645172779),(-10883784,-10883783)),
    (85314051436405470022,85314051436405470023,(5,4),(737493555,737493557),(-136394680,-136394679)),
):
    D = 10**20
    vals = tuple(variations([t.eval(S.Rational(a,D)) for t in sturm]) for a in (lo,hi))
    assert vals == witness
    H,d = head(Ivl(F(lo,D),F(hi,D)))
    for z,box in ((H,Hbox),(d,Dbox)):
        a,b=z.box(10**9)
        assert box[0] <= a <= b <= box[1], (a,b,box)
    assert H.lo > 0
    print("Root bracket:", (lo,hi), "variations:", vals,
          "H grid enclosure:",H.box(10**9), "head determinant:",d.box(10**9))
print("Exactly two real decic roots; both ordered head roots are real over each.")
