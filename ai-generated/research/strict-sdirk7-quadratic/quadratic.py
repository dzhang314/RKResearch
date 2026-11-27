"""Tiny exact arithmetic for Q[ρ], ρ² = 432969."""
from fractions import Fraction

RADICAND = 432969

class Quad:
    __slots__ = ('a', 'b')
    def __init__(self, a=0, b=0):
        if isinstance(a, Quad):
            self.a, self.b = a.a, a.b
        else:
            self.a, self.b = Fraction(a), Fraction(b)
    def __add__(self, rhs):
        rhs = Quad(rhs)
        return Quad(self.a + rhs.a, self.b + rhs.b)
    __radd__ = __add__
    def __neg__(self):
        return Quad(-self.a, -self.b)
    def __sub__(self, rhs):
        return self + -Quad(rhs)
    def __rsub__(self, lhs):
        return Quad(lhs) + -self
    def __mul__(self, rhs):
        rhs = Quad(rhs)
        return Quad(self.a*rhs.a + RADICAND*self.b*rhs.b, self.a*rhs.b + self.b*rhs.a)
    __rmul__ = __mul__
    def norm(self):
        return self.a*self.a - RADICAND*self.b*self.b
    def inv(self):
        d = self.norm()
        return Quad(self.a/d, -self.b/d)
    def __truediv__(self, rhs):
        return self * Quad(rhs).inv()
    def __pow__(self, k):
        assert k >= 0
        p, a = Quad(1), self
        while k:
            if k % 2:
                p *= a
            a *= a
            k //= 2
        return p
    def __eq__(self, rhs):
        rhs = Quad(rhs)
        return (self.a, self.b) == (rhs.a, rhs.b)
    def __bool__(self):
        return bool(self.a or self.b)
    def mod(self, root, m):
        assert (root*root - RADICAND) % m == 0
        return (self.a.numerator * pow(self.a.denominator, -1, m) +
                self.b.numerator * pow(self.b.denominator, -1, m) * root) % m
