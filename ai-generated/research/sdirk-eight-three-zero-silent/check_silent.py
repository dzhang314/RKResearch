"""Exact rational nonvanishing for all ordered pairs of fourth-Gauss clocks."""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import permutations


@dataclass(frozen=True)
class Box:
    lo: Q
    hi: Q

    @staticmethod
    def as_box(t):
        return t if isinstance(t, Box) else Box(Q(t), Q(t))

    def __add__(self, other):
        other = self.as_box(other)
        return Box(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.as_box(other)

    def __rsub__(self, other):
        return self.as_box(other) + -self

    def __mul__(self, other):
        other = self.as_box(other)
        products = [x*y for x in (self.lo, self.hi) for y in (other.lo, other.hi)]
        return Box(min(products), max(products))
    __rmul__ = __mul__

    def sign(self):
        if self.lo > 0: return "+"
        if self.hi < 0: return "-"
        raise ArithmeticError(f"uncertified nonzero: {self}")


def gauss(x):
    return ((70*x-140)*x+90)*x*x-20*x+1


def line(d,z):
    return (1-z*z)*Q(1,2)-d*(1-z)-(1-d)*(z-d)


def quad(d,z,e,gamma):
    return ((1-z*z*z)*Q(1,3)-(d+e)*(1-z*z)*Q(1,2)
            +d*e*(1-z)-gamma*(z-d)*(z-e))


def clock_candidates(d):
    return [(1-d,d), (1-d,1-d), (Q(1,2),Q(1,2)), (4-5*d,1-d),
            (3*d-1,1-d), (Q(1,2),1-d),
            ((4-d)*Q(1,5),(1+d)*Q(1,5)), ((1+d)*Q(1,3),(2-d)*Q(1,3))]


def main():
    scale = 10**20
    starts = (6943184420297371238,33000947820757186759,
              66999052179242813240,93056815579702628761)
    boxes = [Box(Q(k,scale),Q(k+1,scale)) for k in starts]
    assert gauss(Q(1,2)) != 0
    for j,b in enumerate(boxes):
        assert 0 < b.lo < b.hi < 1
        assert gauss(b.lo)*gauss(b.hi) < 0
        if j: assert boxes[j-1].hi < b.lo
        assert b.lo == 1-boxes[3-j].hi and b.hi == 1-boxes[3-j].lo

    expected = ("+ -++-++++", "- -+++--++", "- ++-+----",
                "+ --+-+--+", "- ++++-+++", "- ---+----",
                "+ --------", "+ ++---+--", "- ----+---",
                "- ----++--", "- +---+---", "- +-+-+-+-")
    for (i,j),want in zip(permutations(range(4),2),expected):
        d,z = boxes[i],boxes[j]
        row = line(d,z).sign() + " " + "".join(
            quad(d,z,e,gamma).sign() for e,gamma in clock_candidates(d))
        assert row == want
        print(i+1,j+1,row)


if __name__ == "__main__":
    main()
