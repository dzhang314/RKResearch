#!/usr/bin/env python3
"""Exact companion units for the remaining three-plus-three DIRK12 chronology."""
from itertools import permutations
from pathlib import Path
import importlib.util

fixed_path = (Path(__file__).resolve().parent.parent
              / "dirk12-fifteen-rank3-four-singleton-end-exclusion" / "check.py")
spec = importlib.util.spec_from_file_location("fixed_grid", fixed_path)
fixed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixed)

P = fixed.P


class Quotient:
    """Standard basis of F_p[q]/(e(q)), with e monic of degree four."""

    def __init__(self, e):
        assert len(e) == 5 and e[-1] != 0
        self.reduce4 = [-x * pow(e[-1], -1, P) % P for x in e[:-1]]
        self.zero = [0, 0, 0, 0]
        self.one = [1, 0, 0, 0]

    def reduce(self, f):
        a = f[:]
        while len(a) > 4:
            tip = a.pop() % P
            for j in range(4):
                k = len(a) - 4 + j
                a[k] = (a[k] + tip * self.reduce4[j]) % P
        return [x % P for x in a] + [0] * (4 - len(a))

    def const(self, v):
        return [v % P, 0, 0, 0]

    def add(self, a, b):
        return [(x + y) % P for x, y in zip(a, b)]

    def sub(self, a, b):
        return [(x - y) % P for x, y in zip(a, b)]

    def scale(self, a, w):
        return [x*w % P for x in a]

    def mul(self, a, b):
        return self.reduce(fixed.mul(a, b))

    def inverse(self, a):
        columns = [self.reduce(fixed.sh(a, j)) for j in range(4)]
        m = [list(r) + [int(i == 0)] for i,r in enumerate(zip(*columns))]
        for j in range(4):
            pivot = next((i for i in range(j,4) if m[i][j]), None)
            assert pivot is not None, ("nonunit", a, self.reduce4)
            m[j],m[pivot] = m[pivot],m[j]
            m[j] = self.scale(m[j], pow(m[j][j], -1, P))
            for i in range(4):
                if i != j:
                    m[i] = self.sub(m[i], self.scale(m[j], m[i][j]))
        result = [row[-1] for row in m]
        assert self.mul(result, a) == self.one
        return result

    def sum(self, ts):
        a = self.zero
        for t in ts:
            a = self.add(a,t)
        return a

    def p_add(self, a, b):
        d = max(len(a), len(b))
        return [self.add(a[i] if i < len(a) else self.zero,
                         b[i] if i < len(b) else self.zero) for i in range(d)]

    def p_mul(self, a, b):
        c = [self.zero] * (len(a) + len(b) - 1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):
                c[j+k] = self.add(c[j+k],self.mul(x,y))
        return c

    def p_scale(self, f, a):
        return [self.mul(x,a) for x in f]

    def p_at(self, f, u):
        return self.sum(self.scale(a,pow(u,i,P)) for i,a in enumerate(f))

    def primitive(self, f, reverse):
        g = [self.zero]+[self.scale(a,pow(i+1,-1,P)) for i,a in enumerate(f)]
        if reverse:
            return [self.p_at(g,1)] + [self.scale(a,-1) for a in g[1:]]
        return g

    def det3(self, m):
        return self.sum(self.scale(self.mul(self.mul(m[0][i],m[1][j]),m[2][k]),sgn)
                        for i,j,k,sgn in ((0,1,2,1),(1,2,0,1),(2,0,1,1),
                                          (0,2,1,-1),(1,0,2,-1),(2,1,0,-1)))


def case(g):
    ax = fixed.cut_axes(g)
    left = fixed.front(g,ax,0,g[1])
    right = fixed.front(g,ax,g[5],1)
    a,b = fixed.pick(left,0,2), fixed.pick(left,1,2)
    c,d = fixed.pick(right,1,2), fixed.pick(right,2,2)
    e = [(v-w) % P for v,w in zip(fixed.mul(a,d),fixed.mul(b,c))]
    # The coefficient of x0^4 is nonzero. Normalize x1=1, so q=x0.
    R = Quotient(e[::-1])
    s,t = R.reduce(b[::-1]), R.reduce([-x % P for x in reversed(a)])

    def L(f):
        v = fixed.moment(f,g,ax)
        l0,l1 = (R.reduce(fixed.pick(v,j,1)[::-1]) for j in (0,1))
        return R.add(R.mul(l0,s),R.mul(l1,t))

    mu = [L(fixed.sh([1],j)) for j in range(6)]

    def evaluate_L(f):
        assert len(f) <= 6
        return R.sum(R.mul(v,w) for v,w in zip(f,mu))

    missing = []
    for u,v in ((0,g[1]),(g[5],1)):
        h = fixed.hull((u,v))
        i0,i1 = (fixed.integrate(fixed.sh(h,j),u,v) for j in (0,1))
        h0,h1,h2 = (L(fixed.sh(h,j)) for j in (0,1,2))
        denominator = R.sub(R.scale(h1,i0),R.scale(h0,i1))
        numerator = R.sub(R.scale(h2,i0),R.scale(h1,i1))
        missing.append(R.mul(numerator,R.inverse(denominator)))
    wf,wr = missing
    R.inverse(R.sub(wf,wr))
    ff,fr = ([R.scale(w,-1),R.one] for w in missing)
    h2 = R.p_mul(ff,fr)
    n0,n1,n2,n3 = (evaluate_L([R.zero]*j+h2) for j in range(4))
    inv = R.inverse(R.sub(R.mul(n0,n2),R.mul(n1,n1)))
    q0 = R.mul(inv,R.sub(R.mul(n1,n3),R.mul(n2,n2)))
    q1 = R.mul(inv,R.sub(R.mul(n1,n2),R.mul(n0,n3)))
    factor = [q0,q1,R.one]

    p = [R.scale(R.det3([[mu[i+j] for j in range(4) if j != k] for i in range(3)]),(-1)**k)
         for k in range(4)]
    for reverse in (0,1):  # Check each primitive independently.
        w,other = (fr,ff) if reverse else (ff,fr)
        h3 = R.p_mul(other,factor)
        S = R.p_add(R.p_scale(p,R.p_at(h3,reverse)),
                    R.p_scale(h3,R.scale(R.p_at(p,reverse),-1)))
        gate = evaluate_L(R.p_mul(w,R.primitive(S,reverse)))
        R.inverse(gate)


def main():
    for xs in permutations(fixed.ROOTS):
        case((0,*xs,1))
    print("mod 1013, all 120 ordered Lobatto interiors:")
    print("quartic infinity guard, two clock-ratio denominators, clock difference,")
    print("remaining quadratic determinant, and two independent grade-four gates are units")


if __name__ == "__main__":
    main()
