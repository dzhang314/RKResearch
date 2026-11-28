#!/usr/bin/env python3
"""Exact fixed-Lobatto arithmetic, Python standard library only."""
from itertools import permutations

P = 1013
DERIVATIVE = (-42, 840, -5040, 12600, -13860, 5544)
ROOTS = (347, 468, 507, 546, 667)


def hull(nodes):
    f = [1]
    for z in nodes:
        f = mul(f, [-z, 1])
    return f


def mul(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i + j] = (h[i + j] + a * b) % P
    return h


def dot(a, b):
    return sum(x * y for x, y in zip(a, b)) % P


def ev(f, z):
    return dot(f, (pow(z, i, P) for i in range(len(f))))


def primitive(f):
    return [0] + [a * pow(i + 1, -1, P) % P for i, a in enumerate(f)]


def sh(f, j):
    return [0] * j + f


def integrate(f, u=0, v=1):
    g = primitive(f)
    return (ev(g, v) - ev(g, u)) % P


def masses(nodes, f, moments):
    return [dot(moments, ell) * pow(ev(ell, z) * ev(f, z) % P, -1, P) % P
            for i, z in enumerate(nodes) for ell in [hull(nodes[:i] + nodes[i+1:])]]


def rank(rows, width):
    pivots = {}
    for row in rows:
        assert len(row) == width
        r = [v % P for v in row]
        for j, w in enumerate(r):
            if not w:
                continue
            if j not in pivots:
                pivots[j] = [v * pow(w, -1, P) % P for v in r]
                break
            r = [(x - w * y) % P for x, y in zip(r, pivots[j])]
    return len(pivots)


def cut_axes(g):
    early, mid, late = g[:3], g[3], g[4:]
    f, h = hull(early), hull(late)
    f4, h4 = mul(f, [-mid, 1]), mul(h, [-mid, 1])
    m = [[integrate(mul(sh(h4, i), primitive(sh(f, j)))) for j in range(3)]
         for i in range(2)]
    n = [[integrate(mul(sh(h, i), primitive(sh(f4, j)))) for j in range(2)]
         for i in range(3)]
    assert rank(m, 3) == rank(n, 2) == 2
    va, vb = [], []
    for a in m:  # a = M^T x, so the two rows are its coordinate directions.
        rot = [(a[2] - mid * a[1]) % P, (mid * a[0] - a[1]) % P]
        b = [dot(row, rot) for row in n]
        va.append(masses(late, f, a))
        vb.append(masses(early, h, b))
    return va, vb


# A biform of known bidegree is encoded sparsely by exponents of x_1,t.
def add(f, g):
    r = f.copy()
    for k, a in g.items():
        v = (r.get(k, 0) + a) % P
        if v:
            r[k] = v
        elif k in r:
            del r[k]
    return r


def scl(f, c):
    return {k: a*c % P for k, a in f.items() if a*c % P}


def times(f, g):
    r = {}
    for (i, j), a in f.items():
        for (k, l), b in g.items():
            r = add(r, {(i+k, j+l): a*b})
    return r


def sum_forms(forms):
    r = {}
    for f in forms:
        r = add(r, f)
    return r


def det3(m):
    return sum_forms(scl(times(times(m[0][i], m[1][j]), m[2][k]), sign)
                      for i, j, k, sign in ((0,1,2,1),(1,2,0,1),(2,0,1,1),
                                            (0,2,1,-1),(1,0,2,-1),(2,1,0,-1)))


def lift_int(a):
    return {(0, 0): a}


def moment(f, grid, axes):
    return {(i, j): dot(v, (ev(f, z) for z in xs))
            for j, (xs, vs) in enumerate(((grid[4:], axes[0]), (grid[:3], axes[1])))
            for i, v in enumerate(vs)}


def pick(f, j, d):
    return [f.get((i, j), 0) for i in range(d+1)]


def front(grid, axes, u, v):
    f = hull((u, v))
    return det3([[moment(sh(f, j+d), grid, axes) for j in range(3)]
                 for d in (0, 1)] +
                [[lift_int(integrate(sh(f, j), u, v)) for j in range(3)]])


def power(f, e):
    r = [1]
    for _ in range(e):
        r = mul(r, f)
    return r


def sub_scales(g, s, t):
    terms = [mul(mul(pick(g, j, 4), power(s, 4-j)), power(t, j)) for j in range(5)]
    return [sum(col) % P for col in zip(*terms)]


def mac_rows(fs, d):
    for f in fs:
        for j in range(d+2-len(f)):
            yield [0]*j + f + [0]*(d+1-len(f)-j)


def fixed_case(grid):
    axes = cut_axes(grid)
    left = front(grid, axes, 0, grid[1])
    right = front(grid, axes, grid[5], 1)
    assert pick(left, 2, 2) == pick(right, 0, 2) == [0, 0, 0]
    a, b, c, d = pick(left, 0, 2), pick(left, 1, 2), pick(right, 1, 2), pick(right, 2, 2)
    assert rank(mac_rows((a,b), 3), 4) == 4
    e = [(v-w) % P for v,w in zip(mul(a,d), mul(b,c))]
    m = [moment(sh([1], j), grid, axes) for j in range(6)]
    pc = [scl(det3([[m[r+j] for j in range(4) if j != i] for r in range(3)]), (-1)**i)
          for i in range(4)]
    f = sum_forms(times(p, scl(m[i+2], pow(i+2, -1, P))) for i,p in enumerate(pc))
    g = sum_forms(times(p, sum_forms((
              scl(m[0], pow(i+1, -1, P) - pow(i+2, -1, P)),
              scl(m[i+1], -pow(i+1, -1, P)),
              scl(m[i+2], pow(i+2, -1, P))))) for i,p in enumerate(pc))
    f, g = (sub_scales(z, b, [-v % P for v in a]) for z in (f,g))
    assert rank(mac_rows((e,f), 15), 16) == rank(mac_rows((e,g), 15), 16) == 16


def main():
    assert all(P % q for q in range(2, int(P**0.5)+1))
    assert DERIVATIVE[-1] % P != 0
    assert tuple(z for z in range(P) if ev(DERIVATIVE, z) == 0) == ROOTS
    assert len(set((0, *ROOTS, 1))) == 7
    for xs in permutations(ROOTS):
        fixed_case((0, *xs, 1))
    print("mod 1013, all 120 ordered Lobatto interiors:")
    print("cut ranks (2,2), binary degree-three rank 4, each single-front degree-fifteen rank 16")


if __name__ == "__main__":
    main()
