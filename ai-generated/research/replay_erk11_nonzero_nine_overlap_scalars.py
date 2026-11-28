"""Exact rational receipt for the q=9 Jacobi-basis and overlap arithmetic."""
from fractions import Fraction as F

R4 = (1, -14, 56, -84, 42)
R5 = (-1, 20, -120, 300, -330, 132)
O8 = (353, -6592, 47432, -180576, 407346, -564984, 474432, -221760, 44352)


def clean(v):
    v = list(v)
    while len(v) > 1 and not v[-1]:
        v.pop()
    return tuple(v)


def add(a, b):
    u = [0] * max(len(a), len(b))
    for k, p in enumerate(a):
        u[k] += p
    for k, q in enumerate(b):
        u[k] += q
    return clean(u)


def scale(a, z):
    return clean(z * k for k in a)


def mul(a, b):
    v = [0] * (len(a) + len(b) - 1)
    for k, p in enumerate(a):
        for j, q in enumerate(b):
            v[k + j] += p * q
    return clean(v)


def comp(a, b):
    r = (0,)
    for v in reversed(a):
        r = add(mul(r, b), (v,))
    return r


def val(a, z):
    return comp(a, (z,))[0]


def delta(a, b):
    return add(mul(comp(R4, a), comp(R5, b)),
               scale(mul(comp(R5, a), comp(R4, b)), -1))


def moment(a, j=0):
    return sum(F(c, (i + j + 2) * (i + j + 3)) for i, c in enumerate(a))


def certify_gram(n=5):
    """Exact LDL^t: each pivot is positive over any ordered field."""
    A = [[F(1, (i + j + 2) * (i + j + 3)) for i in range(n)] for j in range(n)]
    L, ds = [[F(int(i == j)) for j in range(n)] for i in range(n)], []
    for j in range(n):
        z = A[j][j] - sum(L[j][k] ** 2 * ds[k] for k in range(j))
        assert z > 0
        ds.append(z)
        for i in range(j + 1, n):
            L[i][j] = (A[i][j] - sum(L[i][k] * L[j][k] * ds[k] for k in range(j))) / z
    assert [[sum(L[i][k] * L[j][k] * ds[k] for k in range(n))
             for i in range(n)] for j in range(n)] == A
    return ds


def certify():
    for R in (R4, R5):
        assert all(moment(R, j) == 0 for j in range(4))
    for r, left, right in ((R4, F(1, 30), F(1, 30)), (R5, F(-1, 42), F(1, 42))):
        assert sum(F(c, i+2) for i,c in enumerate(r)) == right
        assert sum(F(c, (i+1)*(i+2)) for i,c in enumerate(r)) == left
    print("Rational Gram pivots and endpoint weights", certify_gram(), flush=True)
    assert comp(R4, (1, -1)) == R4
    assert comp(R5, (1, -1)) == scale(R5, -1)

    intervals5 = [
        (F(1, 12), F(1, 10)), (F(1, 4), F(1, 3)),
        (F(1, 2), F(1, 2)), (F(2, 3), F(3, 4)),
        (F(9, 10), F(11, 12)),
    ]
    intervals4 = [
        (F(1, 9), F(1, 8)), (F(1, 3), F(5, 12)),
        (F(7, 12), F(2, 3)), (F(7, 8), F(8, 9)),
    ]
    for R, intervals in ((R4, intervals4), (R5, intervals5)):
        assert len(intervals) == len(R) - 1
        for lo, hi in intervals:
            assert 0 < lo <= hi < 1
            if lo == hi:
                assert val(R, lo) == 0
            else:
                assert val(R, lo) * val(R, hi) < 0
    for k, (lo, hi) in enumerate(intervals4):
        assert intervals5[k][1] <= lo and hi <= intervals5[k + 1][0]
    print("Exact R4/R5 interlacing signs verified.", flush=True)

    A = (0, 1)
    assert val(R4, F(1, 3)) == val(R4, F(2, 3)) == F(-1, 27)
    assert val(R5, F(1, 3)) == F(-7, 81) and val(R5, F(2, 3)) == F(7, 81)
    assert delta((F(1, 3),), (F(2, 3),)) == (F(-14, 2187),)
    assert delta(A, (-1, 2)) == scale(mul((-1, 1), O8), 2)
    # primitive square completion coefficient
    assert F(1, 5) * F(5, 4) ** 2 + F(1, 48) == F(1, 3)
    print("Double overlap determinant and single overlap octic verified.", flush=True)


if __name__ == "__main__":
    certify()
