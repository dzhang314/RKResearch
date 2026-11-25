#!/usr/bin/env python3
"""Independent arithmetic checks. No asserted physical order or attainment."""
from fractions import Fraction as Q
from itertools import product


def widths(m):
    return [1 + min(j, m - 1 - j) for j in range(m)]


def free_floor(m):
    ws = widths(m)
    return max(sum(ws[::2]), sum(ws[1::2]))


def budget_profile(m, z):
    ls = []
    for j, w in enumerate(widths(m)):
        ls.append(w + (max(0, ls[j - 2] - z) if j >= 2 else 0))
    return ls


def rank(a, modulus=None):
    if not a:
        return 0
    a = [list(row) for row in a]
    r = 0
    for j in range(len(a[0])):
        i = next((i for i in range(r, len(a)) if a[i][j]), None)
        if i is None:
            continue
        a[r], a[i] = a[i], a[r]
        pivot = a[r][j]
        for i in range(r + 1, len(a)):
            scale = a[i][j] / pivot if modulus is None else a[i][j]*pow(pivot, -1, modulus)
            row = [v - scale*w for v, w in zip(a[i], a[r])]
            a[i] = row if modulus is None else [v % modulus for v in row]
        r += 1
    return r


def recurrence():
    comparisons = 0
    early = None
    for m in range(1, 221):
        ws = widths(m)
        for z in range(m + 3):
            ls = budget_profile(m, z)
            goal = z + free_floor(m - 2*z) if m > 2*z else (m + 1)//2
            assert max(ls) == goal
            if z > 1 and max(ls) > max(ls[-2:]) and early is None:
                early = (m, z, ls)
            if m <= 40:
                for j, v in enumerate(ls):
                    assert v == max(z + sum(w - z for w in ws[i:j+1:2])
                                    for i in range(j % 2, j + 1, 2))
            comparisons += 1
    assert early is not None
    print("Local-nullity bounds:", comparisons,
          "; first example with the best grade before the ends:", early)


def field_hankels():
    checked = 0
    # Solve the monic extension by ordinary elimination, independently
    # of the linear-mask Hankel whose rank is then evaluated.
    for mod in (11, 13, 17, 19, 23):
        for w in range(1, (mod - 1)//2 + 1):
            inv = lambda d: pow(d, -1, mod)
            ext = [[inv(i+j+1) for j in range(w)] + [-inv(i+w+1) % mod]
                   for i in range(w)]
            for j in range(w):
                piv = next(i for i in range(j, w) if ext[i][j])
                ext[j], ext[piv] = ext[piv], ext[j]
                ext[j] = [v*inv(ext[j][j]) % mod for v in ext[j]]
                for i in range(w):
                    if i != j:
                        a = ext[i][j]
                        ext[i] = [(v - a*t) % mod for v, t in zip(ext[i], ext[j])]
            co = [row[-1] for row in ext] + [1]
            for x in range(mod):
                mat = [[(inv(i+j+2) - x*inv(i+j+1)) % mod for j in range(w)]
                       for i in range(w)]
                vanish = sum(v*pow(x, j, mod) for j, v in enumerate(co)) % mod == 0
                assert rank(mat, mod) == w - int(vanish)
                if x in (0, 1):
                    assert not vanish
                checked += 1
    for w in range(1, 13):
        assert rank([[Q(1, i+j+2) for j in range(w)] for i in range(w)]) == w
    print("Exact finite-field linear-mask Hankel ranks:", checked)


def counted_kernel():
    # Independent small triangular matrices, not physical RK tableaux.
    cases = 0
    for strict in product(range(2), repeat=6):
        for diag in product(range(2), repeat=4):
            A = [[diag[i] if i == j else 0 for j in range(4)] for i in range(4)]
            for (i,j),v in zip(((i,j) for i in range(4) for j in range(i)), strict):
                A[i][j] = v
            x = [sum(row) for row in A]
            R = [[((x[i]-x[j])*A[i][j] - sum(A[i][h]*A[h][j] for h in range(4))) % 5
                  for j in range(4)] for i in range(4)]
            assert all(R[i][i] == -diag[i]**2 % 5 for i in range(4))
            for k in range(5):
                for side in (range(k), range(k, 4)):
                    block = [[R[i][j] for j in side] for i in side]
                    assert len(side)-rank(block, 5) <= sum(diag[i] == 0 for i in side)
                    cases += 1
    print("Local triangular kernel bounds:", cases)


if __name__ == "__main__":
    recurrence()
    field_hankels()
    counted_kernel()
    print("All exact arithmetic checks pass.")
