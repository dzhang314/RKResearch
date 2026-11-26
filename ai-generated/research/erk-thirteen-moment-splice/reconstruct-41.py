"""Exact standard-library reconstruction of the paid explicit 41-stage ERK13.

Use --emit for canonical JSON. The default compares that JSON and verifies
selected rooted conditions and the next-order unit ideal. It does not perform
the exhaustive order-13 tree replay; ORDER-13-IN-41-STAGES.md supplies the proof.
"""

import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import chain
import json
from math import factorial, gcd, lcm, prod
from pathlib import Path


HERE = Path(__file__).resolve().parent
SEED_SHA256 = '8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39'
Z, O = F(0), F(1)
PAID = factorial(13)


def paid_integer(n):
    while (d := gcd(abs(n), PAID)) > 1:
        n //= d
    return abs(n) == 1


def unit(x):
    return paid_integer(x.numerator) and paid_integer(x.denominator)


def dot(a, b):
    return sum((u * v for u, v in zip(a, b)), Z)


def pad(a, n):
    return a + [Z] * (n - len(a))


def basis(i, n):
    return [F(j == i) for j in range(n)]


def solve(matrix, target):
    """Solve exactly over Q and verify that the determinant is a paid unit."""
    m = [list(row) + [v] for row, v in zip(matrix, target)]
    det, n = O, len(target)
    for j in range(n):
        i = next(i for i in range(j, n) if m[i][j])
        if i != j:
            m[i], m[j], det = m[j], m[i], -det
        pivot = m[j][j]
        det *= pivot
        m[j] = [v / pivot for v in m[j]]
        for i in range(n):
            if i != j and (v := m[i][j]):
                m[i] = [u - v * w for u, w in zip(m[i], m[j])]
    assert unit(det), det
    return [row[-1] for row in m], det


def read(ops, rows, desired):
    """Represent a polynomial functional by a literal stage-vector read."""
    ns = len(ops)
    scalars, det = solve([[f(j) for f in ops] for j in range(ns)], [desired(j) for j in range(ns)])
    n = max(map(len, rows))
    return [dot(scalars, c) for c in zip(*(pad(r, n) for r in rows))], det


def eval_at(x):
    return lambda j: x ** j


def primitive_at(x):
    return lambda j: x ** (j + 1) / (j + 1)


def moment(k):
    return lambda j: F(1, j + k + 1)


def nodal(roots):
    coefficients = [O]
    for x in roots:
        coefficients = [s - x * t for s, t in zip([Z] + coefficients, coefficients + [Z])]
    return coefficients


def average(j):
    return Z if j % 2 else F(1, j + 1)


def omega_average(j):
    return average(j) - 2 * average(j + 2) + average(j + 4)


def forward_prefix(seed):
    a = [list(map(F, r)) for r in seed['A']]
    b9 = list(map(F, seed['b']))
    c9 = list(map(sum, a))
    q1, mid, q3 = map(F, ('1/4', '1/2', '3/4'))
    ops5 = [eval_at(Z), eval_at(O), moment(0), moment(1), eval_at(mid)]
    rows5 = [basis(0, 16), basis(7, 16), pad(a[7], 16),
             pad([u * v for u, v in zip(a[7], c9)], 16), basis(8, 16)]
    assert all(read(ops5, rows5, primitive_at(x))[0] == pad(a[i], 16)
               for x, i in ((q1, 10), (mid, 8), (q3, 9)))

    a.append(b9)
    old_mom = [pad([u * v ** j for u, v in zip(b9, c9)], 17) for j in range(4)]
    ops6 = [eval_at(Z), eval_at(O)] + [moment(j) for j in range(4)]
    rows6 = [basis(0, 17), basis(16, 17)] + old_mom
    r, det6 = read(ops6, rows6, primitive_at(mid))
    a.append(r)

    ops7 = ops6[:-1] + [lambda j: q1 ** j - q3 ** j, eval_at(mid)]
    quarter = [u - v for u, v in zip(basis(10, 18), basis(9, 18))]
    rows7 = rows6[:-1] + [quarter, basis(17, 18)]
    old_z = list(map(F, ('-5', '-1/3', '1/5', '1/3')))
    old_x = [(1 + u) / 2 for u in old_z]
    for x in old_x:
        r, det7 = read(ops7, rows7, primitive_at(x))
        a.append(r)
    assert all(unit(x-y) for i, x in enumerate([Z, O] + old_x) for y in ([Z, O] + old_x)[:i])
    assert sum(c * omega_average(j) for j, c in enumerate(nodal(old_z))) == 0
    ell = []
    for z in old_z:
        others = [u for u in old_z if u != z]
        value = sum(c * omega_average(j) for j, c in enumerate(nodal(others)))
        denom = (1 - z * z) ** 2 * prod(z - u for u in others)
        assert unit(denom)
        ell.append(value / denom)
    assert unit(ell[0])
    where_ell = [Z] * 18 + ell

    ops8 = ops6[:4] + list(map(eval_at, old_x))
    rows8 = rows6[:4] + [basis(i, 22) for i in range(18, 22)]
    new_z = list(map(F, ('-1/3', '1/5', '1/3', '-1/2', '1/2')))
    new_x = [(1 + u) / 2 for u in new_z]
    for x in new_x:
        r, det8 = read(ops8, rows8, primitive_at(x))
        a.append(r)

    ops9 = ops6[:3] + [lambda j: dot(ell, [x ** j for x in old_x])] + list(map(eval_at, new_x))
    rows9 = rows6[:3] + [where_ell] + [basis(i, 27) for i in range(22, 27)]
    integral, det9 = read(ops9, rows9, moment(0))
    assert integral == pad(b9, 27)
    assert list(map(sum, a))[16:] == [O, mid] + old_x + new_x
    return a, ops9, rows9, ell, (det6, det7, det8, det9)


def reverse_suffix():
    sites = [F(u + 6, 12) for u in (-6, -5, -4, -3, -2, -1, 0, 2, 3, 4, 5, 6, 8)]
    raw = {}
    for x in sites:
        other = [z for z in sites if z != x]
        den = prod(x - z for z in other)
        assert unit(den)
        raw[x] = sum(c / (j + 1) for j, c in enumerate(nodal(other))) / den
    quadrature = lambda j: sum(w * x ** j for x, w in raw.items())
    assert all(quadrature(j) == F(1, j + 1) for j in range(13))
    a, b, c = map(F, ('5/6', '1/2', '2/3'))
    assert raw[a] == F(6534, 79625) and unit(raw[a])
    interior = [x for x in sites if x not in (Z, O)]
    factor = {x: x * prod(x - z for z in interior if z != x) for x in interior}
    assert all(unit(v) for v in factor.values())
    eta = -F(1, 72) * raw[a] * factor[a]
    assert unit(eta)

    late = [x for x in interior if x not in (a, b, c)]
    # All nondonors are pure and may be permuted after the four reverse donors.
    x = [O, a, b, c] + late + late + [b, c, Z, O]
    n = len(x)
    mu_b, mu_c = eta / factor[b], 3 * eta / factor[c]
    w = ([O, raw[a], mu_b, mu_c] + [O] * 8 + [raw[k]-1 for k in late]
         + [raw[b]-mu_b, raw[c]-mu_c, raw[Z], raw[O]-1])
    u = [Z, -F(1, 72), O, F(1, 3)] + [eta / factor[k] for k in late] + [Z] * 12
    assert all(sum(v for z, v in zip(x, w) if z == k) == raw[k] for k in sites)
    assert all(unit(v) for v in w[:4])
    assert all(dot(w, [u[i] * x[i] ** j for i in range(n)]) == 0 for j in range(1, 11))
    assert dot(w, [u[i] * x[i] ** 11 for i in range(n)]) == eta

    y = [1 - k for k in x]
    y2 = [k * k for k in y]
    L = [[Z] * n for _ in range(n)]
    L[1][0] = y[1]
    for i in (2, 3):
        L[i][1] = (y[i] ** 2 / 2 + u[i]) / y[1]
        L[i][0] = y[i] - L[i][1]
    g = [dot(r, y2) - k ** 3 / 3 for r, k in zip(L, y)]
    v = [dot(r, u) for r in L]
    test = lambda j, i: w[i] * x[i] * (1-x[i]) * x[i] ** j
    control = [[test(j, i) for i in range(4, 12)] for j in range(8)]
    for arr in (g, v):
        arr[4:12], control_det = solve(control,
            [-sum(test(j, i) * arr[i] for i in range(4)) for j in range(8)])
        arr[12:] = [Z] * (n - 12)

    donor = [[O] * 4, y[:4], y2[:4], u[:4]]
    for i in range(4, n):
        L[i][:4], donor_det = solve(donor,
            [y[i], y[i] ** 2 / 2 + u[i], y[i] ** 3 / 3 + g[i], v[i]])
    assert not any(L[-1])
    for i, r in enumerate(L):
        assert not any(r[i:]) and sum(r) == y[i] and dot(r,y) == y[i] ** 2 / 2 + u[i]
        assert dot(r, y2) == y[i] ** 3 / 3 + g[i] and dot(r, u) == v[i]
    assert all(sum(test(j,i) * arr[i] for i in range(n)) == 0
               for j in range(8) for arr in (g, v))

    T = [[w[n-1-j] * L[n-1-j][n-1-i] / w[n-1-i] if L[n-1-j][n-1-i] else Z
          for j in range(n)] for i in range(n)]
    return x[::-1], T, w[::-1], eta, quadrature(13), (donor_det, control_det)


def merge(a, b):
    representatives, indices, rows, weights, mergers = [], {}, [], [], []
    assert len(a) == len(b)
    for i, (r, wt) in enumerate(zip(a, b)):
        assert len(r) <= i
        padded = [Z] * len(rows)
        for j, value in enumerate(r):
            padded[representatives[j]] += value
        key = tuple((j, value) for j, value in enumerate(padded) if value)
        if key not in indices:
            indices[key] = (len(rows), i+1)
            rows.append(key)
            weights.append(Z)
        j, original = indices[key]
        weights[j] += wt
        representatives.append(j)
        if i+1 != original:
            mergers.append((i+1,original))
    return rows, weights, mergers


def tree_checks(rows, weights, eta, q13):
    @lru_cache(None)
    def size(t):
        return 1 + sum(map(size,t))

    @lru_cache(None)
    def gamma(t):
        return size(t) * prod(map(gamma,t))

    @lru_cache(None)
    def phi(t):
        factors = list(map(ext,t))
        return [prod(r[i] for r in factors) for i in range(len(rows))]

    @lru_cache(None)
    def ext(t):
        y = phi(t)
        return [sum(c*y[j] for j,c in r) for r in rows]

    def defect(t):
        return gamma(t) * dot(weights, phi(t))-1

    def bush(n):
        return ((),)*(n-1)

    tested = {bush(n) for n in range(1,14)}
    for n in (10,11,12):
        r = bush(n)
        candidates = ((r,), ((r,),), ((),r), ((),(),r), ((),(r,)), (((),r),), (((r,),),))
        tested.update(t for t in candidates if size(t) <= 13)
    assert len(tested) == 24, len(tested)
    for t in tested:
        assert defect(t) == 0, (t, defect(t))
    t, b = ((),bush(12)), bush(14)
    assert size(t) == size(b) == 14 and gamma(t) == 168 and gamma(b) == 14
    dt, db = defect(t), defect(b)
    assert db == 14*q13-1 and dt/168 + db/28 == -eta
    assert -(dt/168 + db/28)/eta == 1
    return len(tested), t, b, dt, db


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--emit', action='store_true', help='print the exact canonical tableau')
    args = parser.parse_args()
    seed_bytes = (HERE.parent / 'erk-eleven-twelve-moment-splice' / 'paid9-seed.json').read_bytes()
    assert sha256(seed_bytes).hexdigest() == SEED_SHA256
    a, ops, data, ell, prefix_det = forward_prefix(json.loads(seed_bytes))
    clocks, block, virtual_weights, eta, q13, suffix_det = reverse_suffix()
    for i, row in enumerate(block):
        assert not any(row[i:])
        left, _ = read(ops, data,
            lambda j: primitive_at(clocks[i])(j) - dot(row,[x**j for x in clocks]))
        a.append(left + row[:i])
    assert list(map(sum,a))[27:] == clocks
    rows, weights, mergers = merge(a, [Z]*27 + virtual_weights)
    assert len(rows) == 41 and mergers == [(28,17),(29,1)] + [(i,i-8) for i in range(40,48)]
    entries = list(chain(weights, (c for r in rows for _, c in r)))
    assert all(paid_integer(c.denominator) for c in entries)
    common_denom = lcm(*(c.denominator for c in entries))
    n, t, b, dt, db = tree_checks(rows, weights, eta, q13)
    result = {
        'A': [[str(dict(r).get(j,Z)) for j in range(i)] for i,r in enumerate(rows)],
        'b': list(map(str,weights)),
        'coefficient_common_denominator': str(common_denom),
        'next_order': {'t': t, 'B': b, 'eta': str(eta), 'quadrature_moment_13': str(q13),
                       'cleared_defect_t': str(dt), 'cleared_defect_B': str(db)},
    }
    canonical = json.dumps(result,indent=2) + '\n'
    if args.emit:
        print(canonical,end='')
    else:
        assert (HERE / 'tableau-13-41.json').read_text() == canonical
        print('Exact reconstruction matches the sealed 41-row JSON.')
        print('Grade-nine contrast coefficients:', *map(str,ell))
        print('Paid forward and reverse determinants:', *map(str,prefix_det+suffix_det))
        print('Virtual row merges:', mergers, '| physical rows:',len(rows))
        print('Paid common denominator:', common_denom)
        print(f'Checked {n} sample rooted conditions (not exhaustive).')
        print('eta, Q[x^13], D_t, D_B:', *map(str,(eta,q13,dt,db)))
        print('Verified the two cleared defect identities and the explicit unit combination.')


if __name__ == '__main__':
    main()
