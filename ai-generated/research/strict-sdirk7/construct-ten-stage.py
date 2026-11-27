"""Reproduce the three-helper, seven-tail rational linear solve exactly."""
from fractions import Fraction as F
from pathlib import Path
import json

def solve(rows, rhs, avoid=()):
    n = len(rows[0])
    M = [[F(a) for a in row] + [F(y)] for row, y in zip(rows, rhs)]
    pivots = []
    for j in range(n):
        i = len(pivots)
        k = next((k for k in range(i, len(M)) if M[k][j] and all(M[k][j].numerator % p for p in avoid)), None)
        if k is None:
            continue
        M[i], M[k] = M[k], M[i]
        M[i] = [v / M[i][j] for v in M[i]]
        for k in range(len(M)):
            if k != i and M[k][j]:
                factor = M[k][j]
                M[k] = [x - factor * y for x, y in zip(M[k], M[i])]
        pivots.append(j)
    assert not any(row[-1] for row in M[len(pivots):])
    out = [F(0)] * n
    for i, j in enumerate(pivots):
        out[j] = M[i][-1]
    return out

def dot(u, v):
    return sum(a*b for a, b in zip(u, v))

def construct(z, clocks, avoid=()):
    c = list(map(F, clocks))
    k = len(c)
    C = [[x**i for x in c] for i in range(7)]
    b = solve(C, [F(z**i, i+1) for i in range(7)], avoid)
    b1 = [w*x for w, x in zip(b, c)]
    b2 = [w*x*x for w, x in zip(b, c)]
    ending = [[int(j==i) for j in range(k)] for i in (k-2, k-1)]
    r = solve(C[:5] + ending,
              [dot(b, C[j+2])/(j+1) for j in range(5)] +
              [b[-2] * (c[-2] + c[-1] * (z - c[-2] - 1)), b[-1] * c[-1]], avoid)
    slots = [(i, j) for i in range(k) for j in range(i)]
    rows, rhs = [], []
    for k0 in range(k):
        rows.append([c[j] if i == k0 else 0 for i, j in slots])
        rhs.append(c[k0]**2/2 - c[k0])
    for j0 in range(k):
        rows.append([b[i] if j == j0 else 0 for i, j in slots])
        rhs.append(b[j0] * (z - c[j0] - 1))
        rows.append([b1[i] if j == j0 else 0 for i, j in slots])
        rhs.append(r[j0] - b1[j0])
    for row in (r, b2):
        for degree in (0, 2, 3):
            rows.append([row[i] * C[degree][j] for i, j in slots])
            rhs.append(dot(row, C[degree+1])/(degree+1) - dot(row, C[degree]))
    strict = solve(rows, rhs, avoid)
    B = [[F(i==j) for j in range(k)] for i in range(k)]
    for (i, j), x in zip(slots, strict):
        B[i][j] = x

    # Use identical helpers to the earlier 11-stage rational witness.
    # Their clocks are (1,2,0) and twice their quadratic defect equals that column.
    T = [[F(1), F(0), F(0)], [F(1), F(1), F(0)], [F(-2), F(1), F(1)]]
    for x, row in zip(c, B):
        a = x - sum(row)
        b_feed = x**3/3 - dot(row, C[2])
        T.append([-b_feed, b_feed/2, a + b_feed/2] + row)
    T = [row + [F(0)] * (k+3-len(row)) for row in T]
    return [[x/z for x in row] for row in T], [F(0)]*3 + b

if __name__ == '__main__':
    for name in ('ten-stage-rational.json', 'ten-stage-rational-alt.json'):
        data = json.loads(Path(__file__).with_name(name).read_text())
        A, b = construct(data['z'], data['normalized_tail_clocks'], data.get('avoid_pivot_primes', ()))
        assert A == [[F(x, data['stage_den']) for x in row] for row in data['A']]
        assert b == [F(x, data['weight_den']) for x in data['b']]
        print(f'{name}: exact linear solve reproduced the literal tableau.')
