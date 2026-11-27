from fractions import Fraction as Q
from itertools import combinations_with_replacement
from math import lcm

rows = []
for k in range(3):
    denominators = [(j + k + 2) * (j + k + 3) for j in range(6)]
    scale = lcm(*denominators)
    rows.append(tuple((scale // d) % 4 for d in denominators))
assert rows == [(0, 2, 2, 0, 0, 3), (2, 2, 0, 0, 1, 3), (2, 0, 0, 1, 3, 0)]
factors = [(a, 1) for a in range(4)] + [(1, 0), (1, 2)]
count = 0
for group in combinations_with_replacement(factors, 5):
    p = [1]
    for a, b in group:
        p = [(a*x + b*y) % 4 for x, y in zip(p + [0], [0] + p)]
    assert any(sum(x*y for x, y in zip(row, p)) % 4 for row in rows)
    count += 1
assert count == 252
x = [Q(0), Q(1,9), Q(4,13), Q(2,5), Q(3,5), Q(9,13), Q(8,9), Q(1)]
w = [Q(46201,1451520), Q(176969853,1001960960), Q(815730721,5391671040),
     Q(4609375,32864832)]
w += w[::-1]
for k in range(10):
    assert sum(wi * xi**k for xi, wi in zip(x, w)) == Q(1, k+1)
assert sum(wi * xi**10 for xi, wi in zip(x, w)) - Q(1, 11) == Q(919, 677605500)
print('All 252 normalized factor multisets fail modulo 4; all 10 eight-site moments pass exactly.')
