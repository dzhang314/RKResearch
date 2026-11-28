"""Three exact counts for the two fixed tableaux; no external dependencies."""
from fractions import Fraction as F
from math import factorial, prod
from collections import Counter

N = 9
TOTAL = 8 * 2**N * factorial(N)


def no_place(usable):
    w = [F(0)] + [
        F(int(not usable(j)) + int(not usable(2*j)), 2)
        for j in range(1, N+1)
    ]
    counts = [F(1)]
    for n in range(1, N+1):
        counts.append(sum(w[j]*counts[n-j] for j in range(1, n+1))/n)
    return counts[-1] * F(sum(m for j,m in ((1,1),(2,5),(4,2))
                                if not usable(j)), 8)


def partitions(n, cap):
    if n == 0:
        yield ()
    for j in range(1, min(n, cap) + 1):
        for p in partitions(n-j, j):
            yield (j, *p)


def no_place_by_partitions(usable):
    no = F(0)
    for p in partitions(N, N):
        den = prod(i**m*factorial(m) for i,m in Counter(p).items())
        w = prod(F(int(not usable(j))+int(not usable(2*j)), 2) for j in p)
        no += w/den
    return no * F(sum(m for j,m in ((1,1),(2,5),(4,2)) if not usable(j)), 8)


def no_place_by_integer_cycle(usable):
    counts = [1]
    for n in range(1, N+1):
        counts.append(sum(
            factorial(n-1)//factorial(n-j) * 2**(j-1) *
            (int(not usable(j))+int(not usable(2*j))) * counts[n-j]
            for j in range(1, n+1)
        ))
    return F(counts[-1] * sum(m for j,m in ((1,1),(2,5),(4,2))
                              if not usable(j)), TOTAL)


def verified_no_place(usable):
    results = tuple(f(usable) for f in (
        no_place, no_place_by_partitions, no_place_by_integer_cycle
    ))
    assert results[0] == results[1] == results[2]
    return results[0]


survival = [F(1)] + [verified_no_place(lambda r: r <= m) for m in range(1, 5)]
least = [a-b for a,b in zip(survival, survival[1:])]
assert least == [F(99646543, 212336640), F(75818719, 165150720),
                 F(913, 82944), F(175979, 2903040)]
for m, d in enumerate(least, 1):
    print(f"Least residue degree {m}: {d} ({float(100*d):.9f}%)")
assert sum(least) == 1
ks = [1 - verified_no_place(lambda r: k % r == 0) for k in range(1, 13)]
assert ks[:4] == [least[0], F(1347553, 1451520), F(13001399, 23592960), 1]
for k, d in enumerate(ks[:4], 1):
    print(f"Specified extension degree {k}: {d} ({float(100*d):.9f}%)")
print("Three independent counts agree at all thresholds and for extension degrees 1–12.")
