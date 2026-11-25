#!/usr/bin/env python3
"""Check parity arithmetic and the nodal-polynomial block embedding."""


def width(p, j):
    assert p >= 1 and 0 <= j < p
    return 1 + min(j, p-1-j)


def census(p, r):
    return sum(width(p, r-2*k) for k in range(r//2+1))


def floor(p):
    return max(census(p, r) for r in range(p)) if p > 0 else 0


def rank(mod, rows):
    a = [[v % mod for v in r] for r in rows]
    q = 0
    for j in range(len(a[0]) if a else 0):
        i = next((i for i in range(q, len(a)) if a[i][j]), None)
        if i is None:
            continue
        a[q], a[i] = a[i], a[q]
        for h in range(q+1, len(a)):
            c = a[h][j] * pow(a[q][j], -1, mod) % mod
            a[h] = [(x-c*y) % mod for x, y in zip(a[h], a[q])]
        q += 1
    return q


def main():
    index_count = block_count = 0
    for p in range(1, 49):
        for q in range((p-1)//2+1):
            m = p-2*q
            ds = [sum(max(0, width(p, r-2*k)-q) for k in range(r//2+1))
                  for r in range(p)]
            assert max(ds)==floor(m)
            for h in range(m):
                assert width(p,h+q)==q+width(m,h)
                index_count += 1
                if p <= 20:
                    # P of exact degree q; representation in the original
                    # unmasked coefficient packet is triangular with unit lead.
                    polys = [[0]*a+[1]*(q+1)+[0]*(width(m,h)-1-a)
                             for a in range(width(m,h))]
                    assert all(len(poly)==width(p,h+q) for poly in polys)
                    assert rank(5, polys)==width(m,h)
                    block_count += 1
            for r in range(m):
                assert sum(width(p, r+q-2*k)-q for k in range(r//2+1))==census(m,r)
    assert [floor(p) for p in (3,4,5,6,7,8)]==[2,3,5,6,8,10]
    print("Width and parity checks:", index_count)
    print("Exact coefficient-block ranks:", block_count)
    print("All cutoff arithmetic checks pass. No tableau attainment is inferred.")


if __name__ == '__main__':
    main()
