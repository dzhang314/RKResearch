#!/usr/bin/env python3
"""Exact stdlib regression of the free marked column and leakage identity.

The Simpson rule serves both purposes: it reaches order four, so the
order-three case needs the independent non-bush defect, while the
order-four case pays the actual mixed test of the visible selector.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import prod

C = tuple(map(Q, (0, Q(1, 2), 1)))
B = dict(zip((1-c for c in C), (Q(1, 6), Q(2, 3), Q(1, 6))))
A0, A1 = Q(1, 2), Q(1, 4)
MARKS = (A0, A1)
REPAIR = (Q(1, 11), Q(2, 11), Q(3, 11))


def poly_mul(f, g):
    h = [Q(0)] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            h[i+j] += a*b
    return h


def moments_to_edges(nodes, mom):
    assert len(nodes) == len(mom)
    assert len(set(nodes)) == len(nodes)
    ans = []
    for x in nodes:
        num = [Q(1)]
        den = Q(1)
        for y in nodes:
            if y != x:
                num = poly_mul(num, [-y, Q(1)])
                den *= x-y
        ans.append(sum(a*b for a, b in zip(num, mom))/den)
    for k, mk in enumerate(mom):
        assert sum(a*z**k for a, z in zip(ans, nodes)) == mk
    return ans


def build(p, gamma, marked):
    A, c, b = [], [], []
    exact_by_unary = p == 3

    def append(x, w=Q(0), links=None):
        links = links or {}
        i = len(A)
        row = tuple(links.get(j, Q(0)) for j in range(i)) + (gamma,)
        assert sum(row) == x
        A.append(row)
        c.append(x)
        b.append(w)
        return i

    def pure_append(x, donors):
        nodes = [c[j] for j in donors]
        mom = [x**(k+1)/(k+1)-gamma*x**k for k in range(len(nodes))]
        return append(x, links=dict(zip(donors, moments_to_edges(nodes, mom))))

    prior = (append(gamma),)
    if p == 4:  # The bank of two rows pure through tree order two.
        prior = tuple(pure_append(z, prior) for z in (Q(5, 11), Q(6, 11)))
    mark_ids = {a: pure_append(1-a, prior) for a in MARKS}
    repairs = tuple(pure_append(z, prior) for z in REPAIR)
    assert len(repairs) == (p if exact_by_unary else p-1)
    for x in C:
        u = 1-x
        w = B[u]
        fixed = {mark_ids[a]: marked.get((a, u), Q(0))/w for a in MARKS}
        mom = [x**(k+1)/(k+1)-gamma*x**k-sum(v*c[j]**k for j,v in fixed.items())
               for k in range(len(repairs))]
        if exact_by_unary and u == 0:
            mom[p-1] += 1
        corrections = moments_to_edges(REPAIR, mom)
        append(x,w,{**fixed, **dict(zip(repairs,corrections))})

    assert tuple(sum(row) for row in A) == tuple(c)
    assert all(len(row)==i+1 and row[i]==gamma for i,row in enumerate(A))
    for u in set(1-x for x in c):
        assert sum(w for x,w in zip(c,b) if 1-x==u)==B.get(u,Q(0))
    return tuple(A), tuple(c), tuple(b)


@lru_cache(None)
def trees(n):
    if n == 1:
        return ((),)
    candidates = [(k,t) for k in range(1,n) for t in trees(k)]

    def forests(left, minj):
        if left == 0:
            yield ()
            return
        for j in range(minj,len(candidates)):
            k,t = candidates[j]
            if k > left:
                break
            for tail in forests(left-k,j):
                yield (t,)+tail

    return tuple(forests(n-1,0))


@lru_cache(None)
def size(T):
    return 1+sum(map(size,T))


@lru_cache(None)
def fact(T):
    return size(T)*prod(map(fact,T))


def check_actual_order(A,c,b,p):
    @lru_cache(None)
    def phi(T):
        children = tuple(map(phi,T))
        return tuple(prod(sum(a*v[j] for j,a in enumerate(row)) for v in children)
                     for row in A)

    def scaled(T):
        return fact(T)*sum(w*v for w,v in zip(b,phi(T)))

    counts = tuple(len(trees(n)) for n in range(1,p+1))
    assert counts == (1,1,2,4)[:p]
    for n in range(1,p+1):
        assert all(size(T)==n and scaled(T)==1 for T in trees(n))
    if p==3:
        assert scaled(((),)*p)==1  # The next bush is paid by Simpson.
        assert scaled((((),)*(p-1),))!=1
    else:
        assert scaled(((),)*p)!=1
    return sum(counts)


def grouped_full(A,c,b,a,F):
    x = tuple(1-v for v in c)
    return sum(b[j]*A[j][i]*F(x[j])
               for i in range(len(c)) if x[i]==a
               for j in range(i,len(c)))


def hidden(A,c,b,a,F):
    x = tuple(1-v for v in c)
    qa = lambda y: prod(y-u for u in B if u!=a)
    h = tuple(qa(y) if y not in B else Q(0) for y in x)
    return sum(b[j]*F(x[j])*sum(v*h[i] for i,v in enumerate(row))
               for j,row in enumerate(A))


def main():
    assert all(sum(w*(1-u)**k for u,w in B.items())==Q(1,k+1) for k in range(4))
    assert sum(w*(1-u)**4 for u,w in B.items())==Q(5,24)!=Q(1,5)
    for gamma in (Q(0),Q(1,7)):
        l0 = {(A0,Q(0)):-B[A0]*gamma}
        l1 = {**l0,(A0,Q(0)):l0[A0,Q(0)]+Q(2,7),(A0,Q(1)):Q(1,9),(A1,A0):Q(4,13)}
        for p in (3,4):
            r0,r1 = [build(p,gamma,l) for l in (l0,l1)]
            assert r0[1:]==r1[1:]
            F0 = lambda x: Q(1)
            Fs = (F0, lambda x: x, lambda x: x*x, lambda x: x-A0)
            for r,lam in ((r0,l0),(r1,l1)):
                A,c,b = r
                assert check_actual_order(A,c,b,p)==(4 if p==3 else 8)
                for a in MARKS:
                    for F in Fs:
                        expected=B.get(a,Q(0))*gamma*F(a)+sum(lam.get((a,u),Q(0))*F(u) for u in B)
                        assert grouped_full(A,c,b,a,F)==expected
            assert grouped_full(*r0,A0,F0)==0
            assert grouped_full(*r1,A0,F0)==Q(25,63)
            # A true stop root does not constrain the change in the source.
            Froot = Fs[-1]
            assert Froot(A0)==0
            assert grouped_full(*r1,A0,Froot)-grouped_full(*r0,A0,Froot)==-Q(11,126)
            if p==4:
                assert len(B)+1==p  # Actual mixed charge, deg F=0.
                assert hidden(*r0,A0,F0)==-Q(1,12)
                assert hidden(*r1,A0,F0)==Q(1,63)
                qa = prod(A0-u for u in B if u!=A0)
                for r in (r0,r1):
                    assert grouped_full(*r,A0,F0)+hidden(*r,A0,F0)/qa==B[A0]*A0==Q(1,3)
            tag = "strict ERK" if gamma==0 else "positive common-diagonal SDIRK"
            print(f"{tag}, exact p={p}: two marked column maps; identical physical clocks and weights.")
            print("  constant-profile stop source changes 0 -> 25/63; true-root source change -11/126.")
            if p==3:
                print("  next pure bush passes, but the independent unary-bush condition fails.")
            else:
                print("  paid visible selector, omitted leakage -1/12 -> 1/63; true weighted local value 1/3.")
    print("PASS: literal rooted trees and exact rational column/leakage identities.")


if __name__ == "__main__":
    main()
