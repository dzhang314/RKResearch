#!/usr/bin/env python3
"""Instantiate and check the uniform rank-two counterfamily over exact Q."""
from argparse import ArgumentParser
from fractions import Fraction as Q
from functools import lru_cache
from math import prod


def dot(row, values):
    return sum(coef * values[j] for j, coef in row.items())


def times_x_minus(poly, x):
    out = [Q(0)] * (len(poly) + 1)
    for j, a in enumerate(poly):
        out[j] -= x*a
        out[j+1] += a
    return out


@lru_cache(maxsize=None)
def lagrange(nodes):
    assert len(set(nodes)) == len(nodes)
    basis = []
    for i, x in enumerate(nodes):
        out = [Q(1)]
        den = Q(1)
        for j, y in enumerate(nodes):
            if i != j:
                out = times_x_minus(out, y)
                den *= x-y
        basis.append(tuple(a / den for a in out))
    return tuple(basis)


def solve(nodes, moments):
    assert len(nodes) == len(moments)
    weights = tuple(sum(a*b for a, b in zip(poly, moments))
                    for poly in lagrange(nodes))
    assert all(sum(w*x**k for w, x in zip(weights, nodes)) == m
               for k, m in enumerate(moments))
    return weights


def verify(p):
    assert p >= 3
    A = [dict(enumerate(map(Q, row)))
         for row in [(1,), (1,1), (1,1,1), (Q(7,3),Q(-5,3),Q(1,3),1)]]
    c = list(map(Q, (1,2,3,2)))
    # Independent seed calculation.
    q0 = [2*dot(row, c)-x*x for row, x in zip(A, c)]
    r0 = [3*dot(row, [y*y for y in c])-x**3 for row, x in zip(A, c)]
    nq0 = [dot(row, q0)-y for row, y in zip(A, q0)]
    assert list(map(sum, (row.values() for row in A))) == c
    assert q0 == [1,2,3,0] and nq0 == [0,1,3,0] and r0 == [2,7,15,0]
    assert [x-y for x,y in zip(c,q0)] == [0,0,0,2]
    # Certified row-grade tags, for the structural receipt below.
    grades = [1,1,1,3]
    nodes = tuple(map(Q, range(-1,-p-1,-1)))

    for x in nodes:
        i = len(A)
        # Subtract the diagonal and, except on the first row, the fixed edge.
        mu = [x**(j+1)/(j+1)-x**j for j in range(3)]
        edge = {}
        if i > 4:
            edge[i-1] = Q(1)
            mu = [m-c[i-1]**j for j,m in enumerate(mu)]
        w3 = mu[1]/2
        old = solve(tuple(c[:3]), [m-w3*2**j for j,m in enumerate(mu)])
        row = {**dict(enumerate(old)), 3:w3, **edge, i:Q(1)}
        if i == 4:
            assert row[3] == Q(3,4)
        A.append(row)
        c.append(x)
        assert all(dot(row, [y**j for y in c]) == x**(j+1)/(j+1)
                   for j in range(3))
        assert dot(row, q0 + [Q(0)] * (i-3)) == 0
        grades.append(3)

    # Each earlier used input need only be exact through grade g-1.
    # The triangular tree recursion earns grade g at the receiving row.
    for g in range(4,p):
        donors = list(range(len(A)-p, len(A)-p+g))
        assert len(donors) == g and max(donors) < len(A)-1
        donor_nodes = tuple(c[j] for j in donors)
        for x in nodes:
            i = len(A)
            mu = [x**(j+1)/(j+1)-x**j-c[i-1]**j for j in range(g)]
            row = {**dict(zip(donors, solve(donor_nodes, mu))), i-1:Q(1), i:Q(1)}
            assert all(grades[j] >= g-1 for j,a in row.items() if a and j<i)
            A.append(row)
            c.append(x)
            assert all(dot(row, [y**j for y in c]) == x**(j+1)/(j+1)
                       for j in range(g))
            grades.append(g)

    s = len(A)
    assert s == 4+p*max(1,p-3)
    assert all(row[i] == 1 and max(row) == i for i,row in enumerate(A))
    assert all(A[i][i-1] for i in range(1,s))
    assert [sum(row.values()) for row in A] == c
    q = [2*dot(row, c)-x*x for row,x in zip(A,c)]
    r = [3*dot(row, [y*y for y in c])-x**3 for row,x in zip(A,c)]
    nq = [dot(row, q)-y for row,y in zip(A,q)]
    assert not any((*q[4:], *r[4:], *nq[4:]))
    assert all((x-1)*y == 2*z and rr == (x+1)*y+z
               for x,y,z,rr in zip(c,q,nq,r))
    assert q[0]*nq[1]-q[1]*nq[0] == 1     # rank is exactly two

    # The grade tags prove all paid tree profiles on weight support.
    assert min(grades[-p:]) >= p-1
    w = solve(nodes, tuple(Q(1,k+1) for k in range(p)))
    assert all(w)
    assert w[-1]*prod(A[i][i-1] for i in range(1,s)) != 0
    # Exact first unpaid bush failure (not just a floating comparison).
    vanisher = [Q(1)]
    for x in nodes:
        vanisher = times_x_minus(vanisher, x)
    I_vanisher = sum(a/(k+1) for k,a in enumerate(vanisher))
    assert I_vanisher > 0
    assert sum(b*x**p for b,x in zip(w,nodes)) - Q(1,p+1) == -I_vanisher
    print(f'p={p:2}: s={s:3}, exact order p, full tall width, {p} live fibres, dim D4 = 2')


if __name__ == '__main__':
    cli = ArgumentParser(description=__doc__)
    cli.add_argument('p', nargs='*', type=int, default=[3,4,5,9,20])
    for p in cli.parse_args().p:
        verify(p)
