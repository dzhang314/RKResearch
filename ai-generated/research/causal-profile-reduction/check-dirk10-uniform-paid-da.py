#!/usr/bin/env python3
"""Exact transparent replay of the uniform paid DA suffix obstruction."""

from itertools import permutations
import sys


def check(p):
    roots = tuple(v for v in range(p) if (42*v**4-84*v**3+56*v*v-14*v+1) % p == 0)
    assert len(roots) == 4

    def d(a, b):
        assert b % p
        return a*pow(b % p, -1, p) % p

    result = []
    for U, W, R in permutations(roots, 3):
        J = R*U*U-4*R*U*W+R*W*W+U*U*W+U*W*W
        L = 3*R*R-5*R*(U+W)+10*U*W
        M = 4*R*U*U-13*R*U*W+4*R*W*W+U*U*W+U*W*W
        k = {U: d(-U**3, 6), W: d(W**3*(2*U-W), 6*(U-2*W)),
             R: d(R**3*(2*U-W)*L, 6*M)}
        assert all(k.values()) and J % p
        F = {U: d(U, 2)}
        b1 = d(W*W, 2)
        b2 = d(W**3, 3)-k[W]
        F[W] = d(sum(k[i]*d(b2-j*b1, i*(i-j)) for i, j in [(U,W),(W,U)]), k[W])
        c1 = d(R*R, 2)
        c2 = d(R**3, 3)-k[R]
        c3 = d(R**4, 4)-(U+d(U, 2))*k[R]
        F[R] = d(sum(k[i]*d(c3-(j+h)*c2+j*h*c1, i*(i-j)*(i-h))
               for i,j,h in [(U,W,R),(W,U,R),(R,U,W)]), k[R])
        delta = ((W-R)*F[U]+(R-U)*F[W]+(U-W)*F[R]) % p
        square = d(-3*(R-U)*(R-W)*(U-W)*J*J, (U-2*W)*(2*U-W)*L*M)
        assert delta and delta == square
        result.append(delta)
    assert len(result) == 24
    print(f"mod {p}: nonzero DA affine defect on all {len(result)} ordered fixed triples")


if __name__ == "__main__":
    for prime in map(int, sys.argv[1:]) if len(sys.argv)>1 else (419,719):
        check(prime)
