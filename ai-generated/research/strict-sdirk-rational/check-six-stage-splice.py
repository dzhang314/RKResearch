#!/usr/bin/env python3
"""Derive the six-stage shared splice and replay the literal RK trees over Q."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations_with_replacement
from math import prod

# Reflect chronological order for the weighted-dual stage rows.
x = tuple(map(Q, (0, Q(1, 5), Q(2, 3), 1)))
y = tuple(1 - t for t in x)
w = (Q(1, 24), Q(125, 336), Q(27, 56), Q(5, 48))
assert all(sum(wi * xi**k for wi, xi in zip(w, x)) == Q(1, k+1) for k in range(5))

# Grade-two residuals of the original zero-weight core at c=(1,0).
def residual(xi):
    return xi*(xi-1), 1-2*xi+xi*xi/2

# A common diagonal 1 and reverse row sums y force the first two errors.
low = (Q(1, 2), 2*y[1]-1-y[1]**2/2)
F = [residual(t) for t in x]
j = 0  # N(x)=x*(x-1) vanishes at the final adjustable endpoint.
assert F[3][j] == 0 and F[2][j] != 0 and F[3][1] != 0
delta2 = -sum(w[i]*low[i]*F[i][j] for i in range(2))/(w[2]*F[2][j])
delta3 = -sum(w[i]*t*F[i][1] for i,t in enumerate((*low, delta2)))/(w[3]*F[3][1])
delta = (*low, delta2, delta3)
assert delta == (Q(1, 2), Q(7, 25), Q(-7, 45), Q(9, 5))
assert all(sum(wi*di*fi[j] for wi,di,fi in zip(w,delta,F)) == 0 for j in range(2))

# Row recovery: use the *same* two distinct donor clocks for both repairs.
L = [[Q(i==j) for j in range(4)] for i in range(4)]
L[1][0] = y[1]-1
for i in (2,3):
    s = y[i]-1
    t = y[i]**2/2 + delta[i] - y[i]
    L[i][1] = (t-y[0]*s)/(y[1]-y[0])
    L[i][0] = s-L[i][1]
assert [sum(row) for row in L] == list(y)
assert [sum(a*yi for a,yi in zip(row,y))-yi**2/2 for row,yi in zip(L,y)] == list(delta)
assert L == [
    [Q(1),Q(0),Q(0),Q(0)], [Q(-1,5),Q(1),Q(0),Q(0)],
    [Q(1,2),Q(-7,6),Q(1),Q(0)], [Q(13),Q(-14),Q(0),Q(1)],
]

# Convert to primal chronological T; build the coupling for Π=(x,1-x).
idx = tuple(reversed(range(4)))
T = [[L[j][i]*w[j]/w[i] for j in idx] for i in idx]
xc = [x[i] for i in idx]
A = [[Q(1),Q(0),Q(0),Q(0),Q(0),Q(0)],
     [Q(-1),Q(1),Q(0),Q(0),Q(0),Q(0)]]
for row,t in zip(T,xc):
    k0=t**2/2-sum(a*s for a,s in zip(row,xc))
    k1=t-t**2/2-sum(a*(1-s) for a,s in zip(row,xc))
    A.append([k0,k1,*row])
b = [Q(0),Q(0),*[w[i] for i in idx]]
published_rows = [
    (1,),
    (-1,1),
    (Q(-1,2),Q(1,2),1),
    (Q(-4,9),Q(1,9),0,1),
    (Q(1187,250),Q(-29,250),Q(-98,25),Q(-189,125),1),
    (-36,Q(-3,2),Q(65,2),Q(81,14),Q(-25,14),1),
]
literal = [list(r)+(6-len(r))*[0] for r in published_rows]
assert A == literal and b == [0,0,Q(5,48),Q(27,56),Q(125,336),Q(1,24)]
assert all(A[i][i] == 1 and all(v == 0 for v in A[i][i+1:]) for i in range(6))
assert list(map(sum,A)) == [1,0,*xc]

# No use of the splice criterion in this second check: direct tree weights.
@cache
def order(t):
    return 1+sum(map(order,t))

@cache
def factorial(t):
    return order(t)*prod(map(factorial,t))

@cache
def phi(t):
    child = list(map(phi,t))
    return tuple(prod(sum(a*v for a,v in zip(row,q)) for q in child) for row in literal)

def weight(t):
    return sum(wi*pi for wi,pi in zip(b,phi(t)))

def discrepancies(n):
    return [weight(t)-Q(1,factorial(t)) for t in trees[n]]

trees={1:[()]}
for n in range(2,7):
    pool=[t for k in range(1,n) for t in trees[k]]
    trees[n]=[m for a in range(1,n) for m in combinations_with_replacement(pool,a)
              if sum(map(order,m))==n-1]
    assert len(trees[n])==len(set(trees[n]))
assert [len(trees[n]) for n in range(1,7)] == [1,1,2,4,9,20]
assert all(e==0 for n in range(1,6) for e in discrepancies(n))
tall=()
for _ in range(5):
    tall=(tall,)
tall_weight=weight(tall)
assert tall_weight != Q(1,720)
print("Literal six-stage rational tableau: 17 paid trees passed.")
print("Order-six failures:", sum(e != 0 for e in discrepancies(6)), "of", len(trees[6]))
print("Order-six tall weight:", tall_weight, "instead of 1/720.")
print("Shared reverse donor clocks:", y[:2], "; paid defects:", delta)
