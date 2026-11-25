#!/usr/bin/env python3
"""Exact repeated-clock construction and separate rooted-tree replay."""
from fractions import Fraction as Q
from functools import cache
from itertools import combinations_with_replacement
from math import isqrt, prod

# Both cleared expressions have degrees at most (6,2) in (a,u).
# This rectangular exact evaluation proves the displayed factorization.
def cleared_residual(a,u):
    r = 1-3*a*a
    d = 5*a*a-3
    return (1+2*u+4*a*u-2*a*a-u*u)*d*r-(1+a)**2*(4*a*u+5*r*u*u+d)

def factored_residual(a,u):
    return 2*(u-a)*((3*a*a-1)*(5*a*a+5*a+1)*u-(5*a*a-3)*(3*a**3-3*a-1))

assert all(cleared_residual(a,u) == factored_residual(a,u)
           for a in range(7) for u in range(3))

# Choose a rational endpoint of the derived four-site family, without search.
a = Q(1)
gamma = (1+a)/2
u = (5*a*a-3)*(3*a**3-3*a-1)/((3*a*a-1)*(5*a*a+5*a+1))
v = -(5*a*a+5*a+1)/(5*(3*a**3-3*a-1))
t = (a, u, v, -a)
assert len(set(t)) == 4
assert 1+5*(u*v-a*a)/3-5*a*a*u*v == 0

def derivative(z):
    return prod(z-r for r in t if r != z)

def deleted_mean(z):
    r = [r for r in t if r != z]
    return -sum(r)/3-prod(r)

h = {z: deleted_mean(z) for z in t}
w = {z: h[z]/derivative(z) for z in t}
assert all(sum(wi*z**k for z,wi in w.items()) == (Q(1,k+1) if k%2 == 0 else 0)
           for k in range(5))

def second(xi):
    return 2*gamma*xi-gamma**2-xi**2/2

q1 = gamma**2/2
q2 = second((1+u)/2)
alpha = h[a]*q1
assert q2*h[u] == alpha
q5 = alpha/h[-a]
lam = gamma**2/(2*q5)
q4 = second((1-v)/2)/lam
mean = alpha/h[v]
aggregate_square = sum(w[z]*(alpha/h[z])**2 for z in t)
delta = q4-mean
mass = w[v]
assert delta != 0 and mass*delta**2-aggregate_square != 0
s = -aggregate_square*mass/(mass*delta**2-aggregate_square)
q3 = (mass*mean-s*q4)/(mass-s)

c = (gamma,(1+u)/2,(1+v)/2,(1+v)/2,(1-a)/2)
b = (w[a],w[u],mass-s,s,w[-a])
q = (q1,q2,q3,q4,q5)
def dot(x,y):
    return sum(xi*yi for xi,yi in zip(x,y))

assert all(b)
assert all(dot(b,[x**k for x in c]) == Q(1,k+1) for k in range(5))
assert all(dot(b,[qi*x**k for x,qi in zip(c,q)]) == 0 for k in range(3))
assert dot(b,[qi**2 for qi in q]) == 0

# Two first moments in each row and column of the strictly lower correction.
y = [1-x for x in c]
ell = [bi*(ci-gamma) for bi,ci in zip(b,c)]
rho = [bi*(ci**2/2+qi-gamma*ci) for bi,ci,qi in zip(b,c,q)]
ups = [bi*(yi-gamma) for bi,yi in zip(b,y)]
nu = [bi*((1-ci**2)/2-lam*qi-gamma*ci) for bi,ci,qi in zip(b,c,q)]
S = [[Q(0)]*5 for _ in range(5)]
def pair(total,weighted,x0,x1):
    z = (x1*total-weighted)/(x1-x0)
    return z,total-z

S[1][0] = ell[1]
S[4][3] = ups[3]
S[3][2],S[4][2] = pair(ups[2],nu[2],c[3],c[4])
for i in range(2,5):
    d0 = sum(S[i][j] for j in range(2,i))
    d1 = sum(S[i][j]*c[j] for j in range(2,i))
    S[i][0],S[i][1] = pair(ell[i]-d0,rho[i]-d1,c[0],c[1])
assert [sum(row) for row in S] == ell
assert [dot(row,c) for row in S] == rho
assert [sum(col) for col in zip(*S)] == ups
assert [dot(col,c) for col in zip(*S)] == nu
A = tuple(tuple(S[i][j]/b[i]+(gamma if i==j else 0) for j in range(5)) for i in range(5))
assert all(A[i][i] == gamma != 0 and all(aij == 0 for aij in A[i][i+1:]) for i in range(5))

# Direct literal tableau replay, with no normal-form assumptions.
lower_rows = (
    ("1",),
    ("-6/11", "1"),
    ("14907/2900", "-13167/2900", "1"),
    ("-15818893/310500", "190522673/6520500", "7279319/326025", "1"),
    ("173/92", "-6655/2484", "-28271375/155877831", "-5000/251011", "1"),
)
literal_A = tuple(tuple(map(Q, row))+(Q(0),)*(5-len(row)) for row in lower_rows)
literal_b = tuple(map(Q, (
    "47/216", "14641/22680", "-4940875/569292948", "14375/8032352", "23/160",
)))
assert A == literal_A and b == literal_b
assert sum(bi < 0 for bi in literal_b) == 1
literal_adj = tuple(tuple(literal_A[j][i]*literal_b[j]/literal_b[i] for j in range(5))
                    for i in range(5))
assert all(sum(row) == yi for row,yi in zip(literal_adj,y))
assert all(dot(row,y)-yi**2/2 == lam*qi for row,yi,qi in zip(literal_adj,y,q))
square = -15*prod(literal_b)
assert square > 0
square_root = Q(isqrt(square.numerator),isqrt(square.denominator))
assert square_root**2 == square

@cache
def order(tree):
    return 1+sum(map(order,tree))

@cache
def factorial(tree):
    return order(tree)*prod(map(factorial,tree))

@cache
def phi(tree):
    child = list(map(phi,tree))
    return tuple(prod(dot(row,v) for v in child) for row in literal_A)

trees = {1:[()]}
for n in range(2,7):
    pool = [tree for m in range(1,n) for tree in trees[m]]
    trees[n] = [m for k in range(1,n) for m in combinations_with_replacement(pool,k)
                if sum(map(order,m)) == n-1]
    assert len(trees[n]) == len(set(trees[n]))
assert [len(trees[n]) for n in range(1,7)] == [1,1,2,4,9,20]
passed = [sum(dot(literal_b,phi(tree))*factorial(tree) == 1 for tree in trees[n]) for n in range(1,7)]
assert passed[:5] == [1,1,2,4,9]
tall = ()
for _ in range(5):
    tall = (tall,)
assert dot(literal_b,phi(tall)) == Q(-5,24)
assert passed[5] < len(trees[6])
print("gamma",gamma,"c",tuple(map(str,c)),"b",tuple(map(str,b)))
print("A:")
for row in A:
    print(tuple(map(str,row)))
print("forward q =", tuple(map(str,q)), "; reflected scale =", lam)
print("c-interior pair",u,v,"; aggregate square",aggregate_square,
      "; q4−aggregate defect",delta)
print("aggregate weights", tuple(str(w[z]) for z in t),
      "; sqrt(−15 product b)",square_root)
print("exact all-tree counts",passed,"of",[len(trees[n]) for n in range(1,7)])
print("order-six tall",-Q(5,24),"instead of 1/720")
