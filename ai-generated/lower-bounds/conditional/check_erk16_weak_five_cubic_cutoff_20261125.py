from fractions import Fraction as Q
from math import comb, factorial

def ev(a, x):
    out = Q(0)
    for c in reversed(a):
        out = c + x*out
    return out

def jacobi_in_y_but_monic_in_x(n):
    m = n + 1
    # The (m+1)-st derivative of (y^2-1)^m, scaled as P_m'.
    a = [Q(0)]*(n+1)
    for k in range(m+1):
        j = 2*k-m-1
        if j >= 0:
            a[j] = Q((-1)**(m-k)*comb(m,k)*factorial(2*k),
                     factorial(j)*2**m*factorial(m))
    scale = a[-1]*2**n
    assert scale > 0
    return [c/scale for c in a]

def unit_moment_y(k):
    return Q(0) if k % 2 else Q(2, k+1)

A6 = [-5, 0, 135, 0, -495, 0, 429]
A7 = [0, -35, 0, 385, 0, -1001, 0, 715]
for A in (A6, A7):
    n = len(A)-1
    J = jacobi_in_y_but_monic_in_x(n)
    assert J == [Q(c, A[-1]*2**n) for c in A]
    for k in range(n):
        assert sum(c*(unit_moment_y(i+k)-unit_moment_y(i+k+2))
                   for i, c in enumerate(J)) == 0

for y, n6, n7 in ((Q(13,15), -12224064, -86239040),
                  (Q(7,8), 192061, -1602629)):
    assert ev(A6, y)*y.denominator**6 == n6
    assert ev(A7, y)/y*y.denominator**6 == n7
    assert n7 < 0
assert -12224064 < 0 < 192061

B, U = Q(14,15), Q(11,12)
g = lambda u: (B-Q(3,4)*u)*(B-Q(9,10)+Q(11,100)*u)-Q(3,80)*u*u
assert Q(3,5) - Q(3,4)**2 == Q(3,80)
assert -Q(3,4)*Q(11,100)-Q(3,80) == -Q(3,25)
assert g(0) == Q(7,225) > 0 and g(U) == Q(53,36000) > 0
assert Q(9,5)-Q(18,25)*Q(5,4) == Q(9,10)
assert 2*Q(18,25)-Q(31,20) == -Q(11,100)
assert 101**2+23 == 144*71
assert Q(1,3) < Q(9,25) and Q(5,21) < Q(1,4)
