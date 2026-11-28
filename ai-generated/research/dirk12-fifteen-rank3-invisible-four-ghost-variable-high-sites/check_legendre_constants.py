"""Replay the scalar Legendre constants used in the grade-six ghost feeds."""
from fractions import Fraction
from math import comb

def coefficient(n, k):
    return (-1)**(n-k)*comb(n, k)*comb(n+k, k)

def integral(n):
    # Integral from 0 to 1 of X L_n'(X) (1-X)^5.
    return sum(Fraction(k*coefficient(n, k)*(-1)**j*comb(5, j), k+j+1)
               for k in range(1, n+1) for j in range(6))

assert (integral(5), integral(6), integral(7)) == (Fraction(1, 462), 0, 0)
assert 7*coefficient(7, 7) == 24024
print('Legendre constants 1/462, 0, 0 and leading coefficient 24024: passed')
