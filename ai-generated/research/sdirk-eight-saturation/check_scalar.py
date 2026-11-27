"""Independent rational checks for the SDIRK8 singleton-zero restriction."""
from fractions import Fraction as F
from functools import reduce
from itertools import permutations
from math import factorial as fact


def sum_pol(*ps):
    if not ps:
        return ()
    v = tuple(sum((p[j] if j < len(p) else 0) for p in ps)
              for j in range(max(map(len, ps))))
    return v[:next((j+1 for j in reversed(range(len(v))) if v[j]), 0)]


def scale(c, p):
    return sum_pol(tuple(c*x for x in p))


def mul(p, q):
    return sum_pol(*(tuple([0]*j) + scale(x, p) for j, x in enumerate(q)))


def power(p, n):
    return reduce(mul, [p]*n, (F(1),))


def value(p, x):
    return sum(c*x**k for k, c in enumerate(p))


def moment(p, k=0):
    return sum(F(c, j+k+1) for j, c in enumerate(p))


def det(A):
    v = 0
    for perm in permutations(range(len(A))):
        pr = 1
        for i, j in enumerate(perm):
            pr *= A[i][j]
        v += (-1)**sum(perm[i] > perm[j] for i in range(len(A))
                       for j in range(i+1, len(A))) * pr
    return v


X = (F(0), F(1))
L3 = (F(-1,20), F(3,5), F(-3,2), F(1))
L4 = (F(1,70), F(-2,7), F(9,7), F(-2), F(1))
assert [moment(L3, k) for k in range(3)] == [0]*3
assert [moment(L4, k) for k in range(4)] == [0]*4
B3 = (F(-500,3), F(5200,3), -4200, 2800)
B4 = (F(-1540,3), 2800, -2800)
assert sum_pol(mul(B3,L3),mul(B4,L4)) == (1,)
H = [[F(1,i+j+1) for j in range(4)] for i in range(4)]
HI = [[16,-120,240,-140],[-120,1200,-2700,1680],
      [240,-2700,6480,-4200],[-140,1680,-4200,2800]]
assert [[sum(H[i][k]*HI[k][j] for k in range(4)) for j in range(4)]
        for i in range(4)] == [[int(i == j) for j in range(4)] for i in range(4)]
# Pi(a,X) = (L4(X) - L4(a))/(X-a), collected in powers of X.
pi = tuple(tuple(L4[j+1:]) for j in range(4))
assert pi == ((F(-2,7),F(9,7),-2,1),(F(9,7),-2,1),(-2,1),(1,))
p_at_a = sum_pol(*(mul(power(X,j),p) for j,p in enumerate(pi)))
J_a = sum_pol(*(scale(F(1,j+1),mul(power(X,j+1),p)) for j,p in enumerate(pi)))
J_1 = sum_pol(*(scale(F(1,j+1),p) for j,p in enumerate(pi)))
gamma = (F(4,72),F(35,72),F(-35,72))
assert sum_pol(J_a, scale(-1,mul(gamma,p_at_a))) == mul((F(10,9), F(35,18)),L4)
assert sum_pol(J_1,scale(-2,J_a)) == scale(F(-25,6),L4)
assert sum_pol(power(sum_pol(scale(144,gamma),(-18,)),2),(-30,)) == scale(4900,L4)
assert value(L4,0) == value(L4,1) == F(1,70)
assert det([[F(fact(j),fact(j+k)) for j in range(3)] for k in range(3)]) == F(-1,72)
print("SDIRK8 singleton-zero: Hilbert, Legendre, cardinal and chronology identities verified")

L5 = sum_pol(mul((F(-1,2),1),L4),scale(F(-4,63),L3))
assert [moment(L5, k) for k in range(5)] == [0]*5
# After assuming a non-opposite pair, p=yz has p^2=3/35.
# The difference of the two squared primitive conditions is reduced modulo it.
s = sum_pol(mul(power((F(1,3),1),2),(F(6,7),-2)),
            scale(-1,power((F(6,35),F(2,7)),2)))
assert sum_pol((s[0]+F(3,35)*s[2],s[1]+F(3,35)*s[3])) == (F(464,25725),F(176,2205))
assert F(-87,385)**2-F(3,35)==F(-5136,148225)
print("SDIRK8 two-zero: third Legendre read and conditional reflection identities verified")
