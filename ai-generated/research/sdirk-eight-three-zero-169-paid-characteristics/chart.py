"""Exact signed-quadratic Cramer moments and actual physical endpoint polynomial gates."""
from functools import lru_cache
from itertools import permutations
from flint import fmpq, fmpq_mpoly_ctx, fmpq_poly

C = fmpq_mpoly_ctx.get(("k", "q", "g", "y"))
k, q, g, y = C.gens()
K = C.constant
x = k*k
r = y*y+k*y+q


def mirror(p):
    return p.compose(-k, q, g, y)


def parity(p):
    return (p+mirror(p))/2, (p-mirror(p))/(2*k)


def mean(p):  # uniform measure on [-1,1], with total mass one
    return sum(K(c/fmpq(d+1))*k**a*q**b*g**j
               for (a,b,j,d),c in p.terms() if d % 2 == 0)


def det3(M):
    return sum((-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1,3))
               *M[0][p[0]]*M[1][p[1]]*M[2][p[2]] for p in permutations(range(3)))


m = [mean(r*y**i) for i in range(6)]
Hankel = [[m[i+j] for j in range(3)] for i in range(3)]
T = -105*x*q-15*x+175*q**3+255*q*q+105*q+9
assert det3(Hankel) == 4*T/23625
p0,p1,p2 = [det3([[(-m[i+3] if j == ell else Hankel[i][j]) for j in range(3)]
                  for i in range(3)])*fmpq(23625,4) for ell in range(3)]
P = T*y**3+p2*y*y+p1*y+p0  # T times the monic zero-clock polynomial
assert all(not mean(r*P*y**j) for j in range(3))
A = -63*x*x*q+21*x*x-70*x*q**3-210*x*q*q-138*x*q-30*x+245*q**5+805*q**4+986*q**3+546*q*q+129*q+9
B = -525*x*x*q+525*x*x-1750*x*q**3-5670*x*q*q-3150*x*q-630*x+3675*q**5+13825*q**4+17970*q**3+9990*q*q+2259*q+153
omega = T*m[2]+p2*m[1]+p1*m[0]+(T*m[1]+p2*m[0])*y+T*m[0]*y*y
assert mean(r*r*P.derivative("y")) == 2*A/7
assert mean(r*omega) == B/315
diag = 180*g*A-B

R = r.compose(k,q,g,2*g-1)
D = R+4*g*g
U = 2*R-2*g*(4*g-2+k)
F = (-2*D**3+U*D**2+4*U**2*D-U**3-2*R*(3*U-2*D)*D)/(2*g)
G = 4*U**3-12*U**2*D+3*U*D**2+2*D**3
z = 2*g*(D+2*U)-D
pin = T*z**3+p2*z*z*D+p1*z*D*D+p0*D**3
primitive = 2*y**3+(3*k-12*g)*y*y+(6*q-12*g*k)*y+2-3*k+6*q-12*g*q
anchor = P.resultant(primitive,"y")


def substitute_diagonal(p, num, den):
    """Clear the denominator of g=num/den without modulo or approximation."""
    n = p.degrees()[2]
    assert p.degrees()[3] == 0
    coeff = [dict() for j in range(n+1)]
    for (a,b,j,_),v in p.terms():
        coeff[j][a,b,0,0] = v
    return sum(C.from_dict(cs)*num**j*den**(n-j) for j,cs in enumerate(coeff) if cs)
