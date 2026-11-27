"""Independent exact polynomial replay; requires SymPy."""
from functools import reduce
import sympy as S

y, z, u, s, t, w, r = S.symbols("y z u s t w r")
L = [S.laguerre(j, y) for j in range(4)]

def I(f, end):
    return S.cancel(sum(a * end**j / (j + 1)
                        for (j,), a in S.Poly(f, y).terms()))

def numerator(f):
    return S.fraction(S.cancel(f))[0]

def no_projective_root(poly, x, p):
    coeff = [int(v) for v in S.Poly(poly, x).all_coeffs()]
    n = len(coeff) - 1
    assert all(sum(v * a**(n-i) * b**i for i,v in enumerate(coeff)) % p
               for a,b in [(k,1) for k in range(p)] + [(1,0)])

# Two-head folding would require this rational clock.
no_projective_root(y**3 - 9*y**2 + 18*y - 6, y, 5)

# Exceptional branch: the cubic is orthogonal to L1,L2,L3.
A = S.Matrix([[I(f*y**j,z) for j in range(3)] for f in L[1:]])
b = S.Matrix([-I(f*y**3,z) for f in L[1:]])
D = z**3 - 12*z**2 + 60*z - 120
assert S.factor(A.det() * 518400) == z**6 * D
no_projective_root(D, z, 17)
F = S.expand(y**3 + sum(y**j*c for j,c in enumerate(A.inv()*b)))
fs,ft = F.coeff(y,2),F.coeff(y,1)
G = y*y+(fs+r)*y+ft+fs*r+r*r
res = S.factor_list(S.resultant(numerator(F.subs(y,r)),
                               numerator(I(L[3]*G,z)),r))[1]
P = next(p for p,j in res if S.degree(p,z)==12)
assert [(S.degree(p,z),j) for p,j in res] == [(1,6),(3,4),(12,1)]
no_projective_root(P, z, 11)

# Generic quarter-diagonal branch. Use the monic cubics in y/4.
h = (y-1)*(y-u)
TQ = (3*u-5)*L[1]+(3*u-5)*(u-3)*L[2]+(u-2)**2*(u-3)*L[3]
def Cramer(spec, r0):
    A = S.Matrix([[I(f*(y/4)**j,4) for j in range(r0-1,-1,-1)] for f in spec])
    b = S.Matrix([-I(f*(y/4)**r0,4) for f in spec])
    d = S.expand(A.det())
    ad = A.adjugate()*b
    cl = reduce(S.gcd, [d]+list(ad))
    return list(map(S.cancel,[d/cl]+[a/cl for a in ad]))

D3,S3,T3,W3 = Cramer([L[3],L[1]+(u-3)*L[2],h*(y-2*u+1)],3)
D2,S2,T2 = Cramer([TQ,y*TQ/4],2)
E = S.expand((S2*S2-T2*D2)*D3-S3*S2*D2+T3*D2*D2)
fac = S.factor_list(E)[1]
assert [(S.degree(g,u),n) for g,n in fac] == [(1,1),(2,1),(12,1)]
assert S.expand(fac[0][0]) == u-1
no_projective_root(fac[1][0], u, 5)
no_projective_root(fac[2][0], u, 17)
print("Exact fold, exceptional, and quarter-diagonal projections checked.")
