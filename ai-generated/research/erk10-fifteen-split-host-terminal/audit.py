"""Exact head, tail-moment nullspace, and projective scalar gates."""
from itertools import product
import sympy as S

y,b,c,k,d=S.symbols("y b c k d")
C=4*b*k/(2*k-1)
N=S.factor((2*(4*b*k*k*y-4*b*k*k+2*b*k*y+2*b*k-2*k*y+y)/(2*k-1)).subs(k,c/(2*c-4*b)))
assert S.cancel(N*(y-c/2)+(2-c)*y*(y-c)+c**2*(y-1)*(y-b)/(2*b-c))==0
assert S.cancel((2*b-c).subs(c,C)+2*b/(2*k-1))==0
M=y*y*(y-c)**2
J=lambda p:S.integrate(p,(y,0,y))
I=lambda p:S.integrate(p,(y,0,1))
G0=(y-d)*S.diff(M,y)/4
assert S.expand(4*J(G0)-(y-d)*M+J(M))==0
print("actual precursor anchor factorization and blind primitive identity: exact")

m=S.Matrix([[I((1-y)*y**j*p) for j in range(4)] for p in (M,y*M,J(M))])
cols=[
 [75,-108,45,-5],
 [-525,732,-291,30],
 [1050,-1428,549,-54],
 [-630,840,-315,30],
]
coeff=[sum(q*c**(3-j) for j,q in enumerate(col)) for col in cols]
for i,q in enumerate(coeff):
    cofactor=(-1)**i*m[:,[j for j in range(4) if j!=i]].det()
    assert S.expand(80015040000*cofactor-c*c*q)==0
assert m*S.Matrix(coeff)==S.zeros(3,1) or all(z.expand()==0 for z in m*S.Matrix(coeff))
print("three exact primitive/moment forms yield the stated cubic by 3×3 minors")

def form(c,a,b):
    return sum(sum(q*c**(3-j) for j,q in enumerate(col))*a**i*b**(3-i)
               for i,col in enumerate(cols))
root_counts=[]
for c0 in range(8):
    roots=[(a,b) for a,b in product(range(8),repeat=2)
           if (a%2 or b%2) and not form(c0,a,b)%8]
    root_counts.append(len(roots))
assert root_counts==[0,0,16,0,0,0,0,0]
for poly,p in [(cols[0],2),(cols[3],17)]:
    assert all(sum(q*a**(3-j)*b**j for j,q in enumerate(poly))%p
               for a,b in product(range(p),repeat=2) if a or b)
print("projective modulo-eight root counts:",root_counts)
print("constant and leading parameter coefficients projectively rootless modulo 2 and 17")
