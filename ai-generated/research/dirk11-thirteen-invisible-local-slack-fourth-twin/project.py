#!/usr/bin/env python3
"""Exact Q certificates for the after-third slack whose ordinary twin is fourth."""
from pathlib import Path
from sys import argv
import sympy as s

X, z, a, B, S = s.symbols("X z a B S")

def I(q):
    p = s.Poly(q, X)
    return s.Add(*(c*X**(i+1)/s.Integer(i+1) for (i,), c in p.terms()))

def coeffs(p):
    return list(reversed(p.all_coeffs()))

# Scale Y by the live shared clock; the double primitive at 1 solves r linearly.
m = X**2 - (s.Rational(3,5) + 2*S)*X + S
P = X*m
F = s.cancel(I(P)/X)
T = s.cancel(I(I(P))/(X*(X-1)))
assert s.denom(T) in s.QQ
fm = s.Poly(s.rem(F,m,X), X)
tm = s.Poly(s.rem(T,m,X), X)
assert s.expand(fm.nth(1)*tm.nth(0)-fm.nth(0)*tm.nth(1)) == s.expand(S**2*(5*S-1)/200)
assert s.expand(300*fm.as_expr()-((-100*S**2+15*S-9)*X+50*S**2+15*S)) == 0
assert s.expand(1500*tm.as_expr()-((-200*S**2-45*S+27)*X+100*S**2-45*S)) == 0
print("exact normalized 2×2 remainder determinant = S²(5S−1)/200")

# Back in literal Y, the ordinary nonendpoint hull times (1/4-a) is
# (Y-z)(Y-B) (I(Y*m)/Y - a(Y-z)*m), m=Y²-zY+z²/5.
m = X*X-z*X+z**2/5
F = s.cancel(I(X*m)/X)
test = X*(1-X)*(X-z)*(X-B)*(F-a*(X-z)*m)
rows = []
for k in range(4):
    moment = s.Poly(I(X**k * test).subs(X,1), a, B)
    row = [moment.coeff_monomial(v) for v in [1,a,B,a*B]]
    assert s.expand(moment.as_expr()-sum(c*v for c,v in zip(row,[1,a,B,a*B]))) == 0
    rows.append(row)
M = s.Matrix(rows)
D = s.Poly(13860*z**8-60984*z**7+113736*z**6-117054*z**5
           +72486*z**4-27594*z**3+6310*z**2-800*z+45, z, domain=s.QQ)
assert s.expand(M.det(method="domain-ge") - z**4*D.as_expr()/1330810145280000000) == 0
C = [(-1)**j*s.Poly(M[:3,[i for i in range(4) if i != j]].det(method="domain-ge"),
                    z, domain=s.QQ).rem(D) for j in range(4)]
C0 = C[0]
Q = (C[0]*C[3]-C[1]*C[2]).rem(D)
for v in [C0,Q]:
    assert s.gcd(D,v).is_one
    A,B_,g = s.gcdex(D,v)
    assert g.is_one and A*D+B_*v == g
print("exact degree-8 determinant and both Q Bezout identities verified")

# Optional independent portable kernel receipt of the two finite residue gcds.
# Each numerator and the determinant above is specialized once to F_101.
p=101
Df=s.Poly(D.as_expr(),z,modulus=p)
assert Df.degree() == D.degree()
def modpol(r):
    return s.Poly(sum(int(c.p)*pow(int(c.q),-1,p)*z**i for (i,),c in r.terms()), z, modulus=p)
Cs=[modpol(r) for r in C]
H=(Cs[0]*Cs[3]-Cs[1]*Cs[2]).rem(Df)
vals=[Cs[0],H]
tests=[s.gcdex(Df,r) for r in vals]
assert all(g.is_one and a*Df+b*r==g for (a,b,g),r in zip(tests,vals))
print("independent residue certificates at 101, retaining degree eight")

def lean(p_):
    return "["+", ".join(str(int(c)%p) for c in coeffs(p_))+"]"

if len(argv)>1:
    assert len(argv)==2
    def rowtests(i):
        av,bv,_=tests[i]
        return f"  ok {lean(av)} ordinary {lean(bv)} {lean(vals[i])} 16 = true := by decide"
    Path(argv[1]).write_text("""import Lean

namespace RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable

-- Coefficients are ascending elements of the residue ring, encoded as Nat.
def atC (p : List Nat) (i : Nat) : Nat := p[i]?.getD 0

def mulC (p q : List Nat) (i : Nat) : Nat :=
  ((List.range (i+1)).map (fun j => atC p j * atC q (i-j))).sum

def ok (a b c d : List Nat) (cap : Nat) : Bool :=
  (List.range (cap+1)).all (fun i =>
    (mulC a b i + mulC c d i) % 101 == (if i == 0 then 1 else 0))

def ordinary : List Nat := """+lean(Df)+"""

-- The two Q gcds in project.py are the primary characteristic-zero replay.
-- These independent exact coefficient receipts check both bounded residue
-- products, with cap larger than either possible product degree.
theorem cofactor_has_residue_inverse :
"""+rowtests(0)+"""

theorem product_gate_has_residue_inverse :
"""+rowtests(1)+"""

end RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable

open RKCert.ReviewedNative.DIRKOrderElevenInvisibleLocalSlackFourthTwinPortable
#print axioms cofactor_has_residue_inverse
#print axioms product_gate_has_residue_inverse
""")
