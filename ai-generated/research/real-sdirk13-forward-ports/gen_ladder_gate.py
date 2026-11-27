"""Generate the coefficient polynomials and integer Bézout certificate exactly."""
from pathlib import Path
import sympy as S
x,g=S.symbols('x g')
F=S.Poly(S.prod(x-(2*i-1)*g for i in range(1,6)),x)
scale=S.Integer(27720)
M=[S.Poly(scale*sum(F.nth(i)/S.Integer(i+j+1) for i in range(6)),g,domain=S.QQ)
   for j in range(6)]
det=lambda r:S.Poly(S.expand(S.Matrix([[M[i+j].as_expr() for j in range(3)]
                                        for i in r]).det()),g,domain=S.QQ)
a=det([0,1,2]);b=det([0,1,3]);u,v,G=a.gcdex(b)
assert G==1
f=S.lcm([c.q for w in (u,v) for c in w.all_coeffs()])
u*=f;v*=f
assert u*a+v*b==f and all(w.domain==S.QQ for w in (u,v))
def exp(w):
    assert all(c.q==1 for c in w.all_coeffs())
    return ' + '.join(f'({w.nth(i)} : K)'+(f'*g^{i}' if i else '') for i in range(w.degree()+1) if w.nth(i))
hdr="""module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace RKResearch.Certified.FiveLadderThirteen
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

private def det3 (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

"""
for j,w in enumerate(M): hdr+=f'def M{j} (g : K) : K := {exp(w)}\n'
hdr+=f"""
private def D012 (g : K) : K :=
  det3 (M0 g) (M1 g) (M2 g) (M1 g) (M2 g) (M3 g) (M2 g) (M3 g) (M4 g)
private def D013 (g : K) : K :=
  det3 (M0 g) (M1 g) (M2 g) (M1 g) (M2 g) (M3 g) (M3 g) (M4 g) (M5 g)
private def U (g : K) : K := {exp(u)}
private def V (g : K) : K := {exp(v)}

set_option maxHeartbeats 2500000 in
private theorem bezout (g : K) :
    U g * D012 g + V g * D013 g = ({f} : K) := by
  unfold U V D012 D013 det3 M0 M1 M2 M3 M4 M5
  ring

private theorem no_common_zero (g : K) (h1 : D012 g = 0) (h2 : D013 g = 0) : False := by
  have h := bezout g
  rw [h1,h2,mul_zero,mul_zero,add_zero] at h
  exact (by norm_num : ({f} : K) ≠ 0) h.symm
"""
Path('gate_head.lean').write_text(hdr)
