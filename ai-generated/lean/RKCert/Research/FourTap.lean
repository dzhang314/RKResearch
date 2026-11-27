import Lean

/-!
# The five-coordinate, four-word penultimate ERK obstruction

Coordinates here are numbered 0 to 4.  This module uses only Lean core's
commutative field API.  No positivity or characteristic-zero hypothesis is used.
`nonendpointKrylov` and `exceptionalKrylov` consume actual words in the
cyclic five-coordinate chart. `noTop` treats the noncyclic physical case.
The paper note supplies the link to weighted rooted order and the stage count.
-/
namespace RKResearch.FourTap
open Lean.Grind
variable {K : Type} [Field K]

private theorem cancel {a b c : K} (h : a ≠ 0) (e : a * b = a * c) : b = c := by
  have h' := congrArg (fun x => a⁻¹ * x) e
  simpa [← Semiring.mul_assoc, Field.inv_mul_cancel h, Semiring.one_mul] using h'

private theorem nonzero_mul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h; cases Field.of_mul_eq_zero h with
  | inl x => exact ha x
  | inr x => exact hb x

/-- Over any field, the three normalized two-clock identities and the two
literal equal-clock adjacency identities exclude a nonzero penultimate read.
The premises `adj₀,adj₁` follow from a diagonal clock on physical coordinates.
They are not inferred just from triangular shape in an arbitrary basis. -/
theorem topVisible (m T U V y₀ y₁ y₂ : K) (hT : T ≠ 0)
    (e₀ : y₀*(U*U-T*V) = U*T)
    (e₁ : y₁*(U*U-T*V) = U*T)
    (e₂ : y₂*(U*U-T*V) = U*T)
    (adj₀ : y₀ = y₁ → (m+4)*T = y₀*U)
    (adj₁ : y₁ = y₂ → (m+3)*T = y₁*U) : U = 0 := by
  by_cases hu : U = 0
  · exact hu
  have hr : U*U-T*V ≠ 0 := by
    intro hz
    have h := nonzero_mul hu hT
    apply h
    rw [hz, Semiring.mul_zero] at e₀
    exact e₀.symm
  have h01 : y₀ = y₁ := by
    apply cancel hr
    rw [CommSemiring.mul_comm _ y₀, CommSemiring.mul_comm _ y₁, e₀, e₁]
  have h12 : y₁ = y₂ := by
    apply cancel hr
    rw [CommSemiring.mul_comm _ y₁, CommSemiring.mul_comm _ y₂, e₁, e₂]
  have a := adj₀ h01
  have b := adj₁ h12
  exfalso
  apply hT
  grind

/-- Tail shape for the no-top argument. `u` is A²v on sites (2,3,4);
`r` is βA² on sites (0,1,2). `a10,a20,…` are actual strictly lower entries
with row, column indices denoted by their names. For vectors, `v0,v1` and
weights `b3,b4` are the only other entries required. The two read definitions and six paid-word
identities are listed explicitly, and no matrix/existence assertion is hidden
in the hypotheses. -/
theorem noTop (m y0 y1 y2 y3 y4 u2 u3 u4 r0 r1 r2
    v0 v1 v2 b2 b3 b4 a10 a20 a21 a32 a42 a43 mu3 : K)
    (paid₁ : m+1 ≠ 0) (paid₃ : m+3 ≠ 0)
    (middle : r2*u2 = 0)
    (readF : b3*(a32*u2)+b4*(a42*u2+a43*u3) = mu3)
    (readR : r1*(a10*v0)+r2*(a20*v0+a21*v1) = mu3)
    (ya3 : b3*y3*(a32*u2)+b4*y4*(a42*u2+a43*u3) = 0)
    (aya2 : b3*a32*(y2*u2)+b4*(a42*(y2*u2)+a43*(y3*u3)) = 0)
    (yu : b2*y2*u2+b3*y3*u3+b4*y4*u4 = (m+1)*mu3)
    (a3y : r1*(a10*(y0*v0))+r2*(a20*(y0*v0)+a21*(y1*v1)) = 0)
    (a2ya : r1*y1*(a10*v0)+r2*y2*(a20*v0+a21*v1) = 0)
    (ry : r0*y0*v0+r1*y1*v1+r2*y2*v2 = (m+3)*mu3) :
    mu3 = 0 := by
  by_cases h : mu3 = 0
  · exact h
  exfalso
  rcases Field.of_mul_eq_zero middle with hr | hu
  · have e0 : mu3*y0 = 0 := by grind
    have e1 : mu3*y1 = 0 := by grind
    have z0 := (Field.of_mul_eq_zero e0).resolve_left h
    have z1 := (Field.of_mul_eq_zero e1).resolve_left h
    apply nonzero_mul paid₃ h
    grind
  · have e3 : mu3*y3 = 0 := by grind
    have e4 : mu3*y4 = 0 := by grind
    have z3 := (Field.of_mul_eq_zero e3).resolve_left h
    have z4 := (Field.of_mul_eq_zero e4).resolve_left h
    apply nonzero_mul paid₁ h
    grind

/-! ## Actual paid words in the terminal Krylov chart

`Shift` is the action of A on (v,Av,...,A⁴v) when the last tap is
nonzero.  `Clock` holds all fifteen entries of Y in this basis; the
nonadjacent entries are not discarded or assumed zero.
-/
structure V (K : Type) where
  x0 : K
  x1 : K
  x2 : K
  x3 : K
  x4 : K

structure Clock (K : Type) where
  y0 : K
  z0 : K
  y1 : K
  w0 : K
  z1 : K
  y2 : K
  h0 : K
  w1 : K
  z2 : K
  y3 : K
  j0 : K
  h1 : K
  w2 : K
  z3 : K
  y4 : K

def shift (v : V K) : V K := ⟨0,v.x0,v.x1,v.x2,v.x3⟩
def clock (c : Clock K) (v : V K) : V K :=
  ⟨c.y0*v.x0, c.z0*v.x0+c.y1*v.x1,
   c.w0*v.x0+c.z1*v.x1+c.y2*v.x2,
   c.h0*v.x0+c.w1*v.x1+c.z2*v.x2+c.y3*v.x3,
   c.j0*v.x0+c.h1*v.x1+c.w2*v.x2+c.z3*v.x3+c.y4*v.x4⟩
def dot (b v : V K) : K := b.x0*v.x0+b.x1*v.x1+b.x2*v.x2+b.x3*v.x3+b.x4*v.x4

inductive Op where | A | Y
open Op

def word (c : Clock K) : List Op → V K
  | [] => ⟨1,0,0,0,0⟩
  | A :: l => shift (word c l)
  | Y :: l => clock c (word c l)

def factor (m : K) : List Op → K
  | [] => 1
  | A :: l => factor (m+1) l
  | Y :: l => (m+1)*factor (m+1) l

def moment (b : V K) : Nat → K
  | 0 => b.x0 | 1 => b.x1 | 2 => b.x2 | 3 => b.x3 | _ => b.x4

def Paid4 (m : K) (b : V K) (c : Clock K) : Prop :=
  ∀ l : List Op, l.length ≤ 4 →
    dot b (word c l) = factor m l * moment b l.length

/-- Diagonality in *physical* coordinates implies this condition on every
adjacent two-coordinate chronological quotient in the Krylov basis. -/
def adjacentDiagonal (c : Clock K) : Prop :=
  (c.y0 = c.y1 → c.z0 = 0) ∧ (c.y1 = c.y2 → c.z1 = 0) ∧
  (c.y2 = c.y3 → c.z2 = 0) ∧ (c.y3 = c.y4 → c.z3 = 0)

/-- The two-clock identity, without division by a pivot or by a clock. -/
theorem dividedWord (y z w Yt T U V k p : K)
    (high : y*U+z*T = (k+1)*T)
    (low  : y*V+z*U+w*T = k*U)
    (mixed : y*(p*U)+z*(p*T)+w*(Yt*T) = p*((k+1)*T)) :
    Yt * (y*(U*U-T*V) - U*T) = 0 := by
  have a := congrArg (fun x => p*x) high
  have b := congrArg (fun x => U*x) high
  have c := congrArg (fun x => T*x) low
  grind

private theorem normalized_of_outer {y z w Yt T U V k p : K} (hy : Yt ≠ 0)
    (high : y*U+z*T = (k+1)*T)
    (low : y*V+z*U+w*T = k*U)
    (mixed : y*(p*U)+z*(p*T)+w*(Yt*T) = p*((k+1)*T)) :
    y*(U*U-T*V) = U*T := by
  have e := dividedWord y z w Yt T U V k p high low mixed
  have := (Field.of_mul_eq_zero e).resolve_left hy
  grind

set_option maxHeartbeats 600000 in
/-- For arbitrary coefficients in the terminal Krylov chart, diagonalizable
adjacent clocks and the literal paid words of length at most four force the
penultimate read to vanish when the final clock differs from the endpoint. -/
theorem nonendpointKrylov (m : K) (b : V K) (c : Clock K)
    (pay : Paid4 m b c) (adj : adjacentDiagonal c)
    (hT : b.x4 ≠ 0) (hy : c.y4 ≠ 0) : b.x3 = 0 := by
  have eAAAY := pay [A,A,A,Y] (by decide)
  have eAAYA := pay [A,A,Y,A] (by decide)
  have eAYAA := pay [A,Y,A,A] (by decide)
  have eAAY := pay [A,A,Y] (by decide)
  have eAYA := pay [A,Y,A] (by decide)
  have eYAA := pay [Y,A,A] (by decide)
  have eYAAA := pay [Y,A,A,A] (by decide)
  have eYAAY := pay [Y,A,A,Y] (by decide)
  have eYAYA := pay [Y,A,Y,A] (by decide)
  have eYYAA := pay [Y,Y,A,A] (by decide)
  simp only [word, shift, clock, dot, factor, List.length_cons, List.length_nil,
    moment, Semiring.mul_zero, Semiring.mul_one,
    Semiring.add_zero] at eAAAY eAAYA eAYAA eAAY eAYA eYAA eYAAA eYAAY eYAYA eYYAA
  have h0 : c.y0*b.x3+c.z0*b.x4 = ((m+3)+1)*b.x4 := by grind
  have h1 : c.y1*b.x3+c.z1*b.x4 = ((m+2)+1)*b.x4 := by grind
  have h2 : c.y2*b.x3+c.z2*b.x4 = ((m+1)+1)*b.x4 := by grind
  have eq0 : c.y0*(b.x3*b.x3-b.x4*b.x2) = b.x3*b.x4 := by
    apply normalized_of_outer (z:=c.z0) (w:=c.w0) (k:=m+3) (p:=m+1) hy h0
    · grind
    · grind
  have eq1 : c.y1*(b.x3*b.x3-b.x4*b.x2) = b.x3*b.x4 := by
    apply normalized_of_outer (z:=c.z1) (w:=c.w1) (k:=m+2) (p:=m+1) hy h1
    · grind
    · grind
  have eq2 : c.y2*(b.x3*b.x3-b.x4*b.x2) = b.x3*b.x4 := by
    apply normalized_of_outer (z:=c.z2) (w:=c.w2) (k:=m+1) (p:=m+1) hy h2
    · grind
    · grind
  apply topVisible m b.x4 b.x3 b.x2 c.y0 c.y1 c.y2 hT eq0 eq1 eq2
  · intro e
    have := adj.1 e
    grind
  · intro e
    have := adj.2.1 e
    grind

set_option maxHeartbeats 600000 in
/-- The only possible top-visible exception has a final endpoint, an initial
double clock, and an isolated clock component modulo the last coordinate.
The penultimate moment determines the common initial clock. -/
theorem exceptionalKrylov (m : K) (b : V K) (c : Clock K)
    (pay : Paid4 m b c) (adj : adjacentDiagonal c)
    (hT : b.x4 ≠ 0) (hU : b.x3 ≠ 0) (p1 : m+1 ≠ 0) (p4 : m+4 ≠ 0) :
    c.y4 = 0 ∧ c.y3 ≠ 0 ∧ c.y0 = c.y1 ∧ c.y0 ≠ 0 ∧ c.y1 ≠ c.y2 ∧
    c.y0*b.x3 = (m+4)*b.x4 ∧ c.y0*b.x2 = (m+3)*b.x3 ∧
    c.y0*b.x1 = (m+2)*b.x2 ∧ c.z0 = 0 ∧ c.w0 = 0 ∧ c.h0 = 0 := by
  have end0 : c.y4 = 0 := by
    by_cases h : c.y4 = 0
    · exact h
    · exact False.elim (hU (nonendpointKrylov m b c pay adj hT h))
  have eAAAY := pay [A,A,A,Y] (by decide)
  have eAAYA := pay [A,A,Y,A] (by decide)
  have eAYAA := pay [A,Y,A,A] (by decide)
  have eYAAA := pay [Y,A,A,A] (by decide)
  have eAAY := pay [A,A,Y] (by decide)
  have eAYA := pay [A,Y,A] (by decide)
  have eYAA := pay [Y,A,A] (by decide)
  have eAY := pay [A,Y] (by decide)
  have eAYAY := pay [A,Y,A,Y] (by decide)
  have eAYYA := pay [A,Y,Y,A] (by decide)
  have eAYY := pay [A,Y,Y] (by decide)
  simp only [word, shift, clock, dot, factor, List.length_cons, List.length_nil,
    moment, Semiring.mul_zero, Semiring.mul_one, Semiring.add_zero] at eAAAY eAAYA eAYAA eYAAA eAAY eAYA eYAA eAY eAYAY eAYYA eAYY
  have ty : c.y3 ≠ 0 := by
    intro h
    have zn := adj.2.2.2 (h.trans end0.symm)
    apply nonzero_mul p1 hT
    grind
  have h0 : c.y0*b.x3+c.z0*b.x4 = ((m+3)+1)*b.x4 := by grind
  have h1 : c.y1*b.x3+c.z1*b.x4 = ((m+2)+1)*b.x4 := by grind
  have eq0 : c.y0*(b.x3*b.x3-b.x4*b.x2) = b.x3*b.x4 := by
    apply normalized_of_outer (z:=c.z0) (w:=c.w0) (k:=m+3) (p:=m+2) ty h0
    · grind
    · grind
  have eq1 : c.y1*(b.x3*b.x3-b.x4*b.x2) = b.x3*b.x4 := by
    apply normalized_of_outer (z:=c.z1) (w:=c.w1) (k:=m+2) (p:=m+2) ty h1
    · grind
    · grind
  have hr : b.x3*b.x3-b.x4*b.x2 ≠ 0 := by
    intro hz
    apply nonzero_mul hU hT
    rw [hz, Semiring.mul_zero] at eq0
    exact eq0.symm
  have h01 : c.y0 = c.y1 := by
    apply cancel hr
    rw [CommSemiring.mul_comm _ c.y0, CommSemiring.mul_comm _ c.y1, eq0, eq1]
  have z0 := adj.1 h01
  have y0 : c.y0 ≠ 0 := by
    intro h
    apply nonzero_mul p4 hT
    grind
  have h12 : c.y1 ≠ c.y2 := by
    intro h
    have z1 := adj.2.1 h
    apply hT
    grind
  have w0 : c.w0 = 0 := by
    have cf : (c.y3*b.x4)*c.w0 = 0 := by grind
    exact (Field.of_mul_eq_zero cf).resolve_left (nonzero_mul ty hT)
  have hn : c.h0 = 0 := by
    have cf : (c.y3*b.x4)*c.h0 = 0 := by grind
    exact (Field.of_mul_eq_zero cf).resolve_left (nonzero_mul ty hT)
  exact ⟨end0,ty,h01,y0,h12,by grind,by grind,by grind,z0,w0,hn⟩

/-! ## Rational sharpness example (not an order-nine method)

A genuine five-site strictly lower suffix and diagonal physical clock at shift
two satisfy *every* word test of budget four on the first coordinate, yet the
penultimate and top reads are both one. Earlier origin-column entries can pay
the specified row sums, as explained in the note; no rooted order is claimed.
-/
def sharpA (v : V Rat) : V Rat :=
  ⟨0, v.x0, v.x0/5+v.x1, 3*v.x0/4+14*v.x1/5+v.x2,
   7*v.x0/18+137*v.x1/60-7*v.x2/2+v.x3⟩
def sharpY (v : V Rat) : V Rat := ⟨6*v.x0,6*v.x1,v.x2,2*v.x3,0⟩
def sharpB : V Rat := ⟨5/18,29/120,-6,3/2,1⟩
def sharpWord : List Op → V Rat
  | [] => ⟨1,0,0,0,0⟩
  | A :: l => sharpA (sharpWord l)
  | Y :: l => sharpY (sharpWord l)
def sharpMoments : V Rat := ⟨5/18,5/9,5/6,1,1⟩

theorem sharp_four_words (l : List Op) (h : l.length ≤ 4) :
    dot sharpB (sharpWord l) = factor (2 : Rat) l * moment sharpMoments l.length := by
  match l with
  | [] => decide +kernel
  | [a] => cases a <;> decide +kernel
  | [a,b] => cases a <;> cases b <;> decide +kernel
  | [a,b,c] => cases a <;> cases b <;> cases c <;> decide +kernel
  | [a,b,c,d] => cases a <;> cases b <;> cases c <;> cases d <;> decide +kernel
  | _::_::_::_::_::xs => simp only [List.length_cons] at h; omega

theorem sharp_positive_taps :
    dot sharpB (sharpWord [A,A,A]) = 1 ∧ dot sharpB (sharpWord [A,A,A,A]) = 1 := by
  decide +kernel

end RKResearch.FourTap
#print axioms RKResearch.FourTap.noTop
#print axioms RKResearch.FourTap.nonendpointKrylov
#print axioms RKResearch.FourTap.exceptionalKrylov
#print axioms RKResearch.FourTap.sharp_four_words
#print axioms RKResearch.FourTap.sharp_positive_taps
