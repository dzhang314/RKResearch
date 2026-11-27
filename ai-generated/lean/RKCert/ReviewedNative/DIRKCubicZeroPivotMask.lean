module

public import Init.Grind

@[expose] public section

/-! # Two-clock obstruction strictly after an explicit cubic-profile pivot

The signed moments are those of a monic quadratic mask. The equations below
are the exact cleared mixed primitive tests of a scalar profile
`a*x + b*x² + c*x³`. No inequality, positivity or field ordering is used.
-/
namespace RKResearch.Certified.Graded.CubicZeroPivotMask
open Lean.Grind

variable {K : Type} [CommRing K]

/-- The moments of `x^t*(x² + l*x + h)` for any scalar read `mu`. -/
def maskMoment (mu : Nat → K) (h l : K) (t : Nat) : K :=
  h * mu t + l * mu (t+1) + mu (t+2)

/-- For fixed total `t=j+k`, the first three genuine primitive probes
`x^k J(x^j P)`, with `P = a*x + b*x² + c*x³`, after clearing denominators.
Not all three probes are paid at totals zero and one. -/
structure Tests (a b c : K) (M : Nat → K) : Prop where
  j0 : ∀ t, t ≤ 3 →
    6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(c*M (t+4)) = 0
  j1 : ∀ t, 1 ≤ t → t ≤ 3 →
    20*(a*M (t+2)) + 15*(b*M (t+3)) + 12*(c*M (t+4)) = 0
  j2 : ∀ t, 2 ≤ t → t ≤ 3 →
    15*(a*M (t+2)) + 12*(b*M (t+3)) + 10*(c*M (t+4)) = 0

/-- This integer matrix has determinant ONE; no characteristic gate is
needed to invert the cleared primitive coefficient mixing. -/
theorem separate (a b c : K) (M : Nat → K) (h : Tests a b c M) {t : Nat}
    (lo : 2 ≤ t) (hi : t ≤ 3) :
    a*M (t+2) = 0 ∧ b*M (t+3) = 0 ∧ c*M (t+4) = 0 := by
  let x := a*M (t+2)
  let y := b*M (t+3)
  let z := c*M (t+4)
  let r0 := 6*x + 4*y + 3*z
  let r1 := 20*x + 15*y + 12*z
  let r2 := 15*x + 12*y + 10*z
  have h0 : r0 = 0 := h.j0 t hi
  have h1 : r1 = 0 := h.j1 t (by omega) hi
  have h2 : r2 = 0 := h.j2 t lo hi
  change x=0 ∧ y=0 ∧ z=0
  have hx : x = 6*r0-4*r1+3*r2 := by dsimp only [r0,r1,r2]; grind only
  have hy : y = -20*r0+15*r1-12*r2 := by dsimp only [r0,r1,r2]; grind only
  have hz : z = 15*r0-12*r1+10*r2 := by dsimp only [r0,r1,r2]; grind only
  rw [h0,h1,h2] at hx hy hz
  grind

/-- Three consecutive mask moments cannot vanish for any of the four
shifts needed by the pivot test. Last rows of four integral inverse
Cauchy matrices are used as explicit certificates. -/
theorem no_three (mu : Nat → K) (h l : K) (nz : (1 : K) ≠ 0)
    (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1)) * mu t = 1) (e : Nat)
    (bounds : 2 ≤ e ∧ e ≤ 5) :
    ¬(maskMoment mu h l e = 0 ∧ maskMoment mu h l (e+1) = 0 ∧ maskMoment mu h l (e+2) = 0) := by
  have p2 : (3:K)*mu 2 = 1 := pay 2 (by decide)
  have p3 : (4:K)*mu 3 = 1 := pay 3 (by decide)
  have p4 : (5:K)*mu 4 = 1 := pay 4 (by decide)
  have p5 : (6:K)*mu 5 = 1 := pay 5 (by decide)
  have p6 : (7:K)*mu 6 = 1 := pay 6 (by decide)
  have p7 : (8:K)*mu 7 = 1 := pay 7 (by decide)
  have p8 : (9:K)*mu 8 = 1 := pay 8 (by decide)
  have p9 : (10:K)*mu 9 = 1 := pay 9 (by decide)
  let M := maskMoment mu h l
  have dinv : (2520:K)*(mu 4*mu 6*mu 7*mu 8) =
      (5*mu 4)*(7*mu 6)*(8*mu 7)*(9*mu 8) := by grind only
  rw [p4,p6,p7,p8] at dinv
  have pd : (2520:K) ≠ 0 := by
    intro h
    rw [h] at dinv
    grind
  have d2 : 1587600*M 2 - 5292000*M 3 + 3969000*M 4 = 2520 := by
    calc
      _ = h*(529200*(3*mu 2) - 1323000*(4*mu 3) + 793800*(5*mu 4))
        + l*(396900*(4*mu 3) - 1058400*(5*mu 4) + 661500*(6*mu 5))
        + (317520*(5*mu 4) - 882000*(6*mu 5) + 567000*(7*mu 6)) := by dsimp only [M, maskMoment]; grind only
      _ = 2520 := by rw [p2,p3,p4,p5,p6]; grind only
  have d3 : 4233600*M 3 - 12700800*M 4 + 8890560*M 5 = 2520 := by
    calc
      _ = h*(1058400*(4*mu 3) - 2540160*(5*mu 4) + 1481760*(6*mu 5))
        + l*(846720*(5*mu 4) - 2116800*(6*mu 5) + 1270080*(7*mu 6))
        + (705600*(6*mu 5) - 1814400*(7*mu 6) + 1111320*(8*mu 7)) := by dsimp only [M, maskMoment]; grind only
      _ = 2520 := by rw [p3,p4,p5,p6,p7]; grind only
  have d4 : 9525600*M 4 - 26671680*M 5 + 17781120*M 6 = 2520 := by
    calc
      _ = h*(1905120*(5*mu 4) - 4445280*(6*mu 5) + 2540160*(7*mu 6))
        + l*(1587600*(6*mu 5) - 3810240*(7*mu 6) + 2222640*(8*mu 7))
        + (1360800*(7*mu 6) - 3333960*(8*mu 7) + 1975680*(9*mu 8)) := by dsimp only [M, maskMoment]; grind only
      _ = 2520 := by rw [p4,p5,p6,p7,p8]; grind only
  have d5 : 19051200*M 5 - 50803200*M 6 + 32659200*M 7 = 2520 := by
    calc
      _ = h*(3175200*(6*mu 5) - 7257600*(7*mu 6) + 4082400*(8*mu 7))
        + l*(2721600*(7*mu 6) - 6350400*(8*mu 7) + 3628800*(9*mu 8))
        + (2381400*(8*mu 7) - 5644800*(9*mu 8) + 3265920*(10*mu 9)) := by dsimp only [M, maskMoment]; grind only
      _ = 2520 := by rw [p5,p6,p7,p8,p9]; grind only
  change ¬(M e = 0 ∧ M (e+1) = 0 ∧ M (e+2) = 0)
  intro ⟨h0,h1,h2⟩
  have cases : e=2 ∨ e=3 ∨ e=4 ∨ e=5 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> grind

end RKResearch.Certified.Graded.CubicZeroPivotMask

namespace RKResearch.Certified.Graded.CubicZeroPivotMask
open Lean.Grind
variable {K : Type} [Field K]

private theorem cancel {x y : K} (hx : x ≠ 0) (h : x*y=0) : y=0 :=
  (Field.of_mul_eq_zero h).resolve_left hx

/-- No nonzero scalar cubic with zero constant can pass these genuine
order-ten mixed primitive tests against a monic quadratic clock mask.
In a physical causal array this rules out at most two individually
active clock labels strictly after the zero-diagonal debut of a seed. -/
theorem no_two_clock_mask (mu : Nat → K)
    (pay : ∀ t, t < 10 → (OfNat.ofNat (α := K) (t+1)) * mu t = 1)
    (a b c h l : K) (live : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ¬Tests a b c (maskMoment mu h l) := by
  let M := maskMoment mu h l
  intro hh
  have bad (e : Nat) (he : 2 ≤ e ∧ e ≤ 5) :
      ¬(M e=0 ∧ M (e+1)=0 ∧ M (e+2)=0) :=
    no_three mu h l (Ne.symm Field.zero_ne_one) pay e he
  have h3 : (3:K) ≠ 0 := by
    have hp : (3:K)*mu 2=1 := pay 2 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have h4 : (4:K) ≠ 0 := by
    have hp : (4:K)*mu 3=1 := pay 3 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have h6 : (6:K) ≠ 0 := by
    have hp : (6:K)*mu 5=1 := pay 5 (by decide)
    intro hz; rw [hz] at hp; have hz' := Field.zero_ne_one (α := K); grind
  have at2 : a*M 4=0 ∧ b*M 5=0 ∧ c*M 6=0 :=
    separate a b c M hh (t := 2) (by decide) (by decide)
  have at3 : a*M 5=0 ∧ b*M 6=0 ∧ c*M 7=0 :=
    separate a b c M hh (t := 3) (by decide) (by decide)
  by_cases ha : a=0
  · by_cases hb : b=0
    · have cn : c ≠ 0 := (live.resolve_left (not_not_intro ha)).resolve_left (not_not_intro hb)
      have kill (t : Nat) (ht : t ≤ 3) : M (t+4)=0 := by
        have e := hh.j0 t ht
        change 6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(c*M (t+4))=0 at e
        rw [ha,hb] at e
        apply cancel cn; apply cancel h3; grind
      exact bad 4 (by decide) ⟨kill 0 (by decide),kill 1 (by decide),kill 2 (by decide)⟩
    · by_cases hc : c=0
      · have kill (t : Nat) (ht : t ≤ 3) : M (t+3)=0 := by
          have e := hh.j0 t ht
          change 6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(c*M (t+4))=0 at e
          rw [ha,hc] at e
          apply cancel hb; apply cancel h4; grind
        exact bad 3 (by decide) ⟨kill 0 (by decide),kill 1 (by decide),kill 2 (by decide)⟩
      · exact bad 5 (by decide) ⟨cancel hb at2.2.1,cancel hb at3.2.1,cancel hc at3.2.2⟩
  · by_cases hb : b=0
    · by_cases hc : c=0
      · have kill (t : Nat) (ht : t ≤ 3) : M (t+2)=0 := by
          have e := hh.j0 t ht
          change 6*(a*M (t+2)) + 4*(b*M (t+3)) + 3*(c*M (t+4))=0 at e
          rw [hb,hc] at e
          apply cancel ha; apply cancel h6; grind
        exact bad 2 (by decide) ⟨kill 0 (by decide),kill 1 (by decide),kill 2 (by decide)⟩
      · exact bad 4 (by decide) ⟨cancel ha at2.1,cancel ha at3.1,cancel hc at2.2.2⟩
    · exact bad 4 (by decide) ⟨cancel ha at2.1,cancel ha at3.1,cancel hb at3.2.1⟩

end RKResearch.Certified.Graded.CubicZeroPivotMask
