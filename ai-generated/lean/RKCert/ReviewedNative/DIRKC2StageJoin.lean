module

public import RKCert.ReviewedNative.DIRKC2FourDebut
public import RKCert.ReviewedNative.DIRKGradeSixJoin

@[expose] public section

/-! # Apply the existing stage budget to the completed C(2) surplus
The stage counts are inherited from the checked grade-six join, not a
new reverse rank calculation. C(2), unlike nonzero defects, survives the
possibly noninjective characteristic-zero coefficient specialization. -/
namespace RKResearch.Certified.Graded

open scoped Matrix
variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S]

theorem monomialStageDefect_map (φ : R →+* S) (A : Matrix ι ι R) (n : ℕ) :
    monomialStageDefect (A.map φ) n=φ ∘ monomialStageDefect A n := by
  have one : φ ∘ (1:ι → R)=(1:ι → S) := by ext i; simp
  let c := A *ᵥ (1:ι → R)
  let d := A.map φ *ᵥ (1:ι → S)
  have eq : φ ∘ c=d := funext (fun i=>by
    simpa only [c,d,Function.comp_apply,one] using φ.map_mulVec A (1:ι → R) i)
  have power (k : ℕ) : φ ∘ (c^k)=d^k := by
    ext i
    simp only [Function.comp_apply,Pi.pow_apply,map_pow]
    exact congrArg (fun z : S => z^k) (congrFun eq i)
  ext i
  change ((n+1:ℕ):S) * ((A.map φ) *ᵥ d^n) i-d i^(n+1) =
    φ (((n+1:ℕ):R) * (A *ᵥ c^n) i-c i^(n+1))
  rw [map_sub,map_mul,map_natCast,map_pow,φ.map_mulVec,power,show φ (c i)=d i from congrFun eq i]

end RKResearch.Certified.Graded

namespace RKResearch

open Certified.Graded
open scoped Matrix

/-- For p≥12, the complete native C(2) forward surplus supplies the
existing stage budget over characteristic-zero fields. -/
theorem HasOrder.dirk_C2_stage_floor_field
    {K : Type*} [Field K] [CharZero K] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hp : 12≤p) (c₂ : monomialStageDefect A 1=0) :
    p+(p-1)/2-2 ≤ s :=
  Reverse.dirk_uniform_of_grade_six ha ho hp
    (dirk_grade_six_surplus_C2 ha ho (by omega) c₂)

universe u

/-- Zero quadratic defect descends exactly; no reducedness, domain, or
torsion-free additive group hypothesis is needed on the original ring. -/
theorem HasOrder.dirk_C2_stage_floor
    {R : Type u} [CommRing R] [CharZero R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hp : 12≤p) (c₂ : monomialStageDefect A 1=0) :
    p+(p-1)/2-2 ≤ s :=
  RKCert.ReviewedNative.with_charZero_field (fun K _ _ φ =>
    (ho.map_coefficients φ).dirk_C2_stage_floor_field (ha.map φ) hp (by
      rw [monomialStageDefect_map,c₂]
      ext i; simp))

end RKResearch
