import Mathlib.Tactic.Ring

/-! Arithmetic receipts for the pure support / silent third reverse stage exclusion. -/
namespace RKResearch.Certified.SDIRKEightFiveZeroPureSilentEighth

theorem second_zero_line_cross {R : Type*} [CommRing R]
    {a b rₐ rᵦ jᵦ jxₐ jxᵦ γ tap Lₐ Lᵦ k : R}
    (ha : γ*a*rₐ-jxₐ=k*Lₐ)
    (hb : tap*rₐ + γ*rᵦ=jᵦ)
    (hc : tap*a*rₐ + γ*b*rᵦ-jxᵦ=k*Lᵦ) :
    Lₐ*(a*(jᵦ-γ*rᵦ)+γ*b*rᵦ-jxᵦ)-Lᵦ*(γ*a*rₐ-jxₐ)=0 := by
  rw [←hb,ha]
  have hd : a*(tap*rₐ+γ*rᵦ-γ*rᵦ)+γ*b*rᵦ-jxᵦ=k*Lᵦ := by
    calc
      a*(tap*rₐ+γ*rᵦ-γ*rᵦ)+γ*b*rᵦ-jxᵦ = tap*a*rₐ+γ*b*rᵦ-jxᵦ := by ring
      _ = k*Lᵦ := hc
  rw [hd]
  ring

theorem seventeen_gap_nonzero {F : Type*} [CommRing F] {v : F}
    (h₇ : (7 : F) ≠ 0) (h : v^2+2*v-6=0) : v+1 ≠ 0 := by
  intro h0
  have he : (v+1)^2-(v^2+2*v-6)=(7 : F) := by ring
  rw [h0,h,sub_zero] at he
  have hf : (7 : F) = 0 := by simpa using he.symm
  exact h₇ hf

theorem singular_D_literal :
    (2 : Nat)+55124+2*35190=2*62753 := by
  decide +kernel

end RKResearch.Certified.SDIRKEightFiveZeroPureSilentEighth
