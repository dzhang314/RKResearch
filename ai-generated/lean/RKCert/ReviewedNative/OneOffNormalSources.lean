module

public import RKCert.ReviewedNative.OneOffNormalHead

@[expose] public section

/-! # Four actual feature source actions after the constant-amplitude head -/
namespace RKResearch.Certified.Graded.OneOff
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

def NormalFour (a d e hd he x G H : K) : Prop :=
  ThreeFeatures a d hd x G H ∨ (x=e ∧ G=0 ∧ H=he)

abbrev normalCubSource (a d e m1 m2 H : K) :=
  (d+e)*m2-d*e*m1+(a*(a-d)*(a-e)/baseAmp a)*H

abbrev normalHSource (a d e hd he m1 m2 H : K) :=
  (hd/d)*(e*m1-m2-(a*(e-a)/baseAmp a)*H)/(e-d)+
    (he/e)*(m2-d*m1-(a*(a-d)/baseAmp a)*H)/(e-d)

/-- The cubic source identity remains valid if the off clock coincides
with a clean clock. The correcting off feature uses the defect itself. -/
theorem normal_four_cubic (ha : ∀ i j, i ≤ j → A i j = 0) {a d e hd he : K} (r : Fin s)
    (an : a≠0)
    (pre : ∀ l, l < r → NormalFour a d e hd he (nodes A l) (g A l) (h A l)) :
    M3 A r=normalCubSource a d e (M1 A r) (M2 A r) (h A r) := by
  have un : baseAmp a≠0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ an)) (by norm_num)
  let v := (nodes A)^3-(d+e) • (nodes A)^2+(d*e) • nodes A
  have eq := causal_action_eq ha r v ((a*(a-d)*(a-e)/baseAmp a) • g A) (fun l hl => by
    rcases pre l hl with (⟨x,G,H⟩|⟨x,G,H⟩|⟨x,G,H⟩)|⟨x,G,H⟩ <;>
      simp only [v,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul,x,G,
        mul_zero,div_mul_cancel₀ _ un] <;> ring)
  simp only [v,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mat_g] at eq
  unfold normalCubSource
  linear_combination eq

theorem normal_four_h (ha : ∀ i j, i ≤ j → A i j = 0) {a d e hd he : K} (r : Fin s)
    (an : a≠0) (dn : d≠0) (en : e≠0) (ed : e≠d)
    (pre : ∀ l, l < r → NormalFour a d e hd he (nodes A l) (g A l) (h A l)) :
    k A r=normalHSource a d e hd he (M1 A r) (M2 A r) (h A r) := by
  have un : baseAmp a≠0 := div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ an)) (by norm_num)
  let v := ((hd/d)/(e-d)) •
      (e • nodes A-(nodes A)^2-(a*(e-a)/baseAmp a) • g A)+
    ((he/e)/(e-d)) • ((nodes A)^2-d • nodes A-(a*(a-d)/baseAmp a) • g A)
  have con (x G H : K) (k : NormalFour a d e hd he x G H) :
      H=normalHSource a d e hd he x (x^2) G := by
    unfold normalHSource
    rcases k with (⟨x',G',hm⟩|⟨x',G',hm⟩|⟨x',G',hm⟩)|⟨x',G',hm⟩ <;>
      rw [x',G',hm] <;> simp only [mul_zero,div_mul_cancel₀ _ un] <;>
      field_simp [dn,en,sub_ne_zero.mpr ed] <;> ring
  have eq := causal_action_eq ha r (h A) v (fun l hl => by
    have h := con _ _ _ (pre l hl)
    unfold normalHSource at h
    simp only [v,Pi.add_apply,Pi.sub_apply,Pi.pow_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination h)
  simp only [v,map_add,map_sub,map_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mat_g] at eq
  unfold normalHSource
  linear_combination eq

end RKResearch.Certified.Graded.OneOff
