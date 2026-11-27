module

public import RKCert.ReviewedNative.ERK9FifteenLocalRing
public import RKCert.ReviewedNative.ERKIdempotentScalarCut
public import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

@[expose] public section

/-! The two literal tableaux can be joined without any localization or
field hypothesis when their inverse scales are supported on complementary
coefficient idempotents. -/

namespace RKResearch.Certified.ERK9FifteenLocalRing

open RKResearch FiniteRootedTree ERKIdempotentScalarCut
open scoped Matrix

variable {R : Type*} [CommRing R]

private theorem projection_complement {e : R} (he : e*e=e) :
    (1-e)*(1-e)=1-e := by
  calc
    _ = 1-2*e+e*e := by ring
    _ = _ := by rw [he]; ring

private theorem ortho {e : R} (he : e*e=e) : e*(1-e)=0 := by
  rw [mul_sub,mul_one,he,sub_self]

private theorem cut_sum {e : R} (he : e*e=e) {U V : Matrix (Fin 15) (Fin 15) R}
    {u v : Fin 15→R} (hV : e•V=0) (hv : e•v=0) (hu : e•u=u)
    (t : FiniteRootedTree) : e*cond (U+V) (u+v) t=cond U u t := by
  have hA : e•(U+V)=e•U := by rw [smul_add,hV,add_zero]
  have hb : e•(u+v)=e•u := by rw [smul_add,hv,add_zero]
  exact (cut_condition he hA hb t).trans (cut_condition_self hu t)

private theorem cutPow {e : R} (he : e*e=e) (t : FiniteRootedTree) :
    e^(t.order:ℕ)=e :=
  (show IsIdempotentElem e from he).pow_eq (Nat.ne_of_gt t.order.pos)

private theorem unit_five (h9 : IsUnit (Nat.factorial 9:R)) : IsUnit (5:R) := by
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast (α:=R)
    (show (5:ℕ)∣Nat.factorial 9 by decide)) h9

theorem exists_exact_of_projected_scales [Nontrivial R] (h9 : IsUnit (Nat.factorial 9:R))
    {e d₁ d₂ : R} (he : e*e=e) (hd₁ : (D₁:R)*d₁=e) (hd₂ : (D₂:R)*d₂=1-e)
    (hs₁ : e*d₁=d₁) (hs₂ : (1-e)*d₂=d₂) :
    ∃ (A : Matrix (Fin 15) (Fin 15) R) (b : Fin 15→R),
      ERK A ∧ HasOrder 9 A b ∧ ¬ HasOrder 10 A b := by
  let A₁ := ERK9RationalFifteen.A d₁
  let A₂ := ERK9RationalFifteenSecond.A d₂
  let b₁ := ERK9RationalFifteen.b d₁
  let b₂ := ERK9RationalFifteenSecond.b d₂
  have he' := projection_complement he
  have hz₁ : (1-e)*d₁=0 := by rw [sub_mul,one_mul,hs₁,sub_self]
  have hz₂ : e*d₂=0 := by
    calc
      e*d₂ = e*((1-e)*d₂) := by rw [hs₂]
      _ = 0 := by rw [←mul_assoc,ortho he,zero_mul]
  have cu₁ : e•b₁=b₁ := by simp only [b₁,ERK9RationalFifteen.b,smul_smul,hs₁]
  have cv₂ : (1-e)•b₂=b₂ := by
    simp only [b₂,ERK9RationalFifteenSecond.b,smul_smul,hs₂]
  have hA₂ : e•A₂=0 := by
    simp only [A₂,ERK9RationalFifteenSecond.A,smul_smul,hz₂,zero_smul]
  have hA₁ : (1-e)•A₁=0 := by
    simp only [A₁,ERK9RationalFifteen.A,smul_smul,hz₁,zero_smul]
  have hb₂ : e•b₂=0 := by
    simp only [b₂,ERK9RationalFifteenSecond.b,smul_smul,hz₂,zero_smul]
  have hb₁ : (1-e)•b₁=0 := by
    simp only [b₁,ERK9RationalFifteen.b,smul_smul,hz₁,zero_smul]
  have left (t : FiniteRootedTree) : e*cond (A₁+A₂) (b₁+b₂) t=cond A₁ b₁ t :=
    cut_sum he hA₂ hb₂ cu₁ t
  have right (t : FiniteRootedTree) :
      (1-e)*cond (A₁+A₂) (b₁+b₂) t=cond A₂ b₂ t := by
    simpa only [add_comm] using cut_sum (U:=A₂) he' hA₁ hb₁ cv₂ t
  have left_order (t : FiniteRootedTree) (ht : (t.order:ℕ)≤9) : cond A₁ b₁ t=e := by
    have h := scaled_order_value ERK9RationalFifteen.integerA ERK9RationalFifteen.bNum t
      D₁ d₁ (ERK9RationalFifteen.integer_moments ERK9RationalFifteen.receipts t ht)
    change cond A₁ b₁ t=((D₁:R)*d₁)^(t.order:ℕ) at h
    rwa [hd₁,cutPow he t] at h
  have right_order (t : FiniteRootedTree) (ht : (t.order:ℕ)≤9) :
      cond A₂ b₂ t=1-e := by
    have h := scaled_order_value ERK9RationalFifteenSecond.integerA ERK9RationalFifteenSecond.bNum t
      D₂ d₂ (ERK9RationalFifteenSecond.integer_moments ERK9RationalFifteenSecond.receipts t ht)
    change cond A₂ b₂ t=((D₂:R)*d₂)^(t.order:ℕ) at h
    rwa [hd₂,cutPow he' t] at h
  refine ⟨A₁+A₂,b₁+b₂,?_,?_,?_⟩
  · intro i j hij
    change ERK9RationalFifteen.A d₁ i j+ERK9RationalFifteenSecond.A d₂ i j=0
    rw [ERK9RationalFifteen.explicit d₁ (i:=i) (j:=j) hij,
      ERK9RationalFifteenSecond.explicit d₂ (i:=i) (j:=j) hij,zero_add]
  · intro t ht
    change cond (A₁+A₂) (b₁+b₂) t=1
    calc
      _ = e*cond (A₁+A₂) (b₁+b₂) t+(1-e)*cond (A₁+A₂) (b₁+b₂) t := by ring
      _ = 1 := by rw [left t,right t,left_order t ht,right_order t ht]; ring
  · intro h10
    let t := ERK9RationalFifteen.bush10
    have ht : (t.order:ℕ)=10 := by decide
    have h := h10 t (le_of_eq ht)
    change cond (A₁+A₂) (b₁+b₂) t=1 at h
    have hp : cond A₁ b₁ t=e := by rw [←left t,h,mul_one]
    have hDef := scaled_tenth_residual ERK9RationalFifteen.integerA
      ERK9RationalFifteen.bNum t D₁ (9984:ℤ) (5:ℤ) d₁ ht
        (ERK9RationalFifteen.bush_integer)
    change ((9984:ℤ):R)*(cond A₁ b₁ t-((D₁:R)*d₁)^10)=((5:ℤ):R)*((D₁:R)*d₁)^10 at hDef
    rw [hd₁,(show e^10=e from (show IsIdempotentElem e from he).pow_eq (by decide)),hp,sub_self,mul_zero] at hDef
    have hzero : (5:R)*e=0 := by simpa only [Int.cast_ofNat] using hDef.symm
    obtain ⟨u,hu⟩ := unit_five h9
    have hu0 : (u:R)*e=0 := by rwa [hu]
    have e0 : e=0 := calc
      e = ((↑(u⁻¹):R)*(u:R))*e := by rw [u.inv_mul,one_mul]
      _ = 0 := by rw [mul_assoc,hu0,mul_zero]
    have dFinal : (D₂:R)*d₂=1 := by simpa [e0] using hd₂
    apply ERK9RationalFifteenSecond.not_order_ten d₂ dFinal
    intro v hv
    change cond A₂ b₂ v=1
    have hh := h10 v hv
    change cond (A₁+A₂) (b₁+b₂) v=1 at hh
    rw [←right v,hh,e0,sub_zero,mul_one]

end RKResearch.Certified.ERK9FifteenLocalRing
