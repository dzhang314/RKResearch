module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadPhysical

@[expose] public section

/- ThirdRow: the complete paid earlier word adapter. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def firstRatioFactor (a : R) : Word→R :=
  ![0,1,a,a^2,-a*(2:R)⁻¹ʳ,-a^2*(2:R)⁻¹ʳ,0,0]

theorem caseQZ_at_b (c a b : R) (hbC : IsUnit (b-c))
    (hbA : IsUnit (b-a)) (hbD : IsUnit (b-26)) :
    caseQZ c a b b=datumQZ c a b b := by
  unfold caseQZ basisQZ
  rw [Ring.mul_inverse_cancel _ ((hbC.mul hbA).mul hbD)]
  simp

theorem b_ratio_gain (c a b w u : R)
    (ha : IsUnit a) (hD : IsUnit (2*b-c)) (hK : IsUnit (2*c-4*b))
    (hbc : IsUnit (b-c))
    (hr : w*b^2*(b-c)=headN c a b b*u) :
    w*b^2=(-2-4*headK c b*(bOverA a b-1))*u := by
  let k:=headK c b
  let s:=bOverA a b
  have hs : a*s=b := by
    unfold s bOverA
    rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hk : (2*c-4*b)*k=c := by
    unfold k headK
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hK,mul_one]
  have hN : headN c a b b=(b-c)*(-2-4*k*(s-1)) := by
    apply (ha.mul hD).mul_left_cancel
    rw [scaled_N c a b b ha hD]
    unfold nNum
    linear_combination -(2*a*(s-1)*(b-c))*hk-2*c*(b-c)*hs
  apply hbc.mul_left_cancel
  calc
    _ = headN c a b b*u := by linear_combination hr
    _ = _ := by rw [hN];ring

theorem input_a_factor (c a b w u : R) (h2 : IsUnit (2:R))
    (ha : IsUnit a) (hD : IsUnit (2*b-c)) (hu : w*a^2+2*u=0) {j : Word} (hj : j≠0) :
    wordLine c a b a w u j=firstRatioFactor a j*(a*w) := by
  have i2 := Ring.mul_inverse_cancel _ h2
  have ia := Ring.mul_inverse_cancel _ ha
  have zz : observerZ c a b a w u=0 := by
    unfold observerZ scalarM
    rw [headN_at_a c a b ha hD]
    linear_combination (a-c)^2*hu
  have hL : w*scalarL c a+(2-cOverA c a)*(a-c)*u=0 := by
    apply (h2.mul ha).mul_left_cancel
    rw [mul_zero]
    unfold scalarL cOverA
    linear_combination
      ((a-c)*(2*a-c))*hu-a*w*(3*c*a^2-c^2*a)*i2-2*c*(a-c)*u*ia
  have gg : observerG c a a w u=0 := by rw [observerG,hL,mul_zero]
  fin_cases j
  · exact (hj rfl).elim
  · simp [wordLine,firstRatioFactor]
  · simp [wordLine,firstRatioFactor];ring
  · simp [wordLine,firstRatioFactor];ring
  · change u= -a*(2:R)⁻¹ʳ*(a*w)
    linear_combination (2:R)⁻¹ʳ*hu-u*i2
  · change a*u= -a^2*(2:R)⁻¹ʳ*(a*w)
    linear_combination a*(2:R)⁻¹ʳ*hu-a*u*i2
  · simp [wordLine,firstRatioFactor,gg]
  · simp [wordLine,firstRatioFactor,zz]

theorem target_b_factor (c a b w u : R)
    (h2 : IsUnit (2:R)) (h4 : IsUnit (4:R))
    (ha : IsUnit a) (hb : IsUnit b) (hD : IsUnit (2*b-c)) (hK : IsUnit (2*c-4*b))
    (hbC : IsUnit (b-c)) (hbA : IsUnit (b-a)) (hbD : IsUnit (b-26))
    (hr : w*b^2*(b-c)=headN c a b b*u) {j : Word} (hj : j≠0) :
    targetLine c a b b w u j=firstRatioFactor a j*(w*b^2*(2:R)⁻¹ʳ+u) := by
  let k:=headK c b
  let s:=bOverA a b
  let v:=w*b^2*(2:R)⁻¹ʳ+u
  have i2 := Ring.mul_inverse_cancel _ h2
  have i4 := Ring.mul_inverse_cancel _ h4
  have h24 : (2:R)⁻¹ʳ=2*(4:R)⁻¹ʳ := by
    apply h2.mul_left_cancel
    linear_combination i2-i4
  have hs : a*s=b := by
    unfold s bOverA
    rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hm : w*b^2=(-2-4*k*(s-1))*u := b_ratio_gain c a b w u ha hD hK hbC hr
  have hv : v= -2*k*(s-1)*u := by
    unfold v
    rw [hm]
    linear_combination -(1+2*k*(s-1))*u*i2
  have hZ : observerZ c a b b w u=0 := by
    unfold observerZ scalarM
    linear_combination (b-c)*hr
  have ht : targetZ c a b b w u=0 := by
    have hU := (hb.pow 2).mul hbC
    have hI := Ring.mul_inverse_cancel _ hU
    apply hU.mul_left_cancel
    rw [mul_zero,targetZ,caseQZ_at_b c a b hbC hbA hbD,datumQZ]
    linear_combination casePZ c b*hr-u*headN c a b b*casePZ c b*hI
  fin_cases j
  · exact (hj rfl).elim
  · simp [targetLine,firstRatioFactor]
  · change w*b^3*(3:R)⁻¹ʳ+u*a*modelP c a b s=a*v
    change w*b^3*(3:R)⁻¹ʳ+u*a*(2*s*(3:R)⁻¹ʳ+k*(4*s*(3:R)⁻¹ʳ-2)*(s-1))=a*v
    calc
      _ = (w*b^2)*b*(3:R)⁻¹ʳ+u*a*(2*s*(3:R)⁻¹ʳ+k*(4*s*(3:R)⁻¹ʳ-2)*(s-1)) := by ring
      _ = _ := by rw [hm,←hs,hv];ring
  · change w*b^4*(4:R)⁻¹ʳ+u*a^2*modelR c a b s=a^2*v
    have hr0 : modelR c a b s=s^2*(2:R)⁻¹ʳ+k*(s^2-2)*(s-1) := by
      unfold modelR
      simp only [show bOverA a b=s from rfl,sub_self,mul_zero,zero_mul,sub_zero]
      rfl
    rw [hr0]
    calc
      _ = (w*b^2)*b^2*(4:R)⁻¹ʳ+u*a^2*(s^2*(2:R)⁻¹ʳ+k*(s^2-2)*(s-1)) := by ring
      _ = _ := by
        rw [hm,←hs,hv,h24]
        linear_combination -u*a^2*k*(s-1)*s^2*i4
  · change u*k*(b-a)= -a*(2:R)⁻¹ʳ*v
    rw [←hs,hv]
    linear_combination -u*a*k*(s-1)*i2
  · change u*a^2*modelQ c a b s= -a^2*(2:R)⁻¹ʳ*v
    have hr0 : modelQ c a b s=k*(s-1) := by
      unfold modelQ
      simp only [show bOverA a b=s from rfl,sub_self,mul_zero,zero_mul,add_zero]
      rfl
    rw [hr0,hv]
    linear_combination -u*a^2*k*(s-1)*i2
  · simp [targetLine,firstRatioFactor,targetG,hZ,ht]
  · simp [targetLine,firstRatioFactor,ht]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actualK_third (k : Word) :
    ∑ j : Site, actualK c a b 2 j*wordInput c a b j k=wordTarget c a b 2 k := by
  by_cases hk0 : k=0
  · subst k
    exact actualK_leading ρ c a b hp hc ha hb 2 ⟨0,by decide +kernel⟩
  let x:=nodal c a b
  have h2 : IsUnit (2:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h4 : IsUnit (4:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have haU : IsUnit a := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [ha];decide +kernel))
  have hbU : IsUnit b := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [hb];decide +kernel))
  have hg : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hk : IsUnit (2*c-4*b) := (actual_head_denominator_units ρ c a b hc ha hb).2.1
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hbC : IsUnit (b-c) := hAll headB (Finset.mem_univ _) center (Finset.mem_univ _) (by decide +kernel)
  have hbA : IsUnit (b-a) := hAll headB (Finset.mem_univ _) headA (Finset.mem_univ _) (by decide +kernel)
  have hbD : IsUnit (b-26) := hAll headB (Finset.mem_univ _) nodeD (Finset.mem_univ _) (by decide +kernel)
  have haD : IsUnit (Den ordinary x headA) :=
    den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) (by decide +kernel)
  have hin : wordInput c a b 1 k=firstRatioFactor a k*wordInput c a b 1 1 :=
    input_a_factor c a b (score x headA) (uAggregate x (actualScale x) headA)
      h2 haU hg (actual_first_u x haD h2) hk0
  have ht : wordTarget c a b 2 k=firstRatioFactor a k*wordTarget c a b 2 1 :=
    target_b_factor c a b (score x headB) (uAggregate x (actualScale x) headB) h2 h4 haU hbU hg hk
      hbC hbA hbD (actual_head_ratio ρ c a b hp hc ha hb hRoot hOther headB (Or.inl rfl)) hk0
  have single (k : Word) (hk : k≠0) :
      ∑ j : Site, actualK c a b 2 j*wordInput c a b j k=actualK c a b 2 1*wordInput c a b 1 k := by
    rw [Finset.sum_eq_single 1]
    · intro j _ hj
      by_cases h0 : j=0
      · subst j
        have hz : wordInput c a b 0 k=0 := input_at_endpoint c a b _ hk
        rw [hz,mul_zero]
      · have hn : (2:Site) ≤ j := by
          change 2 ≤ j.val
          have h0' : j.val≠0 := fun zz => h0 (Fin.ext zz)
          have h1' : j.val≠1 := fun zz => hj (Fin.ext zz)
          omega
        rw [actualK_strict c a b 2 j hn,zero_mul]
    · simp
  have h1 : 1 < leadingLength (2:Site) := by decide +kernel
  have hpaid : ∑ j : Site, actualK c a b 2 j*wordInput c a b j 1=wordTarget c a b 2 1 :=
    actualK_leading ρ c a b hp hc ha hb 2 ⟨1,h1⟩
  rw [single 1 (by decide +kernel)] at hpaid
  rw [single k hk0,hin,ht,←hpaid]
  ring

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_third
