module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailPhysicalAlign

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric ZTail
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

omit hp in
theorem paid_raw_cardinal (i : Site) (hi : i∈singletonSites) :
    let x:=nodal c a b
    Den cardSites x i*score x i=(actualMu c).eval (x i) := by
  let x:=nodal c a b
  obtain ⟨_,_,_,hh,hC,_,_⟩ := singleton_flags i hi
  change Den cardSites x i*score x i=_
  rw [score,ite_eq_right hh,
    den_mul_cardinal (den_unit (actual_paid_sites ρ c a b hc ha hb cardSites) hC),
    true_cardinal_numerator hRoot hOther hi]

omit hp in
theorem cofactor_losses_paid (i : Site) (hi : i∈singletonSites) :
    let x:=nodal c a b
    (x i)*(x i-1)*Den ordinary x i*score x i=(x i-15)*(actualMu c).eval (x i) ∧
      Den ordinary x i*uAggregate x (actualScale x) i=actualScale x := by
  let x:=nodal c a b
  obtain ⟨_,_,_,_,_,hO,_⟩ := singleton_flags i hi
  constructor
  · rw [show (x i)*(x i-1)*Den ordinary x i=(x i-15)*Den cardSites x i from link_dens c a b hi,
      mul_assoc,paid_raw_cardinal ρ c a b hc ha hb hRoot hOther i hi]
  · have hu := den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) hO
    change Den ordinary x i*uAggregate x (actualScale x) i=actualScale x
    unfold uAggregate ordInv
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hu,mul_one]

omit hp ha hb hRoot hOther in
theorem actual_N26_unit : IsUnit ((N c).eval 26) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  simp only [n_eval,map_mul,map_add,map_sub,map_neg,map_pow,map_ofNat,map_headProduct,map_headSum,
    hc,headProduct_residue,headSum_residue]
  decide +kernel

theorem actual_scale_factor :
    actualScale (nodal c a b)=nScale c a b*scaleZ c := by
  let x:=nodal c a b
  let D:=Den ordinary x nodeD
  let S:=actualScale x
  let w:=score x nodeD
  let u:=uAggregate x S nodeD
  let μ:=(actualMu c).eval 26
  have hi : nodeD∈singletonSites := by decide +kernel
  have ratio := actual_head_ratio ρ c a b hp hc ha hb hRoot hOther nodeD (Or.inr (Or.inl rfl))
  change w*26^2*(26-c)=headN c a b 26*u at ratio
  obtain ⟨hW,hU⟩ := cofactor_losses_paid ρ c a b hc ha hb hRoot hOther nodeD hi
  change (26:R)*(26-1)*D*w=(26-15)*μ at hW
  change D*u=S at hU
  have hR : (26-1)*headN c a b 26*S=μ*26*(26-15)*(26-c) := by
    calc
      _ = ((26-1)*D)*(headN c a b 26*u) := by rw [←hU];ring
      _ = _ := by
        rw [←ratio]
        linear_combination (26:R)*(26-c)*hW
  have haU := (actual_head_denominator_units ρ c a b hc ha hb).1
  have hd : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hN : (N c).eval 26=nScale c a b*headN c a b 26 := by
    rw [nFlat_true c a b 26 hRoot hOther,nScale,scaled_N c a b 26 haU hd]
  have h25 : IsUnit ((26:R)-1) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_ofNat,map_one];decide +kernel))
  have hD := actual_N26_unit ρ c hc
  apply (h25.mul hD).mul_left_cancel
  calc
    _ = nScale c a b*((26-1)*headN c a b 26*S) := by rw [hN];ring
    _ = _ := by
      rw [hR,←actual_scale_read ρ c hp hc]
      ring

theorem actual_targetZ_tail (i : Site) (hi : i=nodeE ∨ i=nodeF) :
    let x:=nodal c a b
    targetZ c a b (x i) (score x i) (uAggregate x (actualScale x) i)=0 := by
  let x:=nodal c a b
  let y:=x i
  let w:=score x i
  let u:=uAggregate x (actualScale x) i
  let D:=Den ordinary x i
  let S:=actualScale x
  let μ:=(actualMu c).eval y
  have hs : i∈singletonSites := by rcases hi with rfl|rfl <;> decide +kernel
  obtain ⟨h0,h1,_,_,_,hO,_⟩ := singleton_flags i hs
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hu0 : IsUnit y := by
    simpa only [show nodal c a b endNode=0 from rfl,sub_zero] using
      hAll i (Finset.mem_univ _) endNode (Finset.mem_univ _) h0
  have hu1 : IsUnit (y-1) := hAll i (Finset.mem_univ _) oldOrigin (Finset.mem_univ _) h1
  have hD : IsUnit D := den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) hO
  have h30 : IsUnit (30:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have hJ := jacobi_center_paid ρ c hc
  have hScale : IsUnit (pScale c) := h30.mul hJ
  obtain ⟨h2,h3,_,_⟩ := standard_paid ρ
  have h5 : IsUnit (5:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have hRead :
      μ*(y-15)*(P c).eval y+(y-1)*y*scaleZ c*(y-c)*(V c).eval y=0 := by
    rcases hi with rfl|rfl
    · exact actual_output_e ρ c hp hc
    · exact actual_output_f ρ c hp hc
  obtain ⟨hW,hU⟩ := cofactor_losses_paid ρ c a b hc ha hb hRoot hOther i hs
  change y*(y-1)*D*w=(y-15)*μ at hW
  change D*u=S at hU
  have QZ := actual_norm_QZ ρ c a b hp hc ha hb hRoot hOther y
  have hP := scaled_PZ c y h2 h3 h5 hJ
  change targetZ c a b y w u=0
  apply (hScale.mul ((hu0.mul hu1).mul hD)).mul_left_cancel
  rw [mul_zero]
  calc
    _ = (y*(y-1)*D*w)*(pScale c*casePZ c y)+
       y*(y-1)*(D*u)*pScale c*caseQZ c a b y := by unfold targetZ;ring
    _ = _ := by
      have hS : S=nScale c a b*scaleZ c :=
        actual_scale_factor ρ c a b hp hc ha hb hRoot hOther
      rw [hW,hU,hP,hS]
      have hQterm :
          y*(y-1)*(nScale c a b*scaleZ c)*pScale c*caseQZ c a b y =
            (y-1)*y*scaleZ c*((nScale c a b*pScale c)*caseQZ c a b y) := by ring
      rw [hQterm,QZ]
      linear_combination hRead

/-- Complete actual reverse row e (its two omitted observers both vanish). -/
theorem actualK_e (k : Word) :
    ∑ j : Site,actualK c a b 6 j*wordInput c a b j k=wordTarget c a b 6 k := by
  by_cases h : k.val<6
  · let j : Fin (leadingLength (6:Site)) := ⟨k.val,h⟩
    have hj : Fin.castLE (leading_le (6:Site)) j=k := Fin.ext rfl
    simpa only [hj] using actualK_leading ρ c a b hp hc ha hb 6 j
  have hlast : k=6 ∨ k=7 := by
    have hk := k.isLt
    have hv : k.val=6 ∨ k.val=7 := by omega
    exact hv.elim (fun hh => Or.inl (Fin.ext hh)) (fun hh => Or.inr (Fin.ext hh))
  have hz : wordTarget c a b 6 7=0 :=
    actual_targetZ_tail ρ c a b hp hc ha hb hRoot hOther nodeE (Or.inl rfl)
  have hze : observerZ c a b (rawY c a b 6) (rawW c a b 6) (rawU c a b 6)=0 :=
    actual_singleton_Z_zero ρ c a b hp hc ha hb hRoot hOther nodeE (Or.inr (Or.inr rfl))
  rcases hlast with rfl|rfl
  · have hG : wordTarget c a b 6 6=0 := by
      change ((rawY c a b 6-26)*observerZ c a b (rawY c a b 6)
        (rawW c a b 6) (rawU c a b 6)-wordTarget c a b 6 7)*(4:R)⁻¹ʳ=0
      rw [hze,hz,mul_zero,sub_self,zero_mul]
    rw [hG]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val<6
    · have hv : wordInput c a b j 6=0 := actual_G_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj⟩
      rw [hv,mul_zero]
    · rw [actualK_strict c a b 6 j (show (6:Site)≤j from Nat.le_of_not_gt hj),zero_mul]
  · rw [hz]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val<6
    · have hv : wordInput c a b j 7=0 :=
        actual_Z_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj.trans (by decide)⟩
      rw [hv,mul_zero]
    · rw [actualK_strict c a b 6 j (show (6:Site)≤j from Nat.le_of_not_gt hj),zero_mul]

/-- Complete actual reverse row f (the seventh leading word excludes
only the terminal observer, whose target is exactly zero). -/
theorem actualK_f (k : Word) :
    ∑ j : Site,actualK c a b 7 j*wordInput c a b j k=wordTarget c a b 7 k := by
  by_cases h : k.val<7
  · let j : Fin (leadingLength (7:Site)) := ⟨k.val,h⟩
    have hj : Fin.castLE (leading_le (7:Site)) j=k := Fin.ext rfl
    simpa only [hj] using actualK_leading ρ c a b hp hc ha hb 7 j
  have h7 : k=7 := by
    apply Fin.ext
    have hk := k.isLt
    change k.val=7
    omega
  subst k
  have hz : wordTarget c a b 7 7=0 :=
    actual_targetZ_tail ρ c a b hp hc ha hb hRoot hOther nodeF (Or.inr rfl)
  rw [hz]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val<7
  · have hv : wordInput c a b j 7=0 := actual_Z_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj⟩
    rw [hv,mul_zero]
  · rw [actualK_strict c a b 7 j (show (7:Site)≤j from Nat.le_of_not_gt hj),zero_mul]

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_scale_factor
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_targetZ_tail
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_e
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_f
