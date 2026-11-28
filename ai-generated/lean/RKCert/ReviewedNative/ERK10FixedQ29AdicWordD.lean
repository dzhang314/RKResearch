module
public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordCenters
@[expose] public section

/- BUNDLE PrimitiveZ -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open scoped Ring

noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

def normalDelta (s t k : R) : R := 3*s*k-2*t*k+t

def normalP (s k y : R) : R :=
  2*y*(3:R)⁻¹ʳ+k*(4*s*(3:R)⁻¹ʳ-2)*(y-1)
def normalQ (s t k y : R) : R :=
  k*(y-1)+s*k*(y-1)*(y-s)*(normalDelta s t k)⁻¹ʳ
def normalR (s t k y : R) : R :=
  y^2*(2:R)⁻¹ʳ+k*(s^2-2)*(y-1)-
    s*k*(s*k-t*k-t+2)*(y-1)*(y-s)*(normalDelta s t k)⁻¹ʳ
def normalN (s t k y : R) : R := -4*s*k+(-2-4*k*(s-t))*y

/-- The true coefficient identity for the primitive observer relation
4 T(L) = Z, after paid scaling by the first live clock. -/
theorem normal_primitive_Z (s t k y : R)
    (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R))
    (hd : IsUnit (normalDelta s t k)) (hk : 2*k*(t-2*s)=t) :
    4*normalR s t k y-6*t*normalP s k y+2*t^2+4*(2-t)*normalQ s t k y
      -4*t*(2-t)*k*(y-1)+(y-t)*normalN s t k y=0 := by
  let d := normalDelta s t k
  have h_2 := Ring.mul_inverse_cancel _ h2
  have h_3 := Ring.mul_inverse_cancel _ h3
  have h_d := Ring.mul_inverse_cancel _ hd
  apply hd.mul_left_cancel
  rw [mul_zero]
  unfold normalR normalP normalQ normalN
  have H :
      d*(4*(y^2*(2:R)⁻¹ʳ+k*(s^2-2)*(y-1)-
                   s*k*(s*k-t*k-t+2)*(y-1)*(y-s)*d⁻¹ʳ)-
          6*t*(2*y*(3:R)⁻¹ʳ+k*(4*s*(3:R)⁻¹ʳ-2)*(y-1))+
          2*t^2+4*(2-t)*(k*(y-1)+s*k*(y-1)*(y-s)*d⁻¹ʳ)-
          4*t*(2-t)*k*(y-1)+(y-t)*(-4*s*k+(-2-4*k*(s-t))*y))=0 := by
    change d*d⁻¹ʳ=1 at h_d
    unfold d normalDelta at *
    linear_combination
      (2*y^2*(3*s*k-2*t*k+t))*h_2+
      ((-4*t*y-8*t*k*s*(y-1))*(3*s*k-2*t*k+t))*h_3-
      (4*s*k^2*(s-t)*(y-1)*(y-s))*h_d+
      (2*(-2*k*s^2*y+2*k*s^2+2*k*s*t*y-5*k*s*t+2*k*s*y^2+k*s*y+
          2*k*t^2-2*k*t*y^2-t^2+t*y))*hk
  exact H

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.normal_primitive_Z

/- BUNDLE DRow -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def ellObserver (c a y w u : R) : R :=
  w*scalarL c y+(2-cOverA c a)*(y-c)*u

def ellRead (c a : R) (P : Word→R) : R :=
  4*P 3-6*c*P 2+2*c^2*P 1+4*(2-cOverA c a)*P 5-4*c*(2-cOverA c a)*P 4

theorem ellRead_input (c a b y w u : R) (h2 : IsUnit (2:R)) :
    ellRead c a (wordLine c a b y w u)=4*ellObserver c a y w u := by
  change 4*(y^3*w)-6*c*(y^2*w)+2*c^2*(y*w)+
    4*(2-cOverA c a)*(y*u)-4*c*(2-cOverA c a)*u=4*ellObserver c a y w u
  unfold ellObserver scalarL
  linear_combination (2*w*(3*c*y^2-c^2*y))*(Ring.mul_inverse_cancel _ h2)

theorem head_normalN (c a b y : R) (ha : IsUnit a) (hD : IsUnit (2*b-c))
    (hK : IsUnit (2*c-4*b)) :
    headN c a b y=a*normalN (bOverA a b) (cOverA c a) (headK c b) (y*a⁻¹ʳ) := by
  let s:=bOverA a b
  let t:=cOverA c a
  let k:=headK c b
  let x:=y*a⁻¹ʳ
  have hs : a*s=b := by unfold s bOverA;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have ht : a*t=c := by unfold t cOverA;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hx : a*x=y := by unfold x;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hk : (2*c-4*b)*k=c := by unfold k headK;rw [mul_left_comm,Ring.mul_inverse_cancel _ hK,mul_one]
  have hNorm : a*normalN s t k x= -4*b*k+(-2-4*k*(s-t))*y := by
    unfold normalN
    linear_combination -4*k*hs+(-2-4*k*(s-t))*hx
  change headN c a b y=a*normalN s t k x
  apply (ha.mul hD).mul_left_cancel
  rw [scaled_N c a b y ha hD,hNorm,nNum]
  linear_combination -2*a*(b+(s-t)*y)*hk-2*c*y*hs+2*c*y*ht

theorem ellRead_target (c a b y w u : R)
    (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (h4 : IsUnit (4:R))
    (ha : IsUnit a) (hD : IsUnit (2*b-c)) (hK : IsUnit (2*c-4*b))
    (hδ : IsUnit (headDelta c a b)) :
    ellRead c a (targetLine c a b y w u)=observerZ c a b y w u := by
  let s:=bOverA a b
  let t:=cOverA c a
  let k:=headK c b
  let x:=y*a⁻¹ʳ
  have ht : a*t=c := by unfold t cOverA;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hx : a*x=y := by unfold x;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hk : 2*k*(t-2*s)=t := center_kappa_relation ha hK
  have hd : IsUnit (normalDelta s t k) := hδ
  have hn : headN c a b y=a*normalN s t k x := head_normalN c a b y ha hD hK
  have hP : modelP c a b x=normalP s k x := rfl
  have hQ : modelQ c a b x=normalQ s t k x := rfl
  have hR : modelR c a b x=normalR s t k x := rfl
  have hN := normal_primitive_Z s t k x h2 h3 hd hk
  unfold ellRead
  simp only [targetLine,Matrix.cons_val_succ',Matrix.cons_val_zero']
  change 4*(w*y^4*(4:R)⁻¹ʳ+u*a^2*modelR c a b x)-
      6*c*(w*y^3*(3:R)⁻¹ʳ+u*a*modelP c a b x)+
      2*c^2*(w*y^2*(2:R)⁻¹ʳ+u)+4*(2-t)*(u*a^2*modelQ c a b x)-
      4*c*(2-t)*(u*k*(y-a))=_
  rw [hR,hP,hQ,observerZ,scalarM,hn]
  linear_combination
    w*y^4*(Ring.mul_inverse_cancel _ h4)-
    2*c*w*y^3*(Ring.mul_inverse_cancel _ h3)+
    c^2*w*y^2*(Ring.mul_inverse_cancel _ h2)+
    (u*a^2)*hN+
    (6*u*a*normalP s k x-2*u*(c+a*t)+4*(2-t)*k*u*(y-a)+u*a*normalN s t k x)*ht+
    (4*a*t*(2-t)*k*u-u*a*normalN s t k x)*hx

theorem ellRead_sum (c a : R) (v : Site→R) (A : Site→Word→R) :
    ellRead c a (fun k => ∑ j : Site,v j*A j k)=
      ∑ j : Site,v j*ellRead c a (A j) := by
  unfold ellRead
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actual_targetZ_d :
    wordTarget c a b 5 7=0 := by
  let x:=nodal c a b
  let w:=score x nodeD
  let u:=uAggregate x (actualScale x) nodeD
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hdiff (i j : Site) (h : i≠j) := hAll i (Finset.mem_univ _) j (Finset.mem_univ _) h
  have hda : IsUnit ((26:R)-a) := hdiff nodeD headA (by decide +kernel)
  have hdb : IsUnit ((26:R)-b) := hdiff nodeD headB (by decide +kernel)
  have hdc : IsUnit ((26:R)-c) := hdiff nodeD center (by decide +kernel)
  have hdh : IsUnit (26:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have H : IsUnit ((26:R)^2*(26-c)) := (hdh.pow 2).mul hdc
  have hq : caseQZ c a b 26=datumQZ c a b 26 := by
    unfold caseQZ basisQZ
    rw [Ring.mul_inverse_cancel _ ((hdc.mul hda).mul hdb)]
    simp
  have hRead : w*26^2*(26-c)=headN c a b 26*u :=
    actual_head_ratio ρ c a b hp hc ha hb hRoot hOther nodeD (Or.inr (Or.inl rfl))
  change targetZ c a b 26 w u=0
  apply H.mul_left_cancel
  rw [mul_zero,targetZ,hq,datumQZ]
  linear_combination casePZ c 26*hRead-
    u*headN c a b 26*casePZ c 26*(Ring.mul_inverse_cancel _ H)

theorem actual_ell_zero_front (j : Site) (hj : j.val < 5) :
    ellObserver c a (rawY c a b j) (rawW c a b j) (rawU c a b j)=0 := by
  have hG : wordInput c a b j 6=0 :=
    actual_G_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj.trans (by decide)⟩
  change (rawY c a b j-26)*ellObserver c a (rawY c a b j) (rawW c a b j) (rawU c a b j)=0 at hG
  have hu : IsUnit (rawY c a b j-26) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    have hh := congrFun (actual_Y_mod ρ c a b hc ha hb) j
    change ρ (rawY c a b j)=Ymod j at hh
    rw [map_sub,map_ofNat,hh]
    exact (show ∀ j : Site,j.val < 5→Ymod j-26≠0 from by decide +kernel) j hj
  exact hu.mul_left_cancel (by rwa [mul_zero])

/-- Complete the five-donor d row. Its sole missing primitive word is
forced by the exact observer relation rather than an extra free tap. -/
theorem actualK_d (k : Word) :
    ∑ j : Site,actualK c a b 5 j*wordInput c a b j k=wordTarget c a b 5 k := by
  let W : Word→R := fun k => ∑ j : Site,actualK c a b 5 j*wordInput c a b j k
  let T := wordTarget c a b 5
  have hSel (k : Word) (h : k.val < 5) : W k=T k := by
    let j : Fin (leadingLength (5 : Site)) := ⟨k.val,h⟩
    have hj : Fin.castLE (leading_le (5 : Site)) j=k := Fin.ext rfl
    simpa only [hj] using actualK_leading ρ c a b hp hc ha hb 5 j
  by_cases hk : k.val < 5
  · exact hSel k hk
  have htail : k=5 ∨ k=6 ∨ k=7 := by
    have hk8 := k.isLt
    have hh : k.val=5 ∨ k.val=6 ∨ k.val=7 := by omega
    rcases hh with hh|hh|hh
    · exact Or.inl (Fin.ext hh)
    · exact Or.inr (Or.inl (Fin.ext hh))
    · exact Or.inr (Or.inr (Fin.ext hh))
  obtain ⟨h2,h3,h4,_⟩ := standard_paid ρ
  obtain ⟨haU,hK,_⟩ := actual_head_denominator_units ρ c a b hc ha hb
  have hDn : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hBU : IsUnit (4*(2-cOverA c a)) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    rw [map_mul,map_sub,map_ofNat,map_ofNat,actual_ca_residue ρ c a hc ha]
    decide +kernel
  have hZ0 : observerZ c a b 26 (rawW c a b 5) (rawU c a b 5)=0 :=
    actual_singleton_Z_zero ρ c a b hp hc ha hb hRoot hOther nodeD (Or.inr (Or.inl rfl))
  have hT7 : T 7=0 := actual_targetZ_d ρ c a b hp hc ha hb hRoot hOther
  rcases htail with rfl|rfl|rfl
  · have hRW : ellRead c a W=0 := by
      unfold W
      rw [ellRead_sum]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j.val < 5
      · change _*ellRead c a (wordLine c a b (rawY c a b j) (rawW c a b j) (rawU c a b j))=0
        rw [ellRead_input c a b _ _ _ h2,
          actual_ell_zero_front ρ c a b hp hc ha hb hRoot hOther j hj,mul_zero,mul_zero]
      · rw [actualK_strict c a b 5 j (show (5 : Site)≤j from Nat.le_of_not_gt hj),zero_mul]
    have hRT : ellRead c a T=0 := by
      change ellRead c a (targetLine c a b 26 (rawW c a b 5) (rawU c a b 5))=0
      rw [ellRead_target c a b _ _ _ h2 h3 h4 haU hDn hK
        (center_dUnit ρ c a b hc ha hb),hZ0]
    change W 5=T 5
    unfold ellRead at hRW hRT
    simp only [hSel 1 (by decide),hSel 2 (by decide),hSel 3 (by decide),hSel 4 (by decide)] at hRW
    apply hBU.mul_left_cancel
    linear_combination hRW-hRT
  · have hT6 : T 6=0 := by
      change ((26-26)*observerZ c a b 26 (rawW c a b 5) (rawU c a b 5)-T 7)*(4:R)⁻¹ʳ=0
      simp [hT7]
    change W 6=T 6
    rw [hT6]
    unfold W
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < 5
    · have h : wordInput c a b j 6=0 :=
        actual_G_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj.trans (by decide)⟩
      rw [h,mul_zero]
    · rw [actualK_strict c a b 5 j (show (5 : Site)≤j from Nat.le_of_not_gt hj),zero_mul]
  · change W 7=T 7
    rw [hT7]
    unfold W
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < 5
    · have h : wordInput c a b j 7=0 :=
        actual_Z_earliest ρ c a b hp hc ha hb hRoot hOther ⟨j.val,hj.trans (by decide)⟩
      rw [h,mul_zero]
    · rw [actualK_strict c a b 5 j (show (5 : Site)≤j from Nat.le_of_not_gt hj),zero_mul]

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ellRead_target
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_d
