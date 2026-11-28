module
public import RKCert.ReviewedNative.ERK10FixedQ29AdicCenterReadoutVerified
@[expose] public section

/- BUNDLE CenterPaid -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open RKResearch.Certified.ERK10CenterScalar (Chart)
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

def centerChart (c a b : R) : Chart R :=
  let s:=bOverA a b
  let t:=cOverA c a
  let k:=headK c b
  let d:=headDelta c a b
  ⟨s,t,k,d,s⁻¹ʳ,t⁻¹ʳ,d⁻¹ʳ,(s-1)⁻¹ʳ,(2:R)⁻¹ʳ,(3:R)⁻¹ʳ,(4:R)⁻¹ʳ⟩

theorem standard_paid (ρ : R→+*F) [IsLocalHom ρ] :
    IsUnit (2:R) ∧ IsUnit (3:R) ∧ IsUnit (4:R) ∧ IsUnit (12:R) := by
  have h2 : IsUnit (2:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h3 : IsUnit (3:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have h4 : IsUnit (4:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  exact ⟨h2,h3,h4,(show (12:R)=3*4 by ring) ▸ h3.mul h4⟩

theorem center_kappa_relation {c a b : R} (ha : IsUnit a) (hd : IsUnit (2*c-4*b)) :
    2*headK c b*(cOverA c a-2*bOverA a b)=cOverA c a := by
  have hK : (2*c-4*b)*headK c b=c := by
    unfold headK
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hd,mul_one]
  apply ha.mul_left_cancel
  unfold bOverA cOverA
  linear_combination (a*a⁻¹ʳ)*hK

theorem actual_gainC (c a b : R) (hD : IsUnit (headDelta c a b))
    (hcd : IsUnit (c^2*headDelta c a b)) :
    (centerChart c a b).L=c^2*centerRatio c a b := by
  let s:=bOverA a b
  let t:=cOverA c a
  let k:=headK c b
  let d:=headDelta c a b
  let n:=(-2)*(2*s*t*k^2+2*s*t*k-2*s*k^2+s*k-2*t*k+t)
  have hu1 : d*d⁻¹ʳ=1 := Ring.mul_inverse_cancel _ hD
  have hu2 : (c^2*d)*(c^2*d)⁻¹ʳ=1 := Ring.mul_inverse_cancel _ hcd
  change n*d⁻¹ʳ=c^2*(n*(c^2*d)⁻¹ʳ)
  apply hD.mul_left_cancel
  change d*(n*d⁻¹ʳ)=d*(c^2*(n*(c^2*d)⁻¹ʳ))
  linear_combination n*hu1-n*hu2

section Paid
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

omit hp in
theorem center_dUnit : IsUnit (headDelta c a b) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [actual_delta_residue ρ c a b hc ha hb]
  decide +kernel

omit hp in
theorem center_chart_paid : (centerChart c a b).Paid := by
  obtain ⟨h2,h3,h4,h12⟩ := standard_paid ρ
  obtain ⟨haU,hK,_⟩ := actual_head_denominator_units ρ c a b hc ha hb
  have hs : IsUnit (bOverA a b) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    rw [actual_ba_residue ρ a b ha hb];decide +kernel
  have ht : IsUnit (cOverA c a) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    rw [actual_ca_residue ρ c a hc ha];decide +kernel
  have hr : IsUnit (bOverA a b-1) := by
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    rw [map_sub,map_one,actual_ba_residue ρ a b ha hb];decide +kernel
  have hD := center_dUnit ρ c a b hc ha hb
  exact ⟨(((h12.mul hs).mul ht).mul hD).mul hr,h4,
    Ring.mul_inverse_cancel _ hs,Ring.mul_inverse_cancel _ ht,Ring.mul_inverse_cancel _ hD,
    Ring.mul_inverse_cancel _ hr,Ring.mul_inverse_cancel _ h2,Ring.mul_inverse_cancel _ h3,
    Ring.mul_inverse_cancel _ h4,rfl,center_kappa_relation haU hK⟩

omit hp in
theorem actual_center_first_mass :
    rawW c a b 3*c^2=(centerChart c a b).L*rawU c a b 3 := by
  have hD := center_dUnit ρ c a b hc ha hb
  have hcd := (actual_head_denominator_units ρ c a b hc ha hb).2.2
  rw [actual_gainC c a b hD hcd]
  change (physicalPair c a b).L*(physicalPair c a b).split.u1*c^2 =
    c^2*centerRatio c a b*(physicalPair c a b).split.u1
  have h : (physicalPair c a b).L=centerRatio c a b := rfl
  rw [h]
  ring

omit hp in
theorem actual_center_nullGain_unit : IsUnit (centerChart c a b).G := by
  have hD := center_dUnit ρ c a b hc ha hb
  have hcd := (actual_head_denominator_units ρ c a b hc ha hb).2.2
  have hL : ρ (centerChart c a b).L=3 := by
    rw [actual_gainC c a b hD hcd,map_mul,map_pow,hc,actual_Lc_residue ρ c a b hc ha hb]
    decide +kernel
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  change ρ (-2*(cOverA c a-bOverA a b)+
    (1-cOverA c a)*(-2-4*headK c b*(bOverA a b-1))*(bOverA a b)⁻¹ʳ+
    (bOverA a b-1)*(centerChart c a b).L*(cOverA c a)⁻¹ʳ)≠0
  simp only [map_mul,map_add,map_sub,map_neg,map_one,map_ofNat,map_ringInverse,
    hL,actual_ca_residue ρ c a hc ha,actual_ba_residue ρ a b ha hb,
    actual_k_residue ρ c b hc hb,Ring.inverse_eq_inv]
  decide +kernel

end Paid

def positiveWord (j : Fin 5) : Word := ⟨j.val+1,by omega⟩
def donorSlot (j : Fin 3) : Site := ⟨j.val+1,by omega⟩
def wScale (a : R) : Fin 5→R := ![a,1,a⁻¹ʳ,1,a⁻¹ʳ]

theorem wScale_unit {a : R} (ha : IsUnit a) (j : Fin 5) : IsUnit (wScale a j) := by
  have hi : IsUnit a⁻¹ʳ := IsUnit.of_mul_eq_one a (by rw [mul_comm,Ring.mul_inverse_cancel _ ha])
  fin_cases j
  · exact ha
  · exact isUnit_one
  · exact hi
  · exact isUnit_one
  · exact hi

def donorMode (M x ix : R) : Fin 5→R := ![M*ix,M,x*M,1,x]

theorem scaled_word_donor (c a b y w u M x ix : R) (ha : IsUnit a)
    (hy : a*x=y) (hi : x*ix=1) (hM : u*M=w*y^2) (j : Fin 5) :
    wScale a j*wordLine c a b y w u (positiveWord j)=u*donorMode M x ix j := by
  have hxy : y*ix=a := by rw [←hy,mul_assoc,hi,mul_one]
  have hyx : a⁻¹ʳ*y=x := by rw [←hy,←mul_assoc,mul_comm a⁻¹ʳ a,Ring.mul_inverse_cancel _ ha,one_mul]
  fin_cases j
  · change a*(y*w)=u*(M*ix)
    calc
      _ = (w*y)*(y*ix) := by linear_combination -(w*y)*hxy
      _ = (w*y^2)*ix := by ring
      _ = _ := by rw [←hM];ring
  · change 1*(y^2*w)=u*M
    rw [one_mul,hM,mul_comm]
  · change a⁻¹ʳ*(y^3*w)=u*(x*M)
    calc
      _ = (a⁻¹ʳ*y)*(w*y^2) := by ring
      _ = _ := by rw [hyx,←hM];ring
  · simp [wScale,wordLine,positiveWord,donorMode]
  · change a⁻¹ʳ*(y*u)=u*x
    rw [←mul_assoc,hyx,mul_comm]

theorem scaled_center_target (c a b w u : R) (ha : IsUnit a) (j : Fin 5) :
    wScale a j*targetLine c a b c w u (positiveWord j)=
      a*((centerChart c a b).target (w*c^2) u j) := by
  let t:=cOverA c a
  have yc : a*t=c := by unfold t cOverA;rw [mul_left_comm,Ring.mul_inverse_cancel _ ha,mul_one]
  have hAI:=Ring.mul_inverse_cancel _ ha
  fin_cases j
  · rfl
  · change 1*(w*c^3*(3:R)⁻¹ʳ+u*a*modelP c a b t)=
       a*(w*c^2*t*(3:R)⁻¹ʳ+u*modelP c a b t)
    linear_combination -w*c^2*(3:R)⁻¹ʳ*yc
  · change a⁻¹ʳ*(w*c^4*(4:R)⁻¹ʳ+u*a^2*modelR c a b t)=
       a*(w*c^2*t^2*(4:R)⁻¹ʳ+u*modelR c a b t)
    have hy : a⁻¹ʳ*c^2=a*t^2 := by
      calc
        _ = (a⁻¹ʳ*c)*c := by ring
        _ = t*c := by unfold t cOverA;ring
        _ = _ := by rw [←yc];ring
    linear_combination w*c^2*(4:R)⁻¹ʳ*hy+u*a*modelR c a b t*hAI
  · change 1*(u*headK c b*(c-a))=a*(u*(headK c b*(t-1)))
    linear_combination -u*headK c b*yc
  · change a⁻¹ʳ*(u*a^2*modelQ c a b t)=a*(u*modelQ c a b t)
    linear_combination u*a*modelQ c a b t*hAI

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_center_first_mass
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_center_nullGain_unit
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.scaled_center_target

/- BUNDLE FrontObservers -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 400000

variable {R : Type*} [CommRing R]

theorem scalarL_center (c : R) (h2 : IsUnit (2:R)) : scalarL c c=0 := by
  unfold scalarL
  linear_combination -c^3*(Ring.mul_inverse_cancel _ h2)

theorem center_input_end (c a b w u : R) (h2 : IsUnit (2:R)) :
    wordLine c a b c w u 6=0 ∧ wordLine c a b c w u 7=0 := by
  constructor
  · change observerG c a c w u=0
    simp [observerG,scalarL_center c h2]
  · change observerZ c a b c w u=0
    simp [observerZ,scalarM]

theorem center_output_end (c a b w u : R) (hJ : IsUnit (jacobiJ c)) :
    targetLine c a b c w u 6=0 ∧ targetLine c a b c w u 7=0 := by
  have hp : casePZ c c=0 := by
    unfold casePZ
    rw [mul_assoc,mul_comm ((jacobiJ c)⁻¹ʳ),Ring.mul_inverse_cancel _ hJ,mul_one,sub_self]
  have hq : caseQZ c a b c=0 := by simp [caseQZ,basisQZ]
  have hT : targetZ c a b c w u=0 := by rw [targetZ,hp,hq,mul_zero,mul_zero,add_zero]
  constructor
  · change targetG c a b c w u=0
    simp [targetG,hT,observerZ,scalarM]
  · exact hT

theorem b_observer_G (c a b w u : R) (h2 : IsUnit (2:R)) (hb : IsUnit b)
    (hK : IsUnit (2*c-4*b))
    (hM : w*b^2=(-2-4*headK c b*(bOverA a b-1))*u) :
    observerG c a b w u=0 := by
  let s:=bOverA a b
  let t:=cOverA c a
  let k:=headK c b
  let m:=(-2)-4*k*(s-1)
  have hkc : (2*c-4*b)*k=c := by
    unfold k headK
    rw [mul_left_comm,Ring.mul_inverse_cancel _ hK,mul_one]
  have ht : c*s=b*t := by unfold s t bOverA cOverA;ring
  have hm : m*(2*b-c)+2*b*(2-t)=0 := by
    unfold m
    linear_combination 2*(s-1)*hkc+2*ht
  have hL : w*scalarL c b+(2-cOverA c a)*(b-c)*u=0 := by
    apply (h2.mul hb).mul_left_cancel
    rw [mul_zero]
    calc
      _ = (b-c)*((w*b^2)*(2*b-c)+2*b*(2-t)*u) := by
        change (2*b)*(w*scalarL c b+(2-t)*(b-c)*u)=_
        unfold scalarL
        linear_combination -w*b*(3*c*b^2-c^2*b)*(Ring.mul_inverse_cancel _ h2)
      _ = _ := by
        change w*b^2=m*u at hM
        rw [hM]
        linear_combination (b-c)*u*hm
  rw [observerG,hL,mul_zero]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

omit hp ha hb hRoot hOther in
theorem jacobi_center_paid : IsUnit (jacobiJ c) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  simp only [jacobiJ,map_add,map_sub,map_mul,map_pow,map_ofNat,hc]
  decide +kernel

theorem actual_b_gain :
    let x:=nodal c a b
    score x headB*b^2 =
      (-2-4*headK c b*(bOverA a b-1))*uAggregate x (actualScale x) headB := by
  let x:=nodal c a b
  obtain ⟨haU,hK,_⟩ := actual_head_denominator_units ρ c a b hc ha hb
  have hD : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hbC : IsUnit (b-c) :=
    hAll headB (Finset.mem_univ _) center (Finset.mem_univ _) (by decide +kernel)
  exact b_ratio_gain c a b _ _ haU hD hK hbC
    (actual_head_ratio ρ c a b hp hc ha hb hRoot hOther headB (Or.inl rfl))

omit hp hRoot hOther in
theorem actual_a_observers :
    wordInput c a b 1 6=0 ∧ wordInput c a b 1 7=0 := by
  let x:=nodal c a b
  have h2 := (standard_paid ρ).1
  have haU := (actual_head_denominator_units ρ c a b hc ha hb).1
  have hD : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hDen : IsUnit (Den ordinary x headA) :=
    den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) (by decide +kernel)
  have hA (k : Word) (hk : k≠0) :
      wordInput c a b 1 k=firstRatioFactor a k*(a*score x headA) :=
    input_a_factor c a b _ _ h2 haU hD (actual_first_u x hDen h2) hk
  exact ⟨(hA 6 (by decide +kernel)).trans (zero_mul _),
          (hA 7 (by decide +kernel)).trans (zero_mul _)⟩

theorem actual_b_observers :
    wordInput c a b 2 6=0 ∧ wordInput c a b 2 7=0 := by
  have h2 := (standard_paid ρ).1
  have hK := (actual_head_denominator_units ρ c a b hc ha hb).2.1
  have hbU : IsUnit b := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [hb];decide +kernel))
  exact ⟨b_observer_G c a b _ _ h2 hbU hK (actual_b_gain ρ c a b hp hc ha hb hRoot hOther),
    actual_singleton_Z_zero ρ c a b hp hc ha hb hRoot hOther headB (Or.inl rfl)⟩

theorem actual_Z_earliest (i : Fin 7) :
    wordInput c a b (Fin.castLE (by decide : 7≤11) i) 7=0 := by
  have h2 := (standard_paid ρ).1
  fin_cases i
  · exact input_at_endpoint c a b _ (by decide +kernel)
  · exact (actual_a_observers ρ c a b hc ha hb).2
  · exact (actual_b_observers ρ c a b hp hc ha hb hRoot hOther).2
  · exact (center_input_end c a b _ _ h2).2
  · exact (center_input_end c a b _ _ h2).2
  · exact actual_singleton_Z_zero ρ c a b hp hc ha hb hRoot hOther nodeD (Or.inr (Or.inl rfl))
  · exact actual_singleton_Z_zero ρ c a b hp hc ha hb hRoot hOther nodeE (Or.inr (Or.inr rfl))

theorem actual_G_earliest (i : Fin 6) :
    wordInput c a b (Fin.castLE (by decide : 6≤11) i) 6=0 := by
  have h2 := (standard_paid ρ).1
  fin_cases i
  · exact input_at_endpoint c a b _ (by decide +kernel)
  · exact (actual_a_observers ρ c a b hc ha hb).1
  · exact (actual_b_observers ρ c a b hp hc ha hb hRoot hOther).1
  · exact (center_input_end c a b _ _ h2).1
  · exact (center_input_end c a b _ _ h2).1
  · change observerG c a 26 _ _=0
    simp [observerG]

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_Z_earliest
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_G_earliest

/- BUNDLE CenterRows -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial PaidBarycentric
open RKResearch.Certified.ERK10CenterScalar (Chart)
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def scatterDonors (v : Fin 3→R) (j : Site) : R :=
  ∑ l : Fin 3, if donorSlot l=j then v l else 0

theorem scatter_read (v : Fin 3→R) (f : Site→R) :
    ∑ j : Site,scatterDonors v j*f j=∑ l : Fin 3,v l*f (donorSlot l) := by
  unfold scatterDonors
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [ite_mul]

theorem scatter_support (v : Fin 3→R) {i j : Site} (hi : i=3 ∨ i=4)
    (hs : i=3→v 2=0) (hij : i.val ≤ j.val) : scatterDonors v j=0 := by
  apply Finset.sum_eq_zero
  intro l _
  by_cases h : donorSlot l=j
  · rw [ite_eq_left h]
    have hh : l.val+1=j.val := congrArg Fin.val h
    have hL := l.isLt
    rcases hi with h3|h4
    · have hl : l=2 := by
        apply Fin.ext
        subst i
        change 3 ≤ j.val at hij
        change l.val=2
        omega
      rw [hl,hs h3]
    · subst i
      change 4 ≤ j.val at hij
      omega
  · rw [ite_eq_right h]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

omit hRoot hOther in
theorem actual_donor_unit (l : Fin 3) : IsUnit (rawU c a b (donorSlot l)) := by
  have hh : ρ (rawU c a b (donorSlot l))=Umod (donorSlot l) :=
    congrFun (actual_U_mod ρ c a b hp hc ha hb) _
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [hh]
  exact (show ∀ l : Fin 3,Umod (donorSlot l)≠0 from by decide +kernel) l

theorem actual_donor_modes (l : Fin 3) (j : Fin 5) :
    wScale a j*wordInput c a b (donorSlot l) (positiveWord j) =
      rawU c a b (donorSlot l)*(centerChart c a b).donors l j := by
  let x:=nodal c a b
  let X:=centerChart c a b
  have H := center_chart_paid ρ c a b hc ha hb
  have h2 := (standard_paid ρ).1
  have haU := (actual_head_denominator_units ρ c a b hc ha hb).1
  have hD : IsUnit (Den ordinary x headA) :=
    den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) (by decide +kernel)
  have hA : rawU c a b 1*(-2)=rawW c a b 1*a^2 := by
    change uAggregate x (actualScale x) headA*(-2)=score x headA*a^2
    have hh := actual_first_u x hD h2
    change score x headA*a^2+2*uAggregate x (actualScale x) headA=0 at hh
    linear_combination -hh
  have hB : rawU c a b 2*X.Rb=rawW c a b 2*b^2 := by
    have h := actual_b_gain ρ c a b hp hc ha hb hRoot hOther
    change rawW c a b 2*b^2=X.Rb*rawU c a b 2 at h
    rw [mul_comm,h.symm]
  have hcM : rawU c a b 3*X.L=rawW c a b 3*c^2 := by
    rw [mul_comm,actual_center_first_mass ρ c a b hc ha hb]
  have hs : a*X.s=b := by
    change a*(b*a⁻¹ʳ)=b
    rw [mul_left_comm,Ring.mul_inverse_cancel _ haU,mul_one]
  have ht : a*X.t=c := by
    change a*(c*a⁻¹ʳ)=c
    rw [mul_left_comm,Ring.mul_inverse_cancel _ haU,mul_one]
  fin_cases l
  · have hh : donorMode (-2:R) 1 1 = X.donors 0 := by
      funext i
      fin_cases i <;> simp [donorMode,Chart.donors]
    change wScale a j*wordLine c a b a (rawW c a b 1) (rawU c a b 1) (positiveWord j) =
      rawU c a b 1*X.donors 0 j
    rw [←hh]
    exact scaled_word_donor c a b a _ _ (-2) 1 1 haU (mul_one _) (one_mul _) hA j
  · have hh : donorMode X.Rb X.s X.iS = X.donors 1 := rfl
    change wScale a j*wordLine c a b b (rawW c a b 2) (rawU c a b 2) (positiveWord j) =
      rawU c a b 2*X.donors 1 j
    rw [←hh]
    exact scaled_word_donor c a b b _ _ X.Rb X.s X.iS haU hs H.aS hB j
  · have hh : donorMode X.L X.t X.iT = X.donors 2 := rfl
    change wScale a j*wordLine c a b c (rawW c a b 3) (rawU c a b 3) (positiveWord j) =
      rawU c a b 3*X.donors 2 j
    rw [←hh]
    exact scaled_word_donor c a b c _ _ X.L X.t X.iT haU ht H.aT hcM j

/-- Both center rows, including their overdetermined positive and
terminal observer columns, on the actual paid physical schedule. -/
theorem actualK_center (i : Site) (hi : i=3 ∨ i=4) (k : Word) :
    ∑ j : Site,actualK c a b i j*wordInput c a b j k=wordTarget c a b i k := by
  let X:=centerChart c a b
  let M:=rawW c a b i*c^2
  let U:=rawU c a b i
  let lam:=X.taps M U X.G⁻¹ʳ
  let V : Fin 3→R := fun l => a*lam l*(rawU c a b (donorSlot l))⁻¹ʳ
  have h0 : 0 < i.val := by rcases hi with rfl|rfl <;> decide +kernel
  have h8 : i.val < 8 := by rcases hi with rfl|rfl <;> decide +kernel
  have hy : rawY c a b i=c := by rcases hi with rfl|rfl <;> rfl
  have haU := (actual_head_denominator_units ρ c a b hc ha hb).1
  have hg := actual_center_nullGain_unit ρ c a b hc ha hb
  apply actualK_early_from_positive ρ c a b hp hc ha hb i h0 h8 (scatterDonors V) ?_ ?_ k
  · intro j hj
    apply scatter_support V hi _ hj
    intro hi3
    have hM : M=X.L*U := by
      subst i
      exact actual_center_first_mass ρ c a b hc ha hb
    have vv : lam 2=0 := by
      change X.scale M U X.G⁻¹ʳ*(X.s-1)=0
      simp [Chart.scale,hM]
    change a*lam 2*(rawU c a b (donorSlot 2))⁻¹ʳ=0
    rw [vv,mul_zero,zero_mul]
  · intro q hq
    rw [scatter_read]
    by_cases hq5 : q.val ≤ 5
    · have hq0 : 0 < q.val := Nat.pos_of_ne_zero (fun h => hq (Fin.ext h))
      let j : Fin 5 := ⟨q.val-1,by omega⟩
      have hEq : positiveWord j=q := by apply Fin.ext;change q.val-1+1=q.val;omega
      rw [←hEq]
      apply (wScale_unit haU j).mul_left_cancel
      have hP (l : Fin 3) :
          wScale a j*(V l*wordInput c a b (donorSlot l) (positiveWord j)) =
             a*(lam l*X.donors l j) := by
        let u:=rawU c a b (donorSlot l)
        have ht : wScale a j*wordInput c a b (donorSlot l) (positiveWord j)=u*(X.donors l j) :=
          actual_donor_modes ρ c a b hp hc ha hb hRoot hOther l j
        calc
          _ = a*lam l*u⁻¹ʳ*(wScale a j*wordInput c a b (donorSlot l) (positiveWord j)) := by unfold V;ring
          _ = _ := by
            rw [ht]
            have hu : u*u⁻¹ʳ=1 := Ring.mul_inverse_cancel _ (actual_donor_unit ρ c a b hp hc ha hb l)
            linear_combination a*(lam l)*(X.donors l j)*hu
      simp_rw [Finset.mul_sum,hP]
      rw [←Finset.mul_sum,
        show (∑ l : Fin 3,lam l*X.donors l j)=X.target M U j from
          X.second_center_reads (center_chart_paid ρ c a b hc ha hb) M U X.G⁻¹ʳ
            (Ring.mul_inverse_cancel _ hg) j]
      change a*X.target M U j=wScale a j*targetLine c a b (rawY c a b i)
        (rawW c a b i) (rawU c a b i) (positiveWord j)
      rw [hy]
      exact (scaled_center_target c a b _ _ haU j).symm
    · have hObs : q=6 ∨ q=7 := by
        have qLt := q.isLt
        have hqr : q.val=6 ∨ q.val=7 := by omega
        exact hqr.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
      have HT := center_output_end c a b (rawW c a b i) (rawU c a b i) (jacobi_center_paid ρ c hc)
      rcases hObs with rfl|rfl
      · have hh : wordTarget c a b i 6=0 := by unfold wordTarget;rw [hy];exact HT.1
        rw [hh]
        apply Finset.sum_eq_zero
        intro l _
        have z : wordInput c a b (donorSlot l) 6=0 :=
          actual_G_earliest ρ c a b hp hc ha hb hRoot hOther ⟨(donorSlot l).val,by
            have h:=l.isLt;change l.val+1 < 6;omega⟩
        rw [z,mul_zero]
      · have hh : wordTarget c a b i 7=0 := by unfold wordTarget;rw [hy];exact HT.2
        rw [hh]
        apply Finset.sum_eq_zero
        intro l _
        have z : wordInput c a b (donorSlot l) 7=0 :=
          actual_Z_earliest ρ c a b hp hc ha hb hRoot hOther ⟨(donorSlot l).val,by
            have h:=l.isLt;change l.val+1 < 7;omega⟩
        rw [z,mul_zero]

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_center
