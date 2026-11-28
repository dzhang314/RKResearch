module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordTarget
public import RKCert.ReviewedNative.ERK10FixedQ29AdicHeadBiChecks

@[expose] public section

/- HeadRatioVal: the complete paid earlier word adapter. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open PaidBarycentric Nonlinear Packed Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 220000

variable {R : Type*} [CommRing R]

def nNum (c a b y : R) : R := 2*a*b*c+2*(-2*a*b+a*c+b*c-c^2)*y

def ratioCross (c a b y : R) : R :=
  2*(a-1)*(a*(2*b-c))*((actualMu c).eval y*y*(y-15)*(y-c))+
  (y-1)*nNum c a b y*((actualMu c).eval a*a*(a-15))

namespace HeadBi

@[simp] theorem val_scale (c a : R) (f : Form) (p : Bi) :
    (scale f p).val c a=f.val c*p.val c a := by
  simp only [scale,Bi.val,Form.val_mul]
  ring

variable (c a : R)
variable (hQ : a^2-repS.val c*a+repQ.val c=0)
include hQ

theorem val_shift_diff (f : Form) (p : Bi) :
    (shiftDiffB f p).val c a=(repS.val c-a-f.val c)*p.val c a := by
  rw [shiftDiffB,val_sub,val_shiftB c a hQ,val_scale]
  ring

theorem val_firstFactor :
    firstFactor.val c a=2*(a-1)*(a*(2*(repS.val c-a)-c)) := by
  simp only [firstFactor,Bi.val,Form.val_mul,Form.val_sub,cForm_val,Form.val,
    qForm,sForm]
  linear_combination 2*(c-2+2*a)*hQ

theorem val_muFactor (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) :
    muFactor.val c a=(actualMu c).eval a*a*(a-15) := by
  rw [muFactor,val_mul c a hQ,muA_val c a hQ ρ hp hc]
  simp only [Bi.val,Form.val_sub,qForm,sForm,Form.val]
  linear_combination -((actualMu c).eval a)*hQ

theorem val_nNum (y : R) :
    headN0.val c+headN1.val c*y=nNum c a (repS.val c-a) y := by
  have h : repQ.val c=a*(repS.val c-a) := by linear_combination hQ
  simp only [headN0,headN1,qForm,sForm,Form.val_mul,Form.val_sub,cForm_val,Form.val]
  rw [h,nNum]
  ring

omit hQ in
private theorem reassoc_ratio (p b c m n0 n1 u : R) :
    p*((b-c)*((b-15)*(b*m)))+n0*((b-1)*u)+n1*(b*((b-1)*u)) =
      p*(m*b*(b-15)*(b-c))+(b-1)*(n0+n1*b)*u := by ring

theorem val_ratioOne (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) (y : Form) :
    (ratioOne y).val c a=ratioCross c a (repS.val c-a) (y.val c) := by
  have h1 : (1:Form).val c=(1:R) := by change ((1:ℤ):R)=1; simp
  have h15 : (15:Form).val c=(15:R) := by change ((15:ℤ):R)=15; norm_num
  simp only [ratioOne,val_add,val_scale,Form.val_mul,Form.val_add,Form.val_sub,
    h1,h15,cForm_val,exactMuF ρ c hp hc,val_firstFactor c a hQ,val_muFactor c a hQ ρ hp hc,
    val_nNum c a hQ,ratioCross,actualMu_eval]
  congr 1
  exact mul_comm _ _

theorem val_ratioB (ρ : R→+*F) [IsLocalHom ρ]
    (hp : (decic R).eval c=0) (hc : ρ c=2) :
    ratioB.val c a=ratioCross c a (repS.val c-a) (repS.val c-a) := by
  have h1 : (1:Form).val c=(1:R) := by change ((1:ℤ):R)=1; simp
  have h15 : (15:Form).val c=(15:R) := by change ((15:ℤ):R)=15; norm_num
  simp only [ratioB,val_add,val_mul c a hQ,val_shiftB c a hQ,val_shift_diff c a hQ,
    val_scale,cForm_val,h1,h15,val_firstFactor c a hQ,muB_val c a hQ ρ hp hc,
    val_muFactor c a hQ ρ hp hc,ratioCross]
  rw [←val_nNum c a hQ (repS.val c-a)]
  exact reassoc_ratio _ _ _ _ _ _ _

end HeadBi

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical


/- HeadRatioCross: the complete paid earlier word adapter. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open PaidBarycentric Nonlinear Packed Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 220000

variable {R : Type*} [CommRing R]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

omit ha hb in
theorem actual_cross (i : Site) (hi : i=headB ∨ i=nodeD ∨ i=nodeE) :
    ratioCross c a b (nodal c a b i)=0 := by
  have hq : a^2-repS.val c*a+repQ.val c=0 := by
    rw [exactS ρ c hp hc,exactQ ρ c hp hc]
    simpa only [headQuadratic,eval_add,eval_sub,eval_pow,eval_X,eval_C,eval_mul] using hRoot
  have hbEq : repS.val c-a=b := by rw [exactS ρ c hp hc,←hOther]
  obtain he | he | he := hi
  · subst i
    have hh := HeadBi.guarded_sound c a ρ hp HeadBi.cert_ratioB
    rw [HeadBi.val_ratioB c a hq ρ hp hc,hbEq] at hh
    exact hh
  · subst i
    have hh := HeadBi.guarded_sound c a ρ hp HeadBi.cert_ratioD
    rw [HeadBi.ratioD,HeadBi.val_ratioOne c a hq ρ hp hc,hbEq,Form.val_nat] at hh
    exact hh
  · subst i
    have hh := HeadBi.guarded_sound c a ρ hp HeadBi.cert_ratioE
    rw [HeadBi.ratioE,HeadBi.val_ratioOne c a hq ρ hp hc,hbEq] at hh
    simp only [Form.val,exactE ρ c hp hc] at hh
    exact hh

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_cross


/- HeadRatio: the complete paid earlier word adapter. -/
namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open PaidBarycentric Nonlinear Packed Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 220000

variable {R : Type*} [CommRing R]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

omit ρ hp hc ha hb hRoot hOther in
theorem link_dens {i : Site} (hi : i∈singletonSites) :
    (nodal c a b i)*(nodal c a b i-1)*Den ordinary (nodal c a b) i =
      (nodal c a b i-15)*Den cardSites (nodal c a b) i := by
  rw [den_ord_single c a b hi,den_card_single c a b hi]
  ring

omit ρ hp hc ha hb hRoot hOther in
theorem scaled_N (y : R) (haU : IsUnit a) (hd : IsUnit (2*b-c)) :
    (a*(2*b-c))*headN c a b y = nNum c a b y := by
  calc
    _ = (2*a*b*c)*((2*b-c)*(2*b-c)⁻¹ʳ)+
        (2*(-2*a*b+a*c+b*c-c^2)*y)*((a*(2*b-c))*(a*(2*b-c))⁻¹ʳ) := by
      unfold headN;ring
    _ = _ := by rw [Ring.mul_inverse_cancel _ hd,Ring.mul_inverse_cancel _ (haU.mul hd),mul_one,mul_one,nNum]

/-- A checked bivariate ratio at the actual cardinal/cofactor site,
with the actual physical denominators all paid by the local residue map. -/
theorem actual_head_ratio (i : Site) (hi : i=headB ∨ i=nodeD ∨ i=nodeE) :
    let x:=nodal c a b
    score x i*(x i)^2*(x i-c)=headN c a b (x i)*uAggregate x (actualScale x) i := by
  let x:=nodal c a b
  let z:=x i
  let S:=actualScale x
  let D:=Den ordinary x i
  let N:=headN c a b z
  let P:=2*(a-1)*(a*(2*b-c))
  have hs : i∈singletonSites := by rcases hi with rfl|rfl|rfl <;> decide +kernel
  have haS : headA∈singletonSites := by decide +kernel
  have h2 : IsUnit (2:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have haU : IsUnit a := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [ha];decide +kernel))
  have hDb : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have h1z : IsUnit (z-1) :=
    hAll i (Finset.mem_univ _) oldOrigin (Finset.mem_univ _) (singleton_flags i hs).2.1
  have h1a : IsUnit (a-1) :=
    hAll headA (Finset.mem_univ _) oldOrigin (Finset.mem_univ _) (by decide +kernel)
  obtain ⟨_,_,_,_,_,hiO,_⟩ := singleton_flags i hs
  have hD : IsUnit D := den_unit (actual_paid_sites ρ c a b hc ha hb ordinary) hiO
  have hP : IsUnit P := ((h2.mul h1a).mul (haU.mul hDb))
  have hCard (j : Site) (hj : j∈singletonSites) :
      Den cardSites x j*score x j=(actualMu c).eval (x j) := by
    obtain ⟨_,_,_,hh,hjC,_,_⟩ := singleton_flags j hj
    rw [score,ite_eq_right hh,den_mul_cardinal (den_unit (actual_paid_sites ρ c a b hc ha hb cardSites) hjC),
      true_cardinal_numerator hRoot hOther hj]
  have haLink : a*(a-1)*Den ordinary x headA=(a-15)*Den cardSites x headA :=
    link_dens c a b haS
  have haCard : Den cardSites x headA*score x headA=(actualMu c).eval a := hCard _ haS
  have hScale : (2*(a-1))*S=-((actualMu c).eval a*a*(a-15)) := by
    calc
      _ = -((2:R)*(2:R)⁻¹ʳ)*
          (a*score x headA*(a*(a-1)*Den ordinary x headA)) := by
        change (2*(a-1))*actualScale x=_
        unfold actualScale
        change (2*(a-1))*(-(score x headA*a^2*Den ordinary x headA)*(2:R)⁻¹ʳ)=_
        ring
      _ = _ := by
        rw [Ring.mul_inverse_cancel _ h2,haLink]
        linear_combination -a*(a-15)*haCard
  have hL : ((z-1)*D)*(score x i*z^2*(z-c)) =
      (actualMu c).eval z*z*(z-15)*(z-c) := by
    have hLink : z*(z-1)*D=(z-15)*Den cardSites x i := link_dens c a b hs
    calc
      _ = (z*(z-1)*D)*(score x i*z*(z-c)) := by ring
      _ = _ := by rw [hLink];linear_combination (z-15)*z*(z-c)*(hCard i hs)
  have hR : ((z-1)*D)*(N*uAggregate x S i)=(z-1)*N*S := by
    unfold uAggregate ordInv
    calc
      _ = (D*D⁻¹ʳ)*((z-1)*N*S) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hD,one_mul]
  have hcross : ratioCross c a b z=0 := actual_cross ρ c a b hp hc hRoot hOther i hi
  have hRight : P*((z-1)*N*S) =
      -((z-1)*nNum c a b z*((actualMu c).eval a*a*(a-15))) := by
    calc
      _ = (z-1)*((a*(2*b-c))*N)*((2*(a-1))*S) := by unfold P;ring
      _ = _ := by rw [show (a*(2*b-c))*N=nNum c a b z from scaled_N c a b z haU hDb,hScale,mul_neg]
  change score x i*z^2*(z-c)=N*uAggregate x S i
  apply (hP.mul (h1z.mul hD)).mul_left_cancel
  calc
    _ = P*((actualMu c).eval z*z*(z-15)*(z-c)) := by linear_combination P*hL
    _ = P*((z-1)*N*S) := by
      rw [hRight]
      exact eq_neg_of_add_eq_zero_left hcross
    _ = _ := by linear_combination -P*hR

theorem actual_singleton_Z_zero (i : Site) (hi : i=headB ∨ i=nodeD ∨ i=nodeE) :
    let x:=nodal c a b
    observerZ c a b (x i) (score x i) (uAggregate x (actualScale x) i)=0 := by
  unfold observerZ scalarM
  exact (by
    have H := actual_head_ratio ρ c a b hp hc ha hb hRoot hOther i hi
    dsimp only at H
    linear_combination (nodal c a b i-c)*H)

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_head_ratio
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_singleton_Z_zero
