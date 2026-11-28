module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailRead
public import RKCert.ReviewedNative.ERK10FixedQ29AdicCardinals
public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordD
public import Mathlib.Algebra.Ring.GrindInstances

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail
open Packed Nonlinear Polynomial PaidBarycentric
open RKCert.ReviewedNative.IntegerHornerCertificate (horner coeval coeval_cons)
open scoped Polynomial BigOperators

noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def packCore (r : ERK10ZTailCore.Rep) : Packed.Rep := ⟨r.nums,r.den⟩

def repV0 := packCore ERK10ZTailCore.v0
def repV1 := packCore ERK10ZTailCore.v1
def repV2 := packCore ERK10ZTailCore.v2
def repQuot0 := packCore ERK10ZTailCore.q0
def repQuot1 := packCore ERK10ZTailCore.q1
def repQuot2 := packCore ERK10ZTailCore.q2
def repQuot3 := packCore ERK10ZTailCore.q3
def repSigma := packCore ERK10ZTailCore.sigma

def J (y : R) : R := y-14*y^2+56*y^3-84*y^4+42*y^5
def P (c : R) : Polynomial R := fromCoeffs [0,-c^5,14*c^5,
  10*c^2*J c-56*c^5,-15*c*J c+84*c^5,6*J c-42*c^5]

def N (c : R) : Polynomial R := fromCoeffs [2*headProduct c*c,
    2*(-2*headProduct c+c*headSum c-c^2)]
def V (c : R) : Polynomial R := fromCoeffs [repV0.val c,repV1.val c,repV2.val c]
def Q (c : R) : Polynomial R := fromCoeffs [repQuot0.val c,repQuot1.val c,repQuot2.val c,repQuot3.val c]
def scaleZ (c : R) : R := repSigma.val c

def D3 (c : R) : Polynomial R := fromCoeffs [headProduct c,-headSum c,1]*(X-C 26)
def residual (c : R) : Polynomial R :=
  X^2*(X-C c)^2*V c+N c*P c-D3 c*Q c

theorem p_eval (c y : R) :
    (P c).eval y=J c*(6*y^5-15*c*y^4+10*c^2*y^3)-c^5*J y := by
  simp only [P,fromCoeffs_eval,horner]
  unfold J
  ring

theorem n_eval (c y : R) :
    (N c).eval y=2*headProduct c*c+2*(-2*headProduct c+c*headSum c-c^2)*y := by
  simp only [N,fromCoeffs_eval,horner,add_zero,mul_zero]
  ring

theorem v_eval (c y : R) :
    (V c).eval y=repV0.val c+repV1.val c*y+repV2.val c*y^2 := by
  simp only [V,fromCoeffs_eval,horner]
  ring

theorem q_eval (c y : R) :
    (Q c).eval y=repQuot0.val c+repQuot1.val c*y+repQuot2.val c*y^2+repQuot3.val c*y^3 := by
  simp only [Q,fromCoeffs_eval,horner]
  ring

theorem d_eval (c y : R) :
    (D3 c).eval y=(y^2-headSum c*y+headProduct c)*(y-26) := by
  simp only [D3,eval_mul,eval_sub,eval_X,eval_C,fromCoeffs_eval,horner]
  ring

theorem residual_degree (c : R) : (residual c).natDegree≤6 := by
  have hP : (P c).natDegree≤5 := natDegree_fromCoeffs _
  have hN : (N c).natDegree≤1 := natDegree_fromCoeffs _
  have hV : (V c).natDegree≤2 := natDegree_fromCoeffs _
  have hQ : (Q c).natDegree≤3 := natDegree_fromCoeffs _
  have hD0 : (fromCoeffs [headProduct c,-headSum c,1]).natDegree≤2 :=
    natDegree_fromCoeffs _
  have hX (z : R) : (X-C z).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le natDegree_X_le (by simp))
  have hD : (D3 c).natDegree≤3 := (natDegree_mul_le ..).trans (Nat.add_le_add hD0 (hX _))
  have hXX : ((X-C c)^2).natDegree≤2 := by
    rw [pow_two]
    exact (natDegree_mul_le ..).trans (Nat.add_le_add (hX c) (hX c))
  have hV0 : ((X : Polynomial R)^2*(X-C c)^2).natDegree≤4 :=
    (natDegree_mul_le ..).trans (Nat.add_le_add (natDegree_X_pow_le _) hXX)
  unfold residual
  exact (natDegree_sub_le ..).trans (max_le
    ((natDegree_add_le ..).trans (max_le
      ((natDegree_mul_le ..).trans (Nat.add_le_add hV0 hV))
      ((natDegree_mul_le ..).trans (Nat.add_le_add hN hP))))
    ((natDegree_mul_le ..).trans (Nat.add_le_add hD hQ)))

/-- Bridge the stock ring's Horner evaluation to the existing actual
packed polynomial evaluation, with the operations supplied by Mathlib. -/
theorem evalI_coeval (x : R) (as : List ℤ) :
    ERK10ZTailCore.evalI x as = coeval as x := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [ERK10ZTailCore.evalI,coeval_cons,ih]

theorem of_mod_notZero (n : ℕ) (h : n%29 != 0) : Packed.Paid n := by
  intro hd
  have he := Nat.mod_eq_zero_of_dvd hd
  simp [he] at h

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c : R) (hp : (decic R).eval c=0) (hc : ρ c=2)

/-- Actual paid literals in the same local ring as the decic root.
All denominator algebra is provided by the portable readout. -/
def coreContext : ERK10ZTailCore.ReadContext c where
  root := by
    rw [evalI_coeval]
    change coeval decicCoeffs c=0
    exact Packed.root_coeval hp
  leading_paid := by
    have h := Packed.paid_unit ρ
      (of_mod_notZero _ ERK10ZTailCore.leading_mod_ne)
    refine ⟨(Ring.inverse (ERK10ZTailCore.leading:R)),?_⟩
    rw [mul_comm,Ring.mul_inverse_cancel _ h]
  inverse := fun n => Ring.inverse (n:R)
  literal_paid := by
    intro p hi
    have h := Packed.paid_unit ρ
      (of_mod_notZero _ (ERK10ZTailCore.slot_mod_ne hi))
    rw [mul_comm,Ring.mul_inverse_cancel _ h]

theorem core_value (p : ERK10ZTailCore.Rep) :
    (coreContext ρ c hp).value p=(packCore p).val c := by
  change Ring.inverse (p.den:R) * ERK10ZTailCore.evalI c p.nums = _
  rw [evalI_coeval,packCore,Packed.Rep.val]
  exact mul_comm _ _

theorem core_p (y : R) : ERK10ZTailCore.pReal c y=(P c).eval y := by
  rw [p_eval]
  unfold ERK10ZTailCore.pReal ERK10ZTailCore.jacReal J
  ring

include hc in
theorem core_n (y : R) :
    ERK10ZTailCore.nReal (coreContext ρ c hp) y=(N c).eval y := by
  unfold ERK10ZTailCore.nReal
  rw [n_eval,core_value,core_value]
  change 2*repQ.val c*c+2*((-2)*repQ.val c+c*repS.val c-c^2)*y=_
  rw [exactS ρ c hp hc,exactQ ρ c hp hc]

include hc in
theorem core_d (y : R) :
    ERK10ZTailCore.dReal (coreContext ρ c hp) y=(D3 c).eval y := by
  unfold ERK10ZTailCore.dReal
  rw [d_eval,core_value,core_value]
  change (y^2-repS.val c*y+repQ.val c)*(y-26)=_
  rw [exactS ρ c hp hc,exactQ ρ c hp hc]

theorem core_v (y : R) :
    ERK10ZTailCore.vReal (coreContext ρ c hp) y=(V c).eval y := by
  rw [v_eval]
  simp only [ERK10ZTailCore.vReal,ERK10ZTailCore.evalReal,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,core_value,repV0,repV1,repV2]
  ring

theorem core_q (y : R) :
    ERK10ZTailCore.qReal (coreContext ρ c hp) y=(Q c).eval y := by
  rw [q_eval]
  simp only [ERK10ZTailCore.qReal,ERK10ZTailCore.evalReal,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,core_value,repQuot0,repQuot1,repQuot2,repQuot3]
  ring

theorem core_sigma : (coreContext ρ c hp).value ERK10ZTailCore.sigma=scaleZ c :=
  core_value ρ c hp _

include hc in
theorem core_mu (y : R) :
    ERK10ZTailCore.muReal (coreContext ρ c hp) y=(actualMu c).eval y := by
  have h0 : (coreContext ρ c hp).value ERK10ZTailCore.mu0=muCoeff c 0 := by
    rw [core_value]
    exact exactMu ρ c hp hc 0 (by decide)
  have h1 : (coreContext ρ c hp).value ERK10ZTailCore.mu1=muCoeff c 1 := by
    rw [core_value]
    exact exactMu ρ c hp hc 1 (by decide)
  have h2 : (coreContext ρ c hp).value ERK10ZTailCore.mu2=muCoeff c 2 := by
    rw [core_value]
    exact exactMu ρ c hp hc 2 (by decide)
  have h3 : (coreContext ρ c hp).value ERK10ZTailCore.mu3=muCoeff c 3 := by
    rw [core_value]
    exact exactMu ρ c hp hc 3 (by decide)
  have h4 : (coreContext ρ c hp).value ERK10ZTailCore.mu4=muCoeff c 4 := by
    rw [core_value]
    exact exactMu ρ c hp hc 4 (by decide)
  have h5 : (coreContext ρ c hp).value ERK10ZTailCore.mu5=muCoeff c 5 := by
    rw [core_value]
    exact exactMu ρ c hp hc 5 (by decide)
  have h6 : (coreContext ρ c hp).value ERK10ZTailCore.mu6=muCoeff c 6 := by
    rw [core_value]
    exact exactMu ρ c hp hc 6 (by decide)
  rw [actualMu_eval,muValue]
  simp only [ERK10ZTailCore.muReal,ERK10ZTailCore.evalReal,List.map_cons,List.map_nil,
    List.foldr_cons,List.foldr_nil,h0,h1,h2,h3,h4,h5,h6,Fin.sum_univ_succ,
    Fin.sum_univ_zero,Fin.val_succ,Fin.val_zero]
  ring

include hc in
theorem core_e : (coreContext ρ c hp).value ERK10ZTailCore.E=eTail c := by
  rw [core_value]
  exact exactE ρ c hp hc

include hc in
theorem core_f : (coreContext ρ c hp).value ERK10ZTailCore.F=fTail c := by
  rw [core_value]
  exact exactF ρ c hp hc

include hc in
theorem core_residual (y : R) :
    ERK10ZTailCore.evalDiv (coreContext ρ c hp) y=(residual c).eval y := by
  simp only [ERK10ZTailCore.evalDiv,core_p,core_n ρ c hp hc,core_d ρ c hp hc,
    core_v,core_q,residual,eval_pow,eval_mul,eval_add,eval_sub,eval_X,eval_C]

include ρ hp hc in
/-- Actual exact quotient, via the portable seven readouts and the
existing paid-ring interpolation lemma. -/
theorem actual_quotient :
    (X^2*(X-C c)^2)*V c+N c*P c=D3 c*Q c := by
  apply sub_eq_zero.mp
  change residual c=0
  letI : Nontrivial R := ρ.domain_nontrivial
  let u : Fin 7→R := fun i => i.val
  have hPay : PaidBarycentric.Paid (Finset.univ : Finset (Fin 7)) u := by
    intro i _ j _ hij
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    simp only [u,map_sub,map_natCast]
    exact (show ∀ i j : Fin 7,i≠j→(i.val:F)-(j.val:F)≠0 from by decide +kernel) i j hij
  have hs (i : Fin 7) : (residual c).eval (u i)=0 := by
    rw [←core_residual ρ c hp hc]
    exact ERK10ZTailCore.div_seven_read (coreContext ρ c hp) i
  have I := interp hPay (residual c) (by simpa using (residual_degree c).trans_lt (by decide : 6<7))
  rw [←I]
  simp only [hs,map_zero,zero_mul,Finset.sum_const_zero]

include ρ hp hc in
theorem actual_scale_read :
    (26-1)*(N c).eval 26*scaleZ c=(actualMu c).eval 26*26*(26-15)*(26-c) := by
  apply sub_eq_zero.mp
  have H := ERK10ZTailCore.scale_read_sound (coreContext ρ c hp)
  simpa only [ERK10ZTailCore.evalScale,core_n ρ c hp hc,core_sigma,core_mu ρ c hp hc] using H

include ρ hp hc in
theorem actual_output_e :
    (actualMu c).eval (eTail c)*(eTail c-15)*(P c).eval (eTail c)+
    (eTail c-1)*(eTail c)*scaleZ c*(eTail c-c)*(V c).eval (eTail c)=0 := by
  have H := (ERK10ZTailCore.out_e_f_read (coreContext ρ c hp)).1
  simpa only [ERK10ZTailCore.evalOut,core_e ρ c hp hc,core_mu ρ c hp hc,
    core_p,core_sigma,core_v] using H

include ρ hp hc in
theorem actual_output_f :
    (actualMu c).eval (fTail c)*(fTail c-15)*(P c).eval (fTail c)+
    (fTail c-1)*(fTail c)*scaleZ c*(fTail c-c)*(V c).eval (fTail c)=0 := by
  have H := (ERK10ZTailCore.out_e_f_read (coreContext ρ c hp)).2
  simpa only [ERK10ZTailCore.evalOut,core_f ρ c hp hc,core_mu ρ c hp hc,
    core_p,core_sigma,core_v] using H

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail.actual_quotient
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail.actual_scale_read
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail.actual_output_e
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail.actual_output_f
