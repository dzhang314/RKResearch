module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicZTailActual
public import RKCert.ReviewedNative.ERK10FixedQ29AdicWordD

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail
open Nonlinear Polynomial PaidBarycentric
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def pScale (c : R) : R := 30*jacobiJ c
def nScale (c a b : R) : R := a*(2*b-c)

theorem scaled_PZ (c y : R) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R))
    (h5 : IsUnit (5:R)) (hJ : IsUnit (jacobiJ c)) :
    pScale c*casePZ c y=(P c).eval y := by
  have hM (z : R) : (30:R)*antiderivativeM c z=6*z^5-15*c*z^4+10*c^2*z^3 := by
    unfold antiderivativeM
    linear_combination 6*z^5*(Ring.mul_inverse_cancel _ h5)-
      15*c*z^4*(Ring.mul_inverse_cancel _ h2)+10*c^2*z^3*(Ring.mul_inverse_cancel _ h3)
  have hcM : (30:R)*antiderivativeM c c=c^5 := by rw [hM];ring
  rw [p_eval]
  change pScale c*casePZ c y=jacobiJ c*(6*y^5-15*c*y^4+10*c^2*y^3)-c^5*jacobiJ y
  calc
    _ = jacobiJ c*(30*antiderivativeM c y)-
        (jacobiJ c*(jacobiJ c)⁻¹ʳ)*(30*antiderivativeM c c)*jacobiJ y := by
       unfold pScale casePZ;ring
    _ = _ := by rw [hM,hcM,Ring.mul_inverse_cancel _ hJ,one_mul]

theorem nFlat_true (c a b y : R) (hA : (headQuadratic c).eval a=0)
    (hB : b=headSum c-a) :
    (N c).eval y=nNum c a b y := by
  have hs : a+b=headSum c := by rw [hB];ring
  have hq : a*b=headProduct c := by
    rw [eval_headQuadratic] at hA
    rw [hB]
    linear_combination -hA
  rw [n_eval,←hq,←hs]
  unfold nNum
  ring

def threeNodes (a b : R) : Fin 3→R := ![a,b,26]
def basis2 (z t u y : R) : R := (y-t)*(y-u)*((z-t)*(z-u))⁻¹ʳ

theorem interp_three [Nontrivial R] (a b y : R) (f : Polynomial R)
    (hP : Paid (Finset.univ : Finset (Fin 3)) (threeNodes a b))
    (hd : f.natDegree≤2) :
    f.eval y=f.eval a*basis2 a b 26 y+f.eval b*basis2 b a 26 y+f.eval 26*basis2 26 a b y := by
  have hI := (congrArg (fun p : Polynomial R => p.eval y)
    (interp hP f (by simpa using (hd.trans_lt (by decide : 2<3))))).symm
  simp only [eval_finsetSum,eval_mul,eval_C] at hI
  have h0 : ((Finset.univ : Finset (Fin 3)).erase 0)={1,2} := by decide +kernel
  have h1 : ((Finset.univ : Finset (Fin 3)).erase 1)={0,2} := by decide +kernel
  have h2 : ((Finset.univ : Finset (Fin 3)).erase 2)={0,1} := by decide +kernel
  have E0 : (basis Finset.univ (threeNodes a b) 0).eval y=basis2 a b 26 y := by
    rw [basis,eval_mul,eval_C,eval_rootPoly,Den,h0,
      Finset.prod_insert (by decide +kernel),Finset.prod_insert (by decide +kernel),
      Finset.prod_singleton,Finset.prod_singleton]
    change Ring.inverse ((a-b)*(a-26))*((y-b)*(y-26))=
      (y-b)*(y-26)*Ring.inverse ((a-b)*(a-26))
    exact mul_comm _ _
  have E1 : (basis Finset.univ (threeNodes a b) 1).eval y=basis2 b a 26 y := by
    rw [basis,eval_mul,eval_C,eval_rootPoly,Den,h1,
      Finset.prod_insert (by decide +kernel),Finset.prod_insert (by decide +kernel),
      Finset.prod_singleton,Finset.prod_singleton]
    change Ring.inverse ((b-a)*(b-26))*((y-a)*(y-26))=
      (y-a)*(y-26)*Ring.inverse ((b-a)*(b-26))
    exact mul_comm _ _
  have E2 : (basis Finset.univ (threeNodes a b) 2).eval y=basis2 26 a b y := by
    rw [basis,eval_mul,eval_C,eval_rootPoly,Den,h2,
      Finset.prod_insert (by decide +kernel),Finset.prod_insert (by decide +kernel),
      Finset.prod_singleton,Finset.prod_singleton]
    change Ring.inverse ((26-a)*(26-b))*((y-a)*(y-b))=
      (y-a)*(y-b)*Ring.inverse ((26-a)*(26-b))
    exact mul_comm _ _
  rw [Fin.sum_univ_three,E0,E1,E2] at hI
  change f.eval y=f.eval a*basis2 a b 26 y+
    f.eval b*basis2 b a 26 y+f.eval 26*basis2 26 a b y at hI
  exact hI

theorem normalized_Q_term (c a b z t u y T w : R) (hz : IsUnit z)
    (hC : IsUnit (z-c)) (ht : IsUnit (z-t)) (hu : IsUnit (z-u))
    (hRead : z^2*(z-c)^2*w= -T*headN c a b z*casePZ c z) :
    T*(datumQZ c a b z*basisQZ c z t u y)=(y-c)*w*basis2 z t u y := by
  let k1:=z^2*(z-c)
  let k2:=(z-c)*(z-t)*(z-u)
  let k3:=(z-t)*(z-u)
  have h1 : IsUnit k1 := (hz.pow 2).mul hC
  have h2 : IsUnit k2 := (hC.mul ht).mul hu
  have h3 : IsUnit k3 := ht.mul hu
  apply (h1.mul h2).mul_left_cancel
  calc
    _ = (k1*k1⁻¹ʳ)*(k2*k2⁻¹ʳ)*((-T*headN c a b z*casePZ c z)*((y-c)*(y-t)*(y-u))) := by
      unfold datumQZ basisQZ k1 k2
      ring
    _ = _ := by
      rw [Ring.mul_inverse_cancel _ h1,Ring.mul_inverse_cancel _ h2,one_mul,one_mul,←hRead]
      change (z^2*(z-c)^2*w)*((y-c)*(y-t)*(y-u)) =
        (k1*k2)*((y-c)*w*basis2 z t u y)
      calc
        _ = (k3*k3⁻¹ʳ)*((z^2*(z-c)^2*w)*((y-c)*(y-t)*(y-u))) := by
          rw [Ring.mul_inverse_cancel _ h3,one_mul]
        _ = _ := by unfold k1 k2 k3 basis2;ring

theorem d3_eval_head (c a b y : R) (ha : (headQuadratic c).eval a=0)
    (hb : b=headSum c-a) :
    (D3 c).eval y=(y-a)*(y-b)*(y-26) := by
  have h := congrArg (fun p : Polynomial R => p.eval y) (headQuadratic_split ha hb)
  simp only [eval_headQuadratic,eval_mul,eval_sub,eval_X,eval_C] at h
  rw [d_eval,h]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actual_norm_QZ (y : R) :
    (nScale c a b*pScale c)*caseQZ c a b y=(y-c)*(V c).eval y := by
  letI : Nontrivial R := ρ.domain_nontrivial
  obtain ⟨h2,h3,_,_⟩ := standard_paid ρ
  have h5 : IsUnit (5:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have hJac := jacobi_center_paid ρ c hc
  have haU := (actual_head_denominator_units ρ c a b hc ha hb).1
  have hbU : IsUnit b := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [hb];decide +kernel))
  have hdU : IsUnit (26:R) := IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_ofNat];decide +kernel))
  have hN : IsUnit (2*b-c) :=
    IsUnit.of_map ρ _ (isUnit_iff_ne_zero.mpr (by rw [map_sub,map_mul,map_ofNat,hb,hc];decide +kernel))
  have hAll := actual_paid_sites ρ c a b hc ha hb Finset.univ
  have hh (i j : Site) (hij : i≠j) := hAll i (Finset.mem_univ _) j (Finset.mem_univ _) hij
  have h3paid : Paid (Finset.univ : Finset (Fin 3)) (threeNodes a b) := by
    intro i _ j _ hij
    apply IsUnit.of_map ρ
    apply isUnit_iff_ne_zero.mpr
    have hn : ρ ∘ threeNodes a b=threeNodes (11:F) 20 := by
      funext l
      fin_cases l <;> simp [threeNodes,ha,hb,map_ofNat]
    rw [map_sub]
    change (ρ ∘ threeNodes a b) i-(ρ ∘ threeNodes a b) j≠0
    rw [hn]
    exact (show ∀ i j : Fin 3,i≠j → threeNodes (11:F) 20 i-threeNodes (11:F) 20 j≠0 from by
      decide +kernel) i j hij
  let T := nScale c a b*pScale c
  have hRead (z : R) (h0 : (z-a)*(z-b)*(z-26)=0) :
      z^2*(z-c)^2*(V c).eval z= -T*headN c a b z*casePZ c z := by
    have h := congrArg (fun p : Polynomial R => p.eval z) (actual_quotient ρ c hp hc)
    simp only [eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C,
      d3_eval_head c a b z hRoot hOther,h0,zero_mul] at h
    have hNreal : nScale c a b*headN c a b z=(N c).eval z := by
      change (a*(2*b-c))*headN c a b z=_
      rw [scaled_N c a b z haU hN,nFlat_true c a b z hRoot hOther]
    have hP := scaled_PZ c z h2 h3 h5 hJac
    calc
      _ = -((N c).eval z*(P c).eval z) := eq_neg_of_add_eq_zero_left h
      _ = _ := by rw [←hNreal,←hP];unfold T;ring
  have hA := normalized_Q_term c a b a b 26 y T ((V c).eval a) haU
    (hh headA center (by decide +kernel)) (hh headA headB (by decide +kernel))
    (hh headA nodeD (by decide +kernel)) (hRead a (by simp))
  have hB := normalized_Q_term c a b b a 26 y T ((V c).eval b) hbU
    (hh headB center (by decide +kernel)) (hh headB headA (by decide +kernel))
    (hh headB nodeD (by decide +kernel)) (hRead b (by simp))
  have hD := normalized_Q_term c a b 26 a b y T ((V c).eval 26) hdU
    (hh nodeD center (by decide +kernel)) (hh nodeD headA (by decide +kernel))
    (hh nodeD headB (by decide +kernel)) (hRead 26 (by simp))
  have hI := interp_three a b y (V c) h3paid (show (V c).natDegree≤2 from natDegree_fromCoeffs _)
  change T*caseQZ c a b y=_
  rw [caseQZ,mul_add,mul_add,hA,hB,hD,hI]
  ring

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.ZTail.actual_norm_QZ
