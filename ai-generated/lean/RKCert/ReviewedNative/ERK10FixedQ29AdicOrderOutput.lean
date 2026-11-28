module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderAttach
public import RKCert.ReviewedOrderBridge
public import RKResearch.ERK

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical

open Nonlinear Polynomial
open scoped Ring BigOperators Polynomial
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

theorem actual_origin_row (c a b : R) (j : Fin 15) :
    tableau15 c a b (actualK c a b) (oldSlot 0) j=0 :=
  actual_tableau_strict c a b _ _ (show (0:Fin 15)≤j from Fin.zero_le _)

theorem retained_origin_model (c a b : R) (t : RKCert.Tree) :
    retainedTreeProfile c a b t 0=treeModel t 0 := by
  cases t with
  | leaf =>
    simp [retainedTreeProfile,RKCert.stageWeight,treeModel,treeScale,RKCert.Tree.order]
  | attach u v =>
    have hu := u.order_pos
    have hv := v.order_pos
    have hpos : u.order+v.order-1≠0 := by omega
    simp [retainedTreeProfile,RKCert.stageWeight,actual_origin_row,
      treeModel,RKCert.Tree.order,zero_pow hpos]

theorem avg_reflected_int :
    ∀ k : Fin 10, (((k.val+1:ℕ):ℤ))*avgRaw (fun y : ℤ => (1-y)^k.val)=(avgDen:ℤ) := by
  decide +kernel

theorem avg_reflected_cast (k : ℕ) :
    (Int.castRingHom R) (avgRaw (fun y : ℤ => (1-y)^k))=
      avgRaw (fun y : R => (1-y)^k) := by
  simp only [avgRaw,map_sum,map_mul,map_pow,map_sub,map_one]
  apply Finset.sum_congr rfl
  intro i _
  change (avgNumerator i.val:R)*(1-((i.val:ℤ):R))^k=_
  rw [Int.cast_natCast]

theorem small_order_paid (ρ : R→+*F) [IsLocalHom ρ] (n : ℕ)
    (hn : 0<n) (hN : n≤10) : IsUnit (n:R) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [map_natCast]
  let u : Fin 11:=⟨n,by omega⟩
  exact (show ∀ u : Fin 11,u.val≠0→(u.val:F)≠0 from by decide +kernel) u (by exact Nat.ne_of_gt hn)

theorem avg_reflected_paid (ρ : R→+*F) [IsLocalHom ρ] (n : ℕ) (hn : n≤9) :
    ((n+1:ℕ):R)*avg (fun y : R => (1-y)^n)=1 := by
  let k : Fin 10 := ⟨n,by omega⟩
  have H := congrArg (Int.castRingHom R) (avg_reflected_int k)
  simp only [map_mul,avg_reflected_cast] at H
  change (((n+1:ℕ):ℤ):R)*avgRaw (fun y : R => (1-y)^n)=((avgDen:ℤ):R) at H
  rw [Int.cast_natCast,Int.cast_natCast] at H
  have hU : IsUnit (avgDen:R) := Packed.paid_unit ρ (by decide +kernel)
  calc
    _ = Ring.inverse (avgDen:R)*(((n+1:ℕ):R)*avgRaw (fun y : R=>(1-y)^n)) := by
      unfold avg
      ring
    _ = _ := by rw [H,mul_comm,Ring.mul_inverse_cancel _ hU]

theorem treeScale_childDensity (ρ : R→+*F) [IsLocalHom ρ] (t : RKCert.Tree)
    (ht : t.order≤10) : (t.childDensityProduct:R)*treeScale t=1 := by
  induction t with
  | leaf => simp [RKCert.Tree.childDensityProduct,treeScale]
  | attach u v ihU ihV =>
    have hu := u.order_pos
    have hv := v.order_pos
    change u.order+v.order≤10 at ht
    have hU := small_order_paid ρ u.order hu (by omega)
    have U := ihU (by omega)
    have V := ihV (by omega)
    simp only [RKCert.Tree.childDensityProduct,treeScale,Nat.cast_mul]
    calc
      _ = ((u.order:R)*Ring.inverse (u.order:R))*
            ((u.childDensityProduct:R)*treeScale u)*((v.childDensityProduct:R)*treeScale v) := by ring
      _ = _ := by rw [Ring.mul_inverse_cancel _ hU,U,V,one_mul,one_mul]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include ρ hp hc ha hb hRoot hOther

theorem actual_weight_scalar (h : OrderAttachReceipts c a b) (t : RKCert.Tree)
    (ht : t.order≤10) :
    RKCert.weight (tableau15 c a b (actualK c a b)) (tableauWeights c a b) t =
      treeScale t*avg (fun y : R => (1-y)^(t.order-1)) := by
  let n:=t.order-1
  let p : Polynomial R := (1-X)^n
  have hn : n≤9 := by unfold n;omega
  have hpdeg : ((1:Polynomial R)-X).natDegree≤1 :=
    (natDegree_sub_le ..).trans (max_le (by simp) natDegree_X_le)
  have hPn : p.natDegree≤n := by
    simpa only [p,mul_one] using natDegree_pow_le_of_le n hpdeg
  have hP := hPn.trans hn
  have hCard := raw_cardinal ρ c a b hp hc ha hb p hP
  have hM : (∑ i : Site,rawW c a b i*(rawClock c a b i)^n) +
      score (nodal c a b) oldOrigin*(0:R)^n = avg (fun y : R => (1-y)^n) := by
    simpa only [p,eval_pow,eval_sub,eval_one,eval_X,avgLin_apply,sub_self,rawClock,mul_comm] using hCard
  have hOld :
      (∑ j : Old,(if j=0 then score (nodal c a b) oldOrigin else 0)*
        retainedTreeProfile c a b t j) =
          score (nodal c a b) oldOrigin*(treeScale t*(0:R)^n) := by
    simp [ite_mul,retained_origin_model,treeModel,n]
  have hD (i : Site) : rawTreeProfile c a b t i =
      rawTreeErr c a b t i+treeScale t*(rawClock c a b i)^n := by
    simp only [rawTreeErr,Pi.sub_apply,rawTreeNominal,treeModel,n]
    ring
  have hRaw :
      (∑ i : Site,rawW c a b i*rawTreeProfile c a b t i)=
        treeScale t*(∑ i : Site,rawW c a b i*(rawClock c a b i)^n) := by
    simp_rw [hD,mul_add,Finset.sum_add_distrib]
    rw [actual_error_output_zero ρ c a b hp hc ha hb hRoot hOther h t ht,zero_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [RKCert.weight,sum_slots]
  simp_rw [tableauWeights_oldSlot,tableauWeights_rawSlot]
  change (∑ j : Old,(if j=0 then score (nodal c a b) oldOrigin else 0)*
    retainedTreeProfile c a b t j)+(∑ i : Site,rawW c a b i*rawTreeProfile c a b t i)=_
  rw [hOld,hRaw,←hM]
  ring

/-- Actual reviewed order ten, conditional only on the stated
low/linear physical edge receipts. The nonlinear filtration and exact
scalar output are already kernel proofs, not abstract order axioms. -/
theorem actual_hasOrder10_of_receipts (h : OrderAttachReceipts c a b) :
    RKResearch.HasOrder 10 (tableau15 c a b (actualK c a b)) (tableauWeights c a b) := by
  apply (RKCert.ReviewedOrderBridge.hasOrder_iff _ _ _).2
  intro t ht
  rw [actual_weight_scalar ρ c a b hp hc ha hb hRoot hOther h t ht,
    RKCert.Tree.density,Nat.cast_mul]
  have hPos := t.order_pos
  have hN : t.order-1≤9 := by omega
  have hJ := avg_reflected_paid ρ (t.order-1) hN
  rw [show t.order-1+1=t.order from by omega] at hJ
  calc
    _ = ((t.childDensityProduct:R)*treeScale t)*
      ((t.order:R)*avg (fun y : R => (1-y)^(t.order-1))) := by ring
    _ = _ := by rw [treeScale_childDensity ρ t ht,hJ,one_mul]

end Actual

theorem actual_is_ERK (c a b : R) : RKResearch.ERK (tableau15 c a b (actualK c a b)) :=
  fun {_ _} h => actual_tableau_strict c a b _ _ h

end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.treeScale_childDensity
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_weight_scalar
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_hasOrder10_of_receipts
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_is_ERK
