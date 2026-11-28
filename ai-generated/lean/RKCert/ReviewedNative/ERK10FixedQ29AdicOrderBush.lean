module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicOrderMinimal

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped Ring BigOperators
noncomputable section
set_option maxHeartbeats 500000
variable {R : Type*} [CommRing R]

def physicalBush : ℕ→RKCert.Tree
  | 0 => .leaf
  | n+1 => .attach .leaf (physicalBush n)

@[simp] theorem physicalBush_order (n : ℕ) : (physicalBush n).order=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [physicalBush,RKCert.Tree.order,ih]
    omega

theorem physicalBush_childDensity (n : ℕ) : (physicalBush n).childDensityProduct=1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [physicalBush,RKCert.Tree.childDensityProduct,RKCert.Tree.order,ih,one_mul]

@[simp] theorem physicalBush_density (n : ℕ) : (physicalBush n).density=n+1 := by
  simp only [RKCert.Tree.density,physicalBush_order,physicalBush_childDensity,mul_one]

theorem physicalBush_profile {s : ℕ} (A : Fin s→Fin s→R) (n : ℕ) (i : Fin s) :
    RKCert.stageWeight A (physicalBush n) i=(∑ j, A i j)^n := by
  induction n with
  | zero => simp [physicalBush,RKCert.stageWeight]
  | succ n ih =>
    simp only [physicalBush,RKCert.stageWeight,mul_one,ih,pow_succ]
    ring

theorem actual_raw_clock_eq (c a b : R) (H : MinimalEdgeReceipts c a b) (i : Site) :
    ∑ j : Fin 15,tableau15 c a b (actualK c a b) (rawSlot i) j=rawClock c a b i := by
  have hh := congrFun (H.base_low .leaf (by decide +kernel)) i
  simp only [rawTreeEdge,RKCert.stageWeight,mul_one,rawTreePrimitive,treePrim,treeScale,
    RKCert.Tree.order,Nat.cast_one,Ring.inverse_one,one_mul,pow_one] at hh
  exact sub_eq_zero.mp hh

theorem actual_bush_weight (c a b : R) (H : MinimalEdgeReceipts c a b) :
    RKCert.weight (tableau15 c a b (actualK c a b)) (tableauWeights c a b) (physicalBush 10)=
      ∑ i : Site,rawW c a b i*(rawClock c a b i)^10 := by
  rw [RKCert.weight,sum_slots]
  simp_rw [tableauWeights_rawSlot,tableauWeights_oldSlot,physicalBush_profile]
  have hh :
      (∑ j : Old,(if j=0 then score (nodal c a b) oldOrigin else 0)*
        (∑ k : Fin 15,tableau15 c a b (actualK c a b) (oldSlot j) k)^10)=0 := by
    simp only [ite_mul,zero_mul]
    simp [actual_origin_row]
  rw [hh,zero_add]
  simp_rw [actual_raw_clock_eq c a b H]

section Actual
variable (ρ : R→+*F) [IsLocalHom ρ] (c a b : R)
variable (hp : (decic R).eval c=0) (hc : ρ c=2) (ha : ρ a=11) (hb : ρ b=20)
include ρ hp hc ha hb

theorem actual_bush_residue (H : MinimalEdgeReceipts c a b) :
    ρ (((physicalBush 10).density:R)*
      RKCert.weight (tableau15 c a b (actualK c a b)) (tableauWeights c a b) (physicalBush 10)-1)=10 := by
  rw [actual_bush_weight c a b H,physicalBush_density]
  have hY (i : Site) : ρ (rawY c a b i)=Ymod i := congrFun (actual_Y_mod ρ c a b hc ha hb) i
  have hW (i : Site) : ρ (rawW c a b i)=Wmod i := congrFun (actual_W_mod ρ c a b hp hc ha hb) i
  simp only [rawClock,map_sub,map_one,map_mul,map_sum,map_pow,map_natCast,hY,hW]
  decide +kernel

/-- A unit defect at the actual literal tableau (not just its prime-field
representative), obtained without comparing all 15×15 coefficients. -/
theorem actual_bush_failure_unit (H : MinimalEdgeReceipts c a b) :
    IsUnit (((physicalBush 10).density:R)*
      RKCert.weight (tableau15 c a b (actualK c a b)) (tableauWeights c a b) (physicalBush 10)-1) := by
  apply IsUnit.of_map ρ
  apply isUnit_iff_ne_zero.mpr
  rw [actual_bush_residue ρ c a b hp hc ha hb H]
  decide +kernel

theorem actual_notOrder11_of_three_edges (H : MinimalEdgeReceipts c a b) :
    ¬ RKResearch.HasOrder 11 (tableau15 c a b (actualK c a b)) (tableauWeights c a b) := by
  intro h
  letI : Nontrivial R := ρ.domain_nontrivial
  have hB := (RKCert.ReviewedOrderBridge.hasOrder_iff _ _ _).1 h
  apply (actual_bush_failure_unit ρ c a b hp hc ha hb H).ne_zero
  exact sub_eq_zero.mpr (hB (physicalBush 10) (by decide +kernel))

variable (hRoot : (headQuadratic c).eval a=0) (hOther : b=headSum c-a)
include hRoot hOther

theorem actual_exact10_of_three_edges (H : MinimalEdgeReceipts c a b) :
    RKResearch.ERK (tableau15 c a b (actualK c a b)) ∧
    RKResearch.HasOrder 10 (tableau15 c a b (actualK c a b)) (tableauWeights c a b) ∧
    ¬ RKResearch.HasOrder 11 (tableau15 c a b (actualK c a b)) (tableauWeights c a b) :=
  ⟨actual_is_ERK c a b,actual_hasOrder10_of_three_edges ρ c a b hp hc ha hb hRoot hOther H,
    actual_notOrder11_of_three_edges ρ c a b hp hc ha hb H⟩

end Actual
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_raw_clock_eq
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_bush_failure_unit
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.actual_exact10_of_three_edges
