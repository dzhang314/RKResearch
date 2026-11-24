module

public import RKCert.NodalHermiteRank
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-! # Weighted polynomial bands on the actual distinct clock values

This finite-dimensional rank device is tree-free. Saturation uses the
remainder modulo the genuine nodal product, not a change of stage order. -/
namespace RKCert.Endpoint.WeightedClock
open Polynomial Module
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}
noncomputable section

def weightedSites (c v : Fin s → K) : Finset K :=
  (Finset.univ.filter (fun i => v i ≠ 0)).image c

theorem mem_weightedSites {c v : Fin s → K} {x : K} :
    x ∈ weightedSites c v ↔ ∃ i, v i ≠ 0 ∧ c i=x := by
  simp [weightedSites,Finset.mem_image,Finset.mem_filter]

def weightedBand (c v : Fin s → K) (k : ℕ) : Submodule K (Fin s → K) :=
  ((weightedEval c v).comp (ofFn k)).range

theorem mem_weightedBand {c v : Fin s → K} {k : ℕ} {w : Fin s → K} :
    w ∈ weightedBand c v k ↔
      ∃ P : K[X], P.degree < (k : WithBot ℕ) ∧ weightedEval c v P = w := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨ofFn k a,ofFn_degree_lt a,rfl⟩
  · rintro ⟨P,d,rfl⟩
    by_cases z : P = 0
    · subst P
      exact ⟨0,by rw [map_zero,map_zero]⟩
    · have e := ofFn_comp_toFn_eq_id_of_natDegree_lt ((natDegree_lt_iff_degree_lt z).mpr d)
      exact ⟨toFn k P,by rw [LinearMap.comp_apply,e]⟩

theorem weightedBand_rank (c v : Fin s → K) (k : ℕ) (enough : k ≤ (weightedSites c v).card) :
    finrank K (weightedBand c v k) = k := by
  apply (LinearMap.finrank_range_of_inj (f:=(weightedEval c v).comp (ofFn k)) ?_).trans
    (Module.finrank_fin_fun K)
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro f hf
  apply injective_ofFn k
  rw [map_zero]
  apply eq_zero_of_degree_lt_of_eval_finset_eq_zero (weightedSites c v)
  · exact (ofFn_degree_lt f).trans_le (by exact_mod_cast enough)
  · intro x hx
    obtain ⟨i,hi,e⟩ := mem_weightedSites.mp hx
    have a := congrFun hf i
    change weightedEval c v (ofFn k f) i=0 at a
    rw [weightedEval_apply,e] at a
    exact (mul_eq_zero.mp a).resolve_right hi

theorem weightedBand_eq_range (c v : Fin s → K) (k : ℕ) (enough : (weightedSites c v).card ≤ k) :
    weightedBand c v k = (weightedEval c v).range := by
  apply le_antisymm
  · rintro w hw
    obtain ⟨P,_,rfl⟩ := mem_weightedBand.mp hw
    exact ⟨P,rfl⟩
  · rintro _ ⟨P,rfl⟩
    let H := nodalHull (weightedSites c v)
    have mon : H.Monic := monic_nodalHull _
    have d : H.degree ≤ (k : WithBot ℕ) := by
      rw [degree_eq_natDegree mon.ne_zero,show H.natDegree=(weightedSites c v).card from natDegree_nodalHull _]
      exact_mod_cast enough
    refine mem_weightedBand.mpr ⟨P %ₘ H,(degree_modByMonic_lt P mon).trans_le d,?_⟩
    ext i
    simp only [weightedEval_apply]
    by_cases nz : v i = 0
    · simp only [nz,mul_zero]
    · have hi : H.eval (c i)=0 := nodalHull_eval_of_mem (mem_weightedSites.mpr ⟨i,nz,rfl⟩)
      have e := congrArg (eval (c i)) (modByMonic_add_div P H)
      rw [eval_add,eval_mul,hi,zero_mul,add_zero] at e
      rw [e]

/-- A complete weighted-evaluation range is invariant under the clock multiplier. -/
theorem weighted_range_clock (c v : Fin s → K) {w : Fin s → K}
    (hw : w ∈ (weightedEval c v).range) :
    (fun i => c i*w i) ∈ (weightedEval c v).range := by
  obtain ⟨P,rfl⟩ := hw
  refine ⟨X*P,?_⟩
  ext i
  simp [weightedEval_apply,mul_assoc]

end
end RKCert.Endpoint.WeightedClock
