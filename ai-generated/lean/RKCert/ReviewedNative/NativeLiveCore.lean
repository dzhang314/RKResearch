module

public import RKCert.ReviewedNative.ClockHeadSupport
public import RKCert.ReviewedNative.WeightedClockBand

@[expose] public section

/-! # The support of a pointwise-closed core in the original coordinates

The indicator is built within the actual submodule. Counting the weighted
polynomial band of this indicator counts distinct live numerical clocks,
not a quotient of the tableau or a selected stage set. -/
namespace RKResearch.Certified.Graded.LiveCore
open Module Polynomial RKCert.OneEscape RKCert.Endpoint RKCert.Endpoint.WeightedClock
open scoped Classical

variable {K : Type*} [Field K] {s : ℕ}
noncomputable section

def live (U : Submodule K (Fin s → K)) (i : Fin s) : Prop := ∃ u∈U, u i≠0

theorem val_eq_zero_of_not_live {U : Submodule K (Fin s → K)} {i : Fin s}
    (dead : ¬live U i) {u : Fin s → K} (hu : u∈U) : u i=0 := by
  by_contra h
  exact dead ⟨u,hu,h⟩

def liveSites (c : Fin s → K) (U : Submodule K (Fin s → K)) : Finset K :=
  (Finset.univ.filter (live U)).image c

theorem mem_liveSites {c : Fin s → K} {U : Submodule K (Fin s → K)} {a : K} :
    a∈liveSites c U ↔ ∃ i, live U i ∧ c i=a := by
  simp [liveSites,Finset.mem_image,Finset.mem_filter]

/-- Any supplied live indicator certifies the distinct-clock count. -/
theorem live_sites_le_rank_of_indicator (c : Fin s → K) (U : Submodule K (Fin s → K))
    (stable : U.map (diag c) ≤ U) {e : Fin s → K} (he : e∈U)
    (mask : ∀ i, e i=if live U i then 1 else 0) :
    (liveSites c U).card≤finrank K U := by
  classical
  have eq : weightedSites c e=liveSites c U := by
    ext a
    simp only [mem_weightedSites,mem_liveSites,mask]
    constructor
    · rintro ⟨i,hi,eq⟩
      by_cases li : live U i
      · exact ⟨i,li,eq⟩
      · exact False.elim (hi (by simp [li]))
    · rintro ⟨i,hi,eq⟩
      exact ⟨i,by simp [hi],eq⟩
  let k := (liveSites c U).card
  have sub : weightedBand c e k≤U := by
    intro v hv
    obtain ⟨P,_,rfl⟩ := mem_weightedBand.mp hv
    have eP : weightedEval c e P = fun i => P.eval (c i)*e i := by ext i; simp
    rw [eP]
    exact clock_function_mem (fun _ hu => stable (Submodule.mem_map_of_mem hu)) (fun x => P.eval x) he
  have rank : finrank K (weightedBand c e k)=k := weightedBand_rank c e k (by rw [eq])
  change k ≤ finrank K U
  rw [←rank]
  exact Submodule.finrank_mono sub

/-- The existing disjoint-representative theorem, applied to the constant
head 1, supplies the support indicator over every field, including finite
fields. The representative agrees modulo U up to a scalar. -/
theorem exists_live_indicator (U : Submodule K (Fin s → K))
    (mulClosed : ∀ u∈U, ∀ v∈U, u*v∈U) :
    ∃ e∈U, ∀ i, e i=if live U i then 1 else 0 := by
  classical
  have stable : U.map (diag (0:Fin s→K)) ≤ U := by
    rintro _ ⟨x,hx,rfl⟩
    have eq : diag (0:Fin s→K) x=0 := by ext i; simp
    rw [eq]
    exact U.zero_mem
  obtain ⟨v,v0,char⟩ := HeadFiber.disjoint_rep (w:=(1:Fin s→K)) stable mulClosed
    (fun x hx => by simpa only [mul_one] using hx)
  have h1 : (1:Fin s→K) ∈ chain (diag (0:Fin s→K)) U 1 1 := by
    change (1:Fin s→K) ∈ U ⊔ Submodule.span K {((diag (0:Fin s→K))^0) 1}
    simp only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [←char 1] at h1
  have hv : (1:Fin s→K)∈U ⊔ Submodule.span K {v} := by
    simpa only [chain,pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using h1
  obtain ⟨u,hu,x,hx,sum⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  refine ⟨u,hu,fun i => ?_⟩
  by_cases hi : live U i
  · simpa only [hi,ite_true,Pi.add_apply,Pi.smul_apply,smul_eq_mul,v0 i hi,mul_zero,
      add_zero,Pi.one_apply] using congrFun sum i
  · simp only [hi,ite_false]
    exact val_eq_zero_of_not_live hi hu

end
end RKResearch.Certified.Graded.LiveCore
