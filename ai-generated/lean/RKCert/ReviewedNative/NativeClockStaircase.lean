module
public import RKCert.OneEscape
public import RKCert.ReviewedNative.GradedDefects

@[expose] public section

/-! # A one-dimensional clock escape on native graded spaces
The linear-algebra core and chain are the original, tree-independent objects;
both strict and diagonal-retaining physical tableaux use this module. -/
namespace RKResearch.Certified.Graded
open Module RKCert.OneEscape
variable {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}

theorem zeroSpace_clock_step_of_unit {n : ℕ}
    (rank : finrank K (zeroSpace A (n+1)) ≤ finrank K (zeroSpace A n)+1)
    (esc : ¬(zeroSpace A n).map (diag (nodes A)) ≤ zeroSpace A n) :
    zeroSpace A (n+1) = zeroSpace A n ⊔ (zeroSpace A n).map (diag (nodes A)) := by
  let F := zeroSpace A n
  let C := diag (nodes A)
  have i : F ⊔ F.map C ≤ zeroSpace A (n+1) :=
    sup_le (zeroSpace_mono A (Nat.le_succ n)) (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A n))
  have lt : F < F ⊔ F.map C := lt_of_le_of_ne le_sup_left (fun e => esc (le_sup_right.trans e.ge))
  have h := Submodule.finrank_lt_finrank_of_lt lt
  exact (Submodule.eq_of_le_of_finrank_le i (by change _ ≤ finrank K ↥(F ⊔ F.map C); change _ ≤ finrank K F+1 at rank; omega)).symm

section Chain
variable {V : Type*} [AddCommGroup V] [Module K V] {T : V →ₗ[K] V} {U S : Submodule K V} {w : V}

theorem clock_chain_le_iff (n : ℕ) :
    chain T U w n ≤ S ↔ U ≤ S ∧ ∀ k < n,(T^k) w∈S := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    rw [chain,sup_le_iff,ih,Submodule.span_singleton_le_iff_mem]
    constructor
    · rintro ⟨⟨hU,old⟩,new⟩
      refine ⟨hU,fun k hk => ?_⟩
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl|h
      · exact new
      · exact old k h
    · rintro ⟨hU,new⟩
      exact ⟨⟨hU,fun k hk=>new k (by omega)⟩,new n (by omega)⟩

theorem clock_chain_next (hU : U.map T ≤ U) {n : ℕ} (hn : 0<n) :
    chain T U w n ⊔ (chain T U w n).map T = chain T U w (n+1) := by
  have R := (clock_chain_le_iff (T:=T) (U:=U) (w:=w) (n+1)).mp le_rfl
  have L := (clock_chain_le_iff (T:=T) (U:=U) (w:=w) n).mp le_rfl
  apply le_antisymm
  · refine sup_le ((clock_chain_le_iff n).mpr ⟨R.1,fun k hk=>R.2 k (by omega)⟩) ?_
    apply Submodule.map_le_iff_le_comap.mpr
    apply (clock_chain_le_iff _).mpr
    refine ⟨fun _ h => R.1 (hU ⟨_,h,rfl⟩),fun k hk => ?_⟩
    change (T*T^k) w ∈ chain T U w (n+1)
    rw [←pow_succ']
    exact R.2 _ (by omega)
  · apply (clock_chain_le_iff _).mpr
    refine ⟨L.1.trans le_sup_left,fun k hk=>?_⟩
    by_cases h:k<n
    · exact (le_sup_left : chain T U w n ≤ _) (L.2 _ h)
    · rw [show k=(n-1)+1 by omega,pow_succ',Module.End.mul_eq_comp,LinearMap.comp_apply]
      exact (le_sup_right : (chain T U w n).map T ≤ _) ⟨_,L.2 _ (by omega),rfl⟩
end Chain

end RKResearch.Certified.Graded
