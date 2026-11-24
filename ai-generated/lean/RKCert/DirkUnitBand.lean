module

public import RKCert.DirkHermite

@[expose] public section
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}

theorem dirk_unit_band_of_no_grade_six_surplus
    (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (ho : HasTreeOrderAtLeast A b p) (hp : 8≤p)
    (h : ¬ finrank K (zeroSpace A 3)+4≤finrank K (zeroSpace A 6)) :
    (∀ j, 3≤j → j<6 → finrank K (zeroSpace A (j+1))=finrank K (zeroSpace A j)+1) ∧
    (∀ j, 4≤j → j≤6 → ¬ (zeroSpace A j).map (diag (nodes A))≤zeroSpace A j) := by
  have h34 := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=3)
    (by decide) (by omega))
  have h45 := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=4)
    (by decide) (by omega))
  have h56 := Submodule.finrank_lt_finrank_of_lt (dirk_zeroSpace_lt_succ ha ho (j:=5)
    (by decide) (by omega))
  change finrank K (zeroSpace A 3)<finrank K (zeroSpace A 4) at h34
  change finrank K (zeroSpace A 4)<finrank K (zeroSpace A 5) at h45
  change finrank K (zeroSpace A 5)<finrank K (zeroSpace A 6) at h56
  have hEq (j : ℕ) (hj : 3≤j) (hj' : j<6) :
      finrank K (zeroSpace A (j+1))=finrank K (zeroSpace A j)+1 := by
    rcases (show j=3 ∨ j=4 ∨ j=5 by omega) with rfl|rfl|rfl
    · change finrank K (zeroSpace A 4)=finrank K (zeroSpace A 3)+1; omega
    · change finrank K (zeroSpace A 5)=finrank K (zeroSpace A 4)+1; omega
    · change finrank K (zeroSpace A 6)=finrank K (zeroSpace A 5)+1; omega
  refine ⟨hEq,fun j hl hu hC => ?_⟩
  have hv (v) (hm : v∈zeroSpace A j) : diag (nodes A) v∈zeroSpace A j :=
    hC (Submodule.mem_map_of_mem hm)
  by_cases he : j=6
  · subst j
    have hi := dirk_forward_invariant_incoming ha ho (j:=6) (by omega) hv
    change finrank K (zeroSpace A 5)+2≤finrank K (zeroSpace A 6) at hi
    omega
  · have hi := dirk_forward_invariant_outgoing ha ho (j:=j) (by omega)
      (zeroSpace A j) le_rfl hv
    have eq := hEq j (by omega) (by omega)
    omega

end RKCert.Paired
