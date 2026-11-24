module

public import RKCert.ReviewedNative.ERKUniform
public import RKCert.ReviewedNative.TerminalCapacity

public section

/-! # Saturation of the measured native even midpoint

At equality in the uniform even floor, neither a forward rank surplus nor
an initial reverse direction fits. The true reverse annihilator and each
paid preceding flag are exact. The final *physical* coordinate is active,
has clock one, and belongs to the midpoint tree space.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {s p q : ℕ}

/-- Physical rank data at the even stage floor, on the unmodified tableau. -/
structure ERKEvenHorizon (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (q : ℕ) : Prop where
  stageCount : s=3*q-2
  defectRank : finrank K (zeroSpace A q)=q-1
  treeRank : finrank K (treeSpace A q)=2*q
  firstZero : firstSeed A b=0
  full : back A b (q-2)=annih (treeSpace A q)
  flagExact : ∀ n ≤ q-2, finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n
  terminal : ∃ t : Fin s, (∀ i, i≤t) ∧ LastActive b t ∧ nodes A t=1 ∧
    coordinate (K:=K) t ∈ treeSpace A q

/-- A cap at the uniform even floor forces the full native horizon. An
auxiliary prefix argument only establishes that the last *original* weight
is nonzero; no count or conclusion replaces the original tableau. -/
theorem erk_even_horizon_of_stage_cap {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder p A b) (hq : 2≤q)
    (pay : 2*q≤p) (cap : s≤3*q-2) : ERKEvenHorizon A b q := by
  have ff := zeroSpace_finrank ha ho (n:=q-1) (by omega)
  rw [show q-1+1=q by omega] at ff
  have room := erk_even_midpoint_budget ha ho hq pay
  have front := erk_midpoint_tree_rank ha ho (by omega) pay
  have hs : s=3*q-2 := by omega
  have f : finrank K (zeroSpace A q)=q-1 := by omega
  have tr : finrank K (treeSpace A q)=2*q := by omega
  obtain ⟨z,full,primitiveFull⟩ :=
    reverse_capacity_paid ha ho (j:=q) (n:=q-2) (by omega) (by omega)
  have top : finrank K (primitiveBack A b (q-2))=q-2 := by
    rw [primitiveFull]
    have dim := finrank_annih (treeSpace A q)
    rw [Fintype.card_fin] at dim
    omega
  have exactFlag (n : ℕ) (hn : n≤q-2) :
      finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n := by
    have g := primitiveBack_interval ha ho n (q-2-n) (by omega)
    rw [show n+(q-2-n)=q-2 by omega,top] at g
    have lo := back_finrank ha ho n (by omega)
    rw [first_dim_zero z,zero_add] at lo
    have inc := back_le_primitiveBack (A:=A) (b:=b) n
    have mono := Submodule.finrank_mono inc
    exact ⟨by omega,Submodule.eq_of_le_of_finrank_le inc (by omega)⟩
  refine ⟨hs,f,tr,z,full,exactFlag,?_⟩
  cases s with
  | zero => omega
  | succ m =>
    let len : m ≤ m+1 := Nat.le_succ m
    have live : b (Fin.last m) ≠ 0 := by
      intro dz
      have tail (i : Fin (m+1)) (hle : m ≤ i.val) : b i=0 := by
        have eq : i=Fin.last m := Fin.ext (by have := i.isLt; change i.val=m; omega)
        rwa [eq]
      have pref := prefix_hasOrder_of_suffix_zero ha ho len tail
      have none := erk_even_midpoint_floor (prefix_strict_lower ha len) pref hq pay
      omega
    have maximal (i : Fin (m+1)) : i≤Fin.last m := by
      change i.val≤m
      have := i.isLt
      omega
    have L : LastActive b (Fin.last m) :=
      ⟨live,fun i hi => (not_lt_of_ge (maximal i) hi).elim⟩
    obtain ⟨_,one,_,terminal⟩ :=
      reverse_capacity_terminal ha ho (j:=q) (n:=q-2) (by omega) (by omega) L
    exact ⟨Fin.last m,maximal,L,one,terminal _ le_rfl⟩

end RKResearch.Certified.Graded.Reverse
