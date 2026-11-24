module

public import RKCert.Dirk15PhysicalSignatures
public import RKCert.Dirk15ReverseNonlocal

@[expose] public section

/-! # Surjectivity of true E7 evaluation on any nonterminal single-clock subset -/
namespace RKCert.Paired
open Module
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

set_option maxHeartbeats 1400000 in
theorem order15_e7_fiber_restrict_top (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {n : ℕ} (idx : Fin n→Fin 20)
    (inj : Function.Injective idx) (nont : ∀ i,idx i≠Fin.last 19) (a : K)
    (node : ∀ i,nodes A (idx i)=a) :
    (treeSpace A 7).map (restrictCol idx)=⊤ := by
  let W := (treeSpace A 7).map (restrictCol idx)
  change W=⊤
  by_contra h
  have Ann : annih W≠⊥ := by
    intro z
    apply h
    rw [←annih_annih_paired W,z]
    apply le_antisymm le_top
    intro v _
    apply mem_annih.mpr
    intro d hd
    rw [Submodule.mem_bot] at hd
    rw [hd,row_apply]
    simp
  obtain ⟨u,hu,un⟩ := (annih W).ne_bot_iff.mp Ann
  let d : Vec K 20 := ∑ i : Fin n,u i • Pi.single (idx i) (1:K)
  have substL (i : Fin 20) (ne : ∀ j,idx j≠i) : d i=0 := by
    rw [show d i=(∑ j : Fin n,u j • Pi.single (idx j) (1:K)) i from rfl,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    simp [Pi.single_eq_of_ne (ne j).symm]
  have eval (i : Fin n) : d (idx i)=u i := by
    rw [show d (idx i)=(∑ j : Fin n,u j • Pi.single (idx j) (1:K)) (idx i) from rfl,
      Finset.sum_apply,Finset.sum_eq_single i]
    · simp
    · intro j _ nj
      simp [Pi.single_eq_of_ne (fun z => nj (inj z.symm))]
    · simp
  have pair (v : Vec K 20) (hv : v∈treeSpace A 7) : row d v=0 := by
    have h₀ := mem_annih.mp hu _ (Submodule.mem_map_of_mem hv)
    change row u (restrictCol idx v)=0 at h₀
    change rowL (∑ j : Fin n,u j • Pi.single (idx j) (1:K)) v=0
    calc
      _ = ∑ j : Fin n,u j*row (Pi.single (idx j) (1:K)) v := by
        rw [map_sum,LinearMap.sum_apply]
        simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,rowL_apply]
      _ = row u (restrictCol idx v) := by
        rw [row_apply u]
        simp only [row_single_left,restrictCol_apply]
      _ = 0 := h₀
  have d0 := order15_no_local_e7_relation ha ho H (order15_minimal_reverse_nonlocal ha ho H)
    pair (substL (Fin.last 19) nont) a
    (fun i ne => substL i (fun j e => ne (e ▸ node j)))
  apply un
  ext i
  rw [←eval i,d0,Pi.zero_apply,Pi.zero_apply]

end
end RKCert.Paired
