module

public import RKCert.ERKGradeFive
public import Mathlib.LinearAlgebra.Eigenspace.Zero

@[expose] public section

/-! # Chronological and dimension lemmas for the low-order barriers -/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s p : ℕ}

/-- Exact prefix truncation when all discarded output weights vanish. -/
theorem prefix_order_of_suffix_zero {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) {k : ℕ} (hk : k ≤ s)
    (hb : ∀ i : Fin s, k ≤ i.val → b i=0) :
    HasTreeOrderAtLeast (prefixTableau A hk) (b ∘ Fin.castLE hk) p := by
  intro t ht
  have h : weight (prefixTableau A hk) (b ∘ Fin.castLE hk) t = weight A b t := by
    rw [weight, ← prefix_tree ha hk]
    exact sum_on_prefix hk (fun j => b j * stageWeight A t j)
      (fun j hj => by rw [hb j hj,zero_mul])
  rw [h]
  exact ho t ht

/-- A tableau attaining the uniform numerical floor cannot leave its last
chronological coordinate unused, without assumptions on earlier weights. -/
theorem last_weight_of_uniform_equality {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (hs : max p ((3*p+1)/2-2)=s+1) :
    b (Fin.last s)≠0 := by
  intro hz
  have hb (i : Fin (s+1)) (hi : s ≤ i.val) : b i=0 := by
    have he : i=Fin.last s := Fin.ext (by change i.val=s; have := i.isLt; omega)
    rwa [he]
  have h := uniform_erk_field (prefix_strict ha (k:=s) (by omega))
    (prefix_order_of_suffix_zero ha ho (k:=s) (by omega) hb)
  omega

/-- The bilinear row representation loses no annihilating dimension. -/
theorem finrank_add_annih_eq (U : Submodule K (Vec K s)) :
    finrank K U + finrank K (annih U) = s := by
  have hmap : (annih U).map rowL = U.dualAnnihilator := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr le_rfl
    · intro f hf
      obtain ⟨v,rfl⟩ := rowL_surj f
      exact Submodule.mem_map_of_mem hf
  have hr := (Submodule.equivMapOfInjective rowL rowL_inj (annih U)).finrank_eq
  rw [hmap] at hr
  rw [hr,Subspace.finrank_add_finrank_dualAnnihilator_eq,Module.finrank_fin_fun]

/-- The exact polynomial-plus-defect decomposition gives an upper rank
bound too. This side of the estimate requires no separation. -/
theorem treeSpace_finrank_le_sum {A : Fin s → Fin s → K} {b : Vec K s}
    (ho : HasTreeOrderAtLeast A b p) (q : ℕ) (hq : q+1 ≤ p) :
    finrank K (treeSpace A q)  ≤  q+1 + finrank K (zeroSpace A q) := by
  let F := zeroSpace A q
  let E := treeSpace A q
  let f : ((Fin (q+1) → K) × F) →ₗ[K] Vec K s := (polyEval A q).coprod F.subtype
  let g : ((Fin (q+1) → K) × F) →ₗ[K] E := f.codRestrict E (fun z =>
    E.add_mem (polyEval_mem_treeSpace _ _ _) (zeroSpace_le_treeSpace _ _ z.2.property))
  have hg : Function.Surjective g := by
    intro v
    obtain ⟨a,ha⟩ := exists_poly_zeroSpace ho hq v.property
    refine ⟨(a,⟨_,ha⟩),Subtype.ext ?_⟩
    change polyEval A q a + ((v : Vec K s)-polyEval A q a) = (v : Vec K s)
    abel
  simpa only [Module.finrank_prod, Module.finrank_fin_fun] using
    (LinearMap.finrank_le_finrank_of_surjective hg)

theorem explicit_treeSpace_finrank_eq {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (q : ℕ)
    (hs : 0 < s) (hq : 2*q ≤ p) (hqp : q+1 ≤ p) :
    finrank K (treeSpace A q) = q+1 + finrank K (zeroSpace A q) :=
  le_antisymm (treeSpace_finrank_le_sum ho q hqp) (explicit_treeSpace_rank ha ho hq hs)

theorem mat_pow_zero_at_early {A : Fin s → Fin s → K} (ha : StrictLower A) (v : Vec K s)
    (n : ℕ) (i : Fin s) (hi : i.val < n) :
    (((mat A : Module.End K (Vec K s))^n) v) i=0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp]
    exact causal_mat ha i _ (fun j hj => ih j (by change j.val < i.val at hj; omega))

theorem mat_isNilpotent {A : Fin s → Fin s → K} (ha : StrictLower A) :
    IsNilpotent (mat A : Module.End K (Vec K s)) := by
  refine ⟨s,?_⟩
  apply LinearMap.ext
  intro v
  ext i
  exact mat_pow_zero_at_early ha v s i i.isLt

theorem stageWeight_chain_eq_pow (A : Fin s → Fin s → K) (n : ℕ) :
    stageWeight A (Tree.chain n) = ((mat A : Module.End K (Vec K s))^n) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext i
    rw [stageWeight_chain_succ,pow_succ',mul_apply_eq_comp,← ih,mat_apply]

/-- An A-invariant actual stage space containing the leaf already has
dimension at least the attained order, by restricted nilpotence. -/
theorem dim_of_invariant_stage_space {A : Fin s → Fin s → K} {b : Vec K s}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p)
    (U : Submodule K (Vec K s)) (h1 : (1 : Vec K s)∈U)
    (hU : ∀ v∈U, mat A v∈U) : p ≤ finrank K U := by
  let f : Module.End K U := (mat A).restrict (fun {x} hx => hU x hx)
  have hpow (n : ℕ) (u : U) : ((f^n) u : Vec K s) = ((mat A : Module.End K (Vec K s))^n) u := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',pow_succ',mul_apply_eq_comp,mul_apply_eq_comp]
      change mat A (((f^n) u : U) : Vec K s) = mat A (((mat A : Module.End K (Vec K s))^n) u)
      rw [ih]
  have hf : IsNilpotent f := by
    obtain ⟨n,hn⟩ := mat_isNilpotent ha
    refine ⟨n,?_⟩
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (hpow n x).trans (by rw [hn]; rfl)
  have hnil : f ^ finrank K U = 0 := by
    simpa only [hf.charpoly_eq_X_pow_finrank,map_pow,Polynomial.aeval_X] using f.aeval_self_charpoly
  by_contra hp
  have hchain := chain_condition ho (n:=finrank K U) (by omega)
  have hz := (hpow (finrank K U) ⟨1,h1⟩).symm
  rw [hnil] at hz
  have hz' : stageWeight A (Tree.chain (finrank K U)) = 0 := by
    rw [stageWeight_chain_eq_pow]
    exact hz
  rw [weight,hz'] at hchain
  simp at hchain

/-- In an annihilator of dimension at most two, a nonzero invariant
subspace is forbidden when the quadratic reverse seed and its first
images fit in the grade budget. -/
theorem annih_invariant_rank_two {A : Fin s → Fin s → K} {b : Vec K s} {j : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hj : j+4 ≤ p)
    (hr : finrank K (annih (treeSpace A j)) ≤ 2)
    (U : Submodule K (Vec K s)) (hU : U ≤ annih (treeSpace A j))
    (hN : ∀ v∈U, transMat A v∈U) (hD : ∀ v∈U, diag (mirror A) v∈U) :
    U=⊥ := by
  by_contra hne
  let V := annih (treeSpace A j)
  let r := backSeed2 A b
  let z := diag (mirror A) b
  have hone : (1 : Vec K s)∈treeSpace A j :=
    stageWeight_mem_space A .leaf (by change 1 ≤ j+1; omega)
  have hzout : z∉V := by
    intro hz
    exact back_target_nonzero ho (by omega) (mem_annih.mp hz _ hone)
  have hrout : r∉U := by
    intro h
    exact hzout (hU (mem_of_invariant_seed Fin.revPerm _ (causal_transpose ha)
      (mirror A) b U hN hD h))
  have hm : r∈V := backSeed2_annih ho (by omega)
  let W := U ⊔ Submodule.span K {r}
  have hWV : W ≤ V := sup_le hU ((Submodule.span_singleton_le_iff_mem ..).mpr hm)
  have hrW := Submodule.finrank_sup_span_singleton hrout
  have hpU : 1 ≤ finrank K U := Submodule.one_le_finrank_iff.mpr hne
  have hdimW : finrank K W=finrank K U+1 := hrW
  have hdimV : finrank K V ≤ 2 := hr
  have he : W=V := Submodule.eq_of_le_of_finrank_le hWV (by omega)
  have hrN : transMat A r∈V := by
    apply mem_annih.mpr
    intro v hv
    rw [row_flip_mat]
    exact mem_annih.mp (backSeed2_annih ho (j:=j+1) (by omega)) _ (mat_treeSpace A j hv)
  have hrD : diag (mirror A) r∈V := by
    apply mem_annih.mpr
    intro v hv
    rw [row_flip_diag]
    exact mem_annih.mp (backSeed2_annih ho (j:=j+1) (by omega)) _ (mirror_treeSpace A j hv)
  apply hzout
  apply mem_of_invariant_seed Fin.revPerm _ (causal_transpose ha) (mirror A) b V _ _ hm
  · intro x hx
    rw [← he] at hx
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add,map_smul]
    exact V.add_mem (hU (hN u hu)) (V.smul_mem _ hrN)
  · intro x hx
    rw [← he] at hx
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add,map_smul]
    exact V.add_mem (hU (hD u hu)) (V.smul_mem _ hrD)

end RKCert.Paired
