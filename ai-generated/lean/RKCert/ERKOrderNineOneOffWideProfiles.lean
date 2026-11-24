module

public import RKCert.ERKOrderNineOneOffAnchoredRadau

@[expose] public section

/-! # The genuine eleven coefficient columns at homogeneous grade five -/
namespace RKCert.Paired.OneOff
open Module Polynomial
open scoped Classical

variable {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Fin s→Fin s→K}

abbrev NormalCoeffs (K : Type*) := (Fin 6→K) × (K × (Fin 3→K))
abbrev WideCoeffs (K : Type*) := NormalCoeffs K × K

noncomputable def normalProfileMap (A : Fin s→Fin s→K) :
    NormalCoeffs K →ₗ[K] Vec K s :=
  (polyEval A 5).coprod (((LinearMap.id : K →ₗ[K] K).smulRight (g A)).coprod
    ((diag (h A)).comp (polyEval A 2)))

noncomputable def wideProfileMap (A : Fin s→Fin s→K) :
    WideCoeffs K →ₗ[K] Vec K s :=
  (normalProfileMap A).coprod ((LinearMap.id : K →ₗ[K] K).smulRight (g A*h A))

noncomputable def wideDefect (A : Fin s→Fin s→K) (w : WideCoeffs K) : Vec K s :=
  (w.1.2.1 • g A+diag (h A) (evalNodes A (ofFn 3 w.1.2.2)))+w.2 • (g A*h A)

omit [CharZero K] in
theorem normalProfileMap_apply (A : Fin s→Fin s→K) (w : NormalCoeffs K) :
    normalProfileMap A w=evalNodes A (ofFn 6 w.1)+
      (w.2.1 • g A+diag (h A) (evalNodes A (ofFn 3 w.2.2))) := by
  rw [evalNodes_ofFn A 5,evalNodes_ofFn A 2]
  rfl

omit [CharZero K] in
theorem wideProfileMap_apply (A : Fin s→Fin s→K) (w : WideCoeffs K) :
    wideProfileMap A w=evalNodes A (ofFn 6 w.1.1)+wideDefect A w := by
  change normalProfileMap A w.1+w.2 • (g A*h A)=_
  rw [normalProfileMap_apply,wideDefect,add_assoc]

theorem wide_defect_mem {b : Vec K s} (ho : HasTreeOrderAtLeast A b 9) (w : WideCoeffs K) :
    wideDefect A w∈zeroSpace A 5 := by
  have gg := qdef_mem A
  have hh := h_in_grade_three A
  have dq : (ofFn 3 w.1.2.2).natDegree≤2 :=
    Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have q := evalNodes_mem_treeSpace A _ dq
  have wq : diag (h A) (evalNodes A (ofFn 3 w.1.2.2))∈zeroSpace A 5 :=
    zeroSpace_mul_treeSpace ho (by decide : 2+1≤9) hh q
  exact (zeroSpace A 5).add_mem
    ((zeroSpace A 5).add_mem
      ((zeroSpace A 5).smul_mem _ (zeroSpace_mono A (by decide) gg)) wq)
    ((zeroSpace A 5).smul_mem _ (zeroSpace_mul gg hh))

theorem wide_profile_mem {b : Vec K s} (ho : HasTreeOrderAtLeast A b 9) (w : WideCoeffs K) :
    wideProfileMap A w∈treeSpace A 5 := by
  rw [wideProfileMap_apply]
  exact (treeSpace A 5).add_mem
    (evalNodes_mem_treeSpace A _ (Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)))
    (zeroSpace_le_treeSpace A 5 (wide_defect_mem ho w))

/-- The top coefficient projection is genuinely linear; no degree
computation is taken as a linear operation. -/
def wideTop : WideCoeffs K →ₗ[K] K where
  toFun w := w.1.1 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharZero K] in
theorem wideTop_coeff (w : WideCoeffs K) : (ofFn 6 w.1.1).coeff 5=wideTop w := by
  exact ofFn_coeff_eq_val_of_lt _ (by decide)

omit [CharZero K] in
theorem wide_coeff_rank : finrank K (WideCoeffs K)=11 := by
  norm_num [WideCoeffs,NormalCoeffs,Module.finrank_prod,Module.finrank_fin_fun,Module.finrank_self]

omit [CharZero K] in
theorem nonzero_kernel_of_rank_lt {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (L : V →ₗ[K] W) (lt : finrank K W < finrank K V) : ∃ w, w≠0 ∧ L w=0 := by
  have notI : ¬Function.Injective L := fun inj =>
    (not_le_of_gt lt) (LinearMap.finrank_le_finrank_of_injective inj)
  have bad := mt (injective_iff_map_eq_zero L).mpr notI
  push Not at bad
  obtain ⟨w,eq,ne⟩ := bad
  exact ⟨w,ne,eq⟩

/-- The polynomial part of any relation is anchored Radau. -/
theorem wide_kernel_poly {A : Fin 12→Fin 12→K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9)
    (w : WideCoeffs K) (ker : wideProfileMap A w=0) :
    ofFn 6 w.1.1=C (wideTop w)*anchorRadau := by
  let P := ofFn 6 w.1.1
  have pd : P.natDegree≤5 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) _)
  have eq : evalNodes A P+wideDefect A w=0 := (wideProfileMap_apply A w).symm.trans ker
  have hP : evalNodes A P∈zeroSpace A 5 := by
    have e : evalNodes A P= -wideDefect A w := by
      apply add_right_cancel (b:=wideDefect A w)
      rw [eq,neg_add_cancel]
    rw [e]
    exact (zeroSpace A 5).neg_mem (wide_defect_mem ho w)
  have n0 : nodes A (0:Fin 12)=0 := by
    unfold nodes
    exact Finset.sum_eq_zero (fun j _=>ha 0 j (Fin.zero_le _))
  have p0 : P.eval 0=0 := by
    have e : evalNodes A P (0:Fin 12)=0 := origin_zeroSpace A ha 5 hP
    rwa [evalNodes_apply,n0] at e
  have pm (j : Fin 4) : probe A b j.val (evalNodes A P)=0 :=
    probe_zeroSpace ho (by have := j.isLt; omega) hP
  rw [←wideTop_coeff w]
  exact anchored_radau_span ho P pd p0 pm

end RKCert.Paired.OneOff
