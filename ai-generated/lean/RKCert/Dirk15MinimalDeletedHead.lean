module

public import RKCert.Dirk15MinimalCore
public import RKCert.Dirk15DeletedScalarOrbit

@[expose] public section

/-! # The two actual terminal-deleted growth directions at order fifteen

The scalar and head orbits are subspaces of the retained nineteen
positions. All grade inclusions start from full-array features. The result
does not assert a new stage bound.
-/
namespace RKCert.Paired
open Module RKCert.OneEscape Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem clock_chain_mono {n : ℕ} {V : Submodule K (Vec K n)} {C : Vec K n →ₗ[K] Vec K n}
    {w : Vec K n} : Monotone (chain C V w) := by
  intro i j ij
  apply (chain_le_iff _).mpr
  have h := (chain_le_iff (T:=C) (U:=V) (w:=w) j).mp le_rfl
  exact ⟨h.1,fun l hl => h.2 _ (hl.trans_le ij)⟩

omit [CharZero K] in
theorem deletedScalarOrbit_mono : Monotone (deletedScalarOrbit A) :=
  fun _ _ h => clock_chain_mono (Nat.add_le_add_right h 1)

omit [CharZero K] in
theorem deleted_clock_sup_extend (T : Vec K 19 →ₗ[K] Vec K 19)
    (S Z : Submodule K (Vec K 19)) :
    (S⊔Z)⊔(S⊔Z).map T=(S⊔S.map T)⊔(Z⊔Z.map T) := by
  rw [Submodule.map_sup]
  ac_rfl

namespace Order15MinimalHead
variable (h : Order15MinimalHead A b)

def length : ℕ := 6-finrank K h.U

omit [CharZero K] in
theorem length_sum : finrank K h.U+h.length=6 := by
  have p := h.high
  unfold length
  omega

omit [CharZero K] in
theorem length_pos : 0<h.length := by
  have p := h.high
  unfold length
  omega

omit [CharZero K] in
theorem length_next_pure :
    chain (diag (nodes A)) h.U h.w (h.length+1)≤zeroSpace A 8 := by
  rw [←chain_sup_map h.maximal.2.1 h.length_pos,←show zeroSpace A 7 =
    chain (diag (nodes A)) h.U h.w h.length from h.seven]
  exact sup_le (zeroSpace_mono A (by decide))
    (Submodule.map_le_iff_le_comap.mpr (diag_zeroSpace A 7))

omit [CharZero K] in
theorem length_next_unpaid : ((diag (nodes A))^h.length) h.w ∉ zeroSpace A 7 := by
  intro paid
  apply h.seven_escape
  have eq : zeroSpace A 7 = chain (diag (nodes A)) h.U h.w h.length := h.seven
  have q : chain (diag (nodes A)) h.U h.w (h.length+1)≤zeroSpace A 7 := by
    change chain (diag (nodes A)) h.U h.w h.length ⊔
      K ∙ (((diag (nodes A))^h.length) h.w) ≤ zeroSpace A 7
    exact sup_le eq.ge ((Submodule.span_singleton_le_iff_mem _ _).mpr paid)
  rw [←chain_sup_map h.maximal.2.1 h.length_pos,←eq] at q
  exact le_sup_right.trans q

omit [CharZero K] in
/-- Grade seven is unchanged in rank by deleting the true terminal, and
still splits as the images of the actual scalar and head parts. -/
theorem deleted_base (ho : HasTreeOrderAtLeast A b 15) :
    deletedTreeSpace A 7=deletedScalarOrbit A 7⊔deletedHeadOrbit A h.U h.w h.length := by
  have eq : treeSpace A 7=LinearMap.range (polyEval A 7)⊔zeroSpace A 7 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a,ha⟩ := exists_poly_zeroSpace ho (by decide : 7+1≤15) hx
      refine Submodule.mem_sup.mpr ⟨polyEval A 7 a,LinearMap.mem_range_self _ _,x-polyEval A 7 a,ha,?_⟩
      abel
    · apply sup_le _ (zeroSpace_le_treeSpace A 7)
      rintro _ ⟨a,rfl⟩
      exact polyEval_mem_treeSpace _ _ _
  rw [deletedTreeSpace,eq,Submodule.map_sup,←deletedScalarOrbit_eq,
      show zeroSpace A 7=chain (diag (nodes A)) h.U h.w h.length from h.seven,
      ←deletedHeadOrbit_eq]

omit [CharZero K] in
theorem deleted_head_rank_upper (n : ℕ) :
    finrank K (deletedHeadOrbit A h.U h.w n)≤finrank K h.U+n := by
  change finrank K (chain (diag (deleteTerminal K 19 (nodes A)))
    (h.U.map (deleteTerminal K 19)) (deleteTerminal K 19 h.w) n)≤_
  exact (chain_dim_upper n).trans (Nat.add_le_add_right
    (Submodule.finrank_map_le (deleteTerminal K 19) h.U) n)

omit [CharZero K] in
theorem deleted_scalar_rank_upper (j : ℕ) :
    finrank K (deletedScalarOrbit A j)≤j+1 := by
  rw [deletedScalarOrbit_eq]
  have r := LinearMap.finrank_range_le (polyEval A j)
  rw [Module.finrank_fin_fun] at r
  exact (Submodule.finrank_map_le (deleteTerminal K 19) _).trans r

/-- Whenever numerical saturation gives the displayed combined band,
its summands are direct. This works for either growth direction, and
does not require full-array scalar separation at grade eleven. -/
theorem deleted_direct (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) {j k n : ℕ} (lo : 7≤j) (hi : j≤11)
    (pay : k+1+finrank K h.U+n≤j+7)
    (eq : deletedTreeSpace A j=deletedScalarOrbit A k⊔deletedHeadOrbit A h.U h.w n) :
    Disjoint (deletedScalarOrbit A k) (deletedHeadOrbit A h.U h.w n) := by
  let S := deletedScalarOrbit A k
  let L := deletedHeadOrbit A h.U h.w n
  have ds := deleted_scalar_rank_upper (A:=A) k
  have dl := h.deleted_head_rank_upper n
  have e := (order15_minimal_deleted_band ha ho H j lo hi).2
  rw [eq] at e
  have r := Submodule.finrank_sup_add_finrank_inf_eq S L
  change finrank K _ + finrank K (deletedScalarOrbit A k⊓deletedHeadOrbit A h.U h.w n :
    Submodule K (Vec K 19)) = finrank K (deletedScalarOrbit A k)+finrank K (deletedHeadOrbit A h.U h.w n) at r
  rw [show S⊔L=deletedScalarOrbit A k⊔deletedHeadOrbit A h.U h.w n from rfl,e] at r
  rw [disjoint_iff_inf_le]
  exact (Submodule.finrank_eq_zero.mp (by omega)).le

set_option maxHeartbeats 1800000 in
/-- The unfolding test is membership of the next original head power in
the deleted E7. If it is present, only scalar powers can grow. If absent,
the head grows at eight and pays each subsequent unit growth. -/
theorem deleted_growth_dichotomy (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) :
    (deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∈deletedTreeSpace A 7 ∧
      ∀ k≤4, deletedTreeSpace A (7+k)=deletedScalarOrbit A (7+k)⊔
        deletedHeadOrbit A h.U h.w h.length) ∨
    (deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)∉deletedTreeSpace A 7 ∧
      ∀ k≤4, deletedTreeSpace A (7+k)=deletedScalarOrbit A 7⊔
        deletedHeadOrbit A h.U h.w (h.length+k)) := by
  let S := deletedScalarOrbit A
  let L := deletedHeadOrbit A h.U h.w
  let E := deletedTreeSpace A
  let C' := deletedClock A
  let n := h.length
  let a := (C'^n) (deleteTerminal K 19 h.w)
  have lm : Monotone L := clock_chain_mono
  have sm : Monotone S := deletedScalarOrbit_mono
  have n0 : 0<n := h.length_pos
  have Lnext : L (n+1)=L n⊔K ∙ a := rfl
  have base : E 7=S 7⊔L n := h.deleted_base ho
  have head0 : L n≤E 7 := le_sup_right.trans base.ge
  have hd : deleteTerminal K 19 (((diag (nodes A))^h.length) h.w)=a :=
    deleteTerminal_diag_pow h.w h.length
  by_cases t : a∈E 7
  · refine Or.inl ⟨hd ▸ t,?_⟩
    have folded : L (n+1)≤E 7 :=
      Lnext ▸ sup_le head0 ((Submodule.span_singleton_le_iff_mem _ _).mpr t)
    intro k k4
    induction k with
    | zero => exact base
    | succ k ih =>
      have step := order15_deleted_clock_step ha ho H (7+k) (by omega) (by omega)
      change E (7+k+1)=E (7+k)⊔(E (7+k)).map C' at step
      have sg := ih (by omega)
      change E (7+k)=S (7+k)⊔L n at sg
      have sq : S (7+k)⊔(S (7+k)).map C'=S (7+k+1) := deletedScalarOrbit_step (7+k)
      have lp : L n⊔(L n).map C'=L (n+1) := deletedHeadOrbit_step h.maximal.2.1 n0
      rw [sg,deleted_clock_sup_extend,sq,lp] at step
      change E (7+k+1)=S (7+k+1)⊔L (n+1) at step
      change E (7+k+1)=S (7+k+1)⊔L n
      rw [step]
      apply le_antisymm
      · apply sup_le le_sup_left
        exact folded.trans (base.le.trans (sup_le
          ((sm (by omega : 7≤7+k+1)).trans le_sup_left) le_sup_right))
      · exact sup_le le_sup_left ((lm (Nat.le_succ n)).trans le_sup_right)
  · refine Or.inr ⟨fun e => t (hd ▸ e),?_⟩
    let Z := S 7⊔L (n+1)
    have Z8 : Z≤E 8 := sup_le ((deletedScalarOrbit_le 7).trans (deleted_tree_mono (by decide)))
      (by
        change deletedHeadOrbit A h.U h.w (h.length+1)≤deletedTreeSpace A 8
        rw [deletedHeadOrbit_eq]
        exact Submodule.map_mono (h.length_next_pure.trans (zeroSpace_le_treeSpace A 8)))
    have lt : E 7<Z := lt_of_le_of_ne (base.le.trans
      (sup_le le_sup_left ((lm (Nat.le_succ n)).trans le_sup_right))) (fun e =>
        t (e.ge ((le_sup_right : L (n+1)≤Z) (Lnext.ge
          ((le_sup_right : (K∙a)≤L n⊔K∙a) (Submodule.subset_span rfl))))))
    have eight : E 8=Z := by
      have r7 := H.deleted_e7_rank
      have r8 := (order15_minimal_deleted_band ha ho H 8 (by decide) (by decide)).2
      have rd := Submodule.finrank_lt_finrank_of_lt lt
      change finrank K (E 7)=14 at r7
      change finrank K (E 8)=15 at r8
      exact (Submodule.eq_of_le_of_finrank_le Z8 (by omega)).symm
    have scalar8 : (S 7).map C'≤Z := eight ▸
      ((Submodule.map_mono (deletedScalarOrbit_le 7)).trans (deleted_tree_clock 7))
    have walk (k : ℕ) (p : k≤3) : E (8+k)=S 7⊔L (n+1+k) := by
      induction k with
      | zero => exact eight
      | succ k ih =>
        have step := order15_deleted_clock_step ha ho H (8+k) (by omega) (by omega)
        change E (8+k+1)=E (8+k)⊔(E (8+k)).map C' at step
        have sg := ih (by omega)
        have lp : L (n+1+k)⊔(L (n+1+k)).map C'=L (n+1+k+1) :=
          deletedHeadOrbit_step h.maximal.2.1 (by omega : 0<n+1+k)
        rw [sg,deleted_clock_sup_extend,lp] at step
        change E (8+k+1)=(S 7⊔(S 7).map C')⊔L (n+1+k+1) at step
        change E (8+k+1)=S 7⊔L (n+1+k+1)
        rw [step]
        apply le_antisymm
        · apply sup_le _ le_sup_right
          exact sup_le le_sup_left (scalar8.trans (sup_le le_sup_left
            ((lm (by omega : n+1≤n+1+k+1)).trans le_sup_right)))
        · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
    intro k k4
    cases k with
    | zero => exact base
    | succ k =>
      change E (7+(k+1))=S 7⊔L (n+(k+1))
      rw [show 7+(k+1)=8+k by omega,show n+(k+1)=n+1+k by omega]
      exact walk k (by omega)

end Order15MinimalHead
end
end RKCert.Paired
