module

public import RKCert.DirkCleanDonors

@[expose] public section

namespace RKCert.Paired.Reduce
open RKCert.Paired.Clock RKCert.Endpoint Polynomial
open scoped Classical
noncomputable section

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}
variable {A : Fin s → Fin s → K} {b : Vec K s}
variable {U : Submodule K (Vec K s)} {w : Vec K s} {P : K[X]}

local notation "B" => foldMatrix A w U
local notation "c" => nodes A
local notation "D" => restrict c w U
local notation "R" => commutatorMatrix B c

omit [CharZero K] in
theorem folded_diag_at_zero_pivot (ha : LowerArray A) {v : Vec K s} {i : Fin s}
    (hpre : ∀ j < i,v j=0) (hvin : v i≠0) (hR : mat R v i=0) : B i i=0 := by
  rw [mat_commutatorMatrix,commutatorR_leading (foldMatrix_lower ha) hpre] at hR
  exact sq_eq_zero_iff.mp (neg_eq_zero.mp ((mul_eq_zero.mp hR).resolve_right hvin))

/-- A dirty pivot after k+3 dirty predecessors has a paid trace with global
zero commutator. One clean intervening row can be corrected only at k=1. -/
theorem dirty_pivot_input (h : Grade3Head A U w P) (ha : LowerArray A)
    {k : ℕ} (hk : k≤1) (d : Fin (3+k) → Fin s)
    (hd : Function.Injective d) (hDirty : ∀ j, Dirty c w U (d j))
    {i : Fin s} (hi : Dirty c w U i) (hChron : ∀ j,d j < i)
    (hCover :
      (∀ j < i, Kept c w U j → j∈Set.range d) ∨
      (k=1 ∧ ∃ u < i, Clean c w U u ∧ P.eval (c u)≠0 ∧
        ∀ j < i, Kept c w U j → j∈Set.range d ∨ j=u)) :
    ∃ v : Vec K s, v i≠0 ∧ (∀ j < i,v j=0) ∧ mat R v=0 ∧ B i i=0 := by
  let S : Finset K := Finset.univ.image (fun j => c (d j))
  let V := nodalHull S
  have hIn : Function.Injective (fun j => c (d j)) :=
    fun i j e => hd (dirty_distinct h (hDirty i) (hDirty j) e)
  have hdV : V.natDegree≤3+k := by
    rw [natDegree_nodalHull,Finset.card_image_of_injective _ hIn,Finset.card_univ,
      Fintype.card_fin]
  obtain ⟨f,hf,v,ht,hv⟩ := realize_dirty h (by omega) V hdV
  have zero (j : Fin (3+k)) : D v (d j)=0 :=
    (hv _ (hDirty j)).trans (nodalHull_eval_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  have val : D v i≠0 := by
    rw [hv _ hi]
    have ho : c i∉S := by
      intro hmem
      obtain ⟨j,_,he⟩ := Finset.mem_image.mp hmem
      exact (ne_of_lt (hChron j)) (dirty_distinct h (hDirty j) hi he)
    simp only [V,nodalHull,eval_prod,eval_sub,eval_X,eval_C,Finset.prod_ne_zero_iff]
    exact fun z hz => sub_ne_zero.mpr (Ne.symm (ne_of_mem_of_not_mem hz ho))
  have run {F : K[X]} {y : Vec K s} (ht : OrdinaryTrace A (3+k) y F) (hF0 : F.eval 0=0)
      (hy : D y i≠0) (hpre : ∀ j < i, D y j=0) :
      ∃ v : Vec K s, v i≠0 ∧ (∀ j < i,v j=0) ∧ mat R v=0 ∧ B i i=0 := by
    have hc : mat R (D y)=0 := by
      rw [mat_commutatorMatrix]
      apply reduced_commutator_zero h hk ht hF0 d hd (by omega) hDirty
      intro j
      rw [←mat_commutatorMatrix]
      exact mat_zero_before (commutatorMatrix_lower (foldMatrix_lower ha)) hpre _ (hChron j)
    exact ⟨D y,hy,hpre,hc,folded_diag_at_zero_pivot ha hpre hy
      (by rw [hc,Pi.zero_apply])⟩
  rcases hCover with cover|⟨rfl,u,_,hu,hPu,cover⟩
  · apply run ht hf val
    intro j hj
    by_cases hkept : Kept c w U j
    · obtain ⟨r,rfl⟩ := cover j hj hkept
      exact zero r
    · simp [restrict_apply,hkept]
  · obtain ⟨θ,hθ,hval⟩ := clean_contrast h
    let x := diag c θ
    have hx := hθ.clock
    have hX (j : Fin s) (hj : Dirty c w U j) : D x j=0 := by
      simp [x,restrict_apply,hj.1,hval j,hj.2]
    have hcX : D x u≠0 := by
      rw [restrict_apply,ite_eq_left hu.1]
      simp only [x,diag_apply,hval u,hu.1.1.1,hu.2,ne_eq,not_true_eq_false,or_self,ite_false]
      exact mul_ne_zero (clean_clock hu) hPu
    let t : K := -(D v u)/(D x u)
    have htr := ht.add (hx.smul t)
    have htr0 : (f+C t*(X*P)).eval 0=0 := by simp [hf]
    have hDx (j : Fin s) : D (v+t • x) j = D v j+t*D x j := by
      rw [map_add,map_smul]
      rfl
    apply run htr htr0
    · change D (v+t • x) i≠0
      simpa only [hDx,hX i hi,mul_zero,add_zero] using val
    · intro j hj
      change D (v+t • x) j=0
      by_cases hkept : Kept c w U j
      · rcases cover j hj hkept with ⟨r,rfl⟩|rfl
        · simp only [hDx,zero r,hX _ (hDirty r),mul_zero,add_zero]
        · rw [hDx]
          dsimp [t]
          rw [div_mul_cancel₀ _ hcX,add_neg_cancel]
      · simp [restrict_apply,hkept]

omit [CharZero K] in
/-- A lower triangular row with a zero prefix input has only its one pivot
tap left if the intermediate products and the diagonal are zero. -/
theorem selected_prefix_tap {M : Matrix (Fin s) (Fin s) K} (ha : LowerArray M)
    {v : Vec K s} {i j : Fin s} (hij : j < i) (hpre : ∀ k < j,v k=0)
    (hdiag : M i i=0)
    (hmid : ∀ k, j < k → k < i → M i k=0 ∨ v k=0) :
    mat M v i=M i j*v j := by
  apply row_single_tap
  intro k hne
  rcases lt_or_gt_of_ne hne with h|h
  · exact Or.inr (hpre _ h)
  · rcases lt_trichotomy k i with h'|rfl|h'
    · exact hmid _ h h'
    · exact Or.inl hdiag
    · exact Or.inl (ha _ _ h')

/-- For any paid profile identically zero at the first clean row and its
primitive, four exact dirty taps permit matching all four donor values
with a genuine quadratic head correction. -/
theorem fit_four_donors (h : Grade3Head A U w P) (ha : LowerArray A)
    {u : Fin s} (hu : Clean c w U u) (hpre : ∀ j < u,¬Clean c w U j)
    (hcard : (beforeDirty A w U u).card=4)
    (f : K[X]) (hd : f.natDegree≤5) (f0 : f.eval 0=0)
    (hf : f.eval (c u)=0) (hJ : (formalPrimitive f).eval (c u)=0) :
    ∃ q : K[X], q.natDegree≤2 ∧
      ∀ j∈beforeDirty A w U u, f.eval (c j)+q.eval (c j)*w j=0 := by
  let T := beforeDirty A w U u
  obtain ⟨i,hi,hiB⟩ := some_clean_tap h ha hu hpre
  let S := T.erase i
  have hc : S.card≤3 := by
    have hh := Finset.card_erase_add_one hi
    change S.card+1=T.card at hh
    change T.card=4 at hcard
    omega
  have hI : Set.InjOn c S := fun x hx y hy e =>
    dirty_distinct h (mem_beforeDirty.mp (Finset.mem_of_mem_erase hx)).2
      (mem_beforeDirty.mp (Finset.mem_of_mem_erase hy)).2 e
  obtain ⟨q,hq,he⟩ := exists_polynomial_interpolate S c hI
    (fun j => -(f.eval (c j))/w j) (d:=2) hc
  have hz (j : Fin s) (hj : j∈S) : f.eval (c j)+q.eval (c j)*w j=0 := by
    rw [he _ hj,div_mul_cancel₀ _ (mem_beforeDirty.mp (Finset.mem_of_mem_erase hj)).2.2,
      add_neg_cancel]
  let v := evalNodes A f+(fun j => q.eval (c j)*w j)
  have htr : OrdinaryTrace A 5 v f := head_trace h (k:=2) (by decide) f q hd hq
  have ev := fold_clean_value h (n:=5) (by decide) (by decide) htr f0 hu
  rw [hJ,row_restrict_sum B u _ T ?_] at ev
  · rw [Finset.sum_eq_single_of_mem i hi] at ev
    · have hkept := (mem_beforeDirty.mp hi).2.1
      rw [restrict_apply,ite_eq_left hkept] at ev
      refine ⟨q,hq,fun j hj => ?_⟩
      by_cases e : j=i
      · subst j
        exact (mul_eq_zero.mp ev).resolve_left hiB
      · exact hz j (Finset.mem_erase.mpr ⟨e,hj⟩)
    · intro j hj hne
      have hk := (mem_beforeDirty.mp hj).2.1
      rw [restrict_apply,ite_eq_left hk]
      exact mul_eq_zero.mpr (Or.inr (hz _ (Finset.mem_erase.mpr ⟨hne,hj⟩)))
  · intro j hj
    rcases lt_trichotomy j u with hl|rfl|hl
    · by_cases hk : Kept c w U j
      · rcases clean_or_dirty hk with hcl|hdi
        · exact (hpre _ hl hcl).elim
        · exact (hj (mem_beforeDirty.mpr ⟨hl,hdi⟩)).elim
      · exact Or.inl (foldMatrix_zero_col hk)
    · right
      rw [restrict_apply,ite_eq_left hu.1]
      simp [v,hf,hu.2]
    · exact Or.inl (foldMatrix_lower ha _ _ hl)

end
end RKCert.Paired.Reduce
