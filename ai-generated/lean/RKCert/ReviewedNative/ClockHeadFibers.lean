module

public import RKCert.ReviewedNative.ClockBlockDetection
public import RKCert.ReviewedNative.NativeClockStaircase
public import RKCert.ReviewedNative.GradedProducts

@[expose] public section

/-! # Localising a clock head modulo its invariant part
Only clock blocks whose head slice lies outside the core count. This avoids
constructing a second, fibre-normalised representative before proving that
the core is multiplicatively closed. -/
namespace RKResearch.Certified.Graded
namespace HeadFiber

open RKCert.OneEscape RKCert.Endpoint Polynomial Module
open scoped Classical Matrix
variable {K : Type*} [Field K] {s n : ℕ} {c w x : Fin s → K}
variable {U : Submodule K (Fin s → K)}

@[simp] theorem clock_power_value (c w : Fin s → K) (n : ℕ) (i : Fin s) :
    (diag c ^ n) w i = c i^n*w i := by
  rw [diag,LinearMap.pow_mulLeft]
  rfl

private theorem weighted_monomial (c w : Fin s → K) (k : ℕ) (a : K) :
    weightedEval c w (monomial k a) = a • (diag c^k) w := by
  ext i; simp [mul_assoc]

/-- The polynomial part is bounded by the number of included powers. -/
theorem exists_poly (hx : x∈chain (diag c) U w n) :
    ∃ u∈U, ∃ P : K[X], P.degree < (n : WithBot ℕ) ∧ x=u+weightedEval c w P := by
  induction n generalizing x with
  | zero =>
    exact ⟨x,hx,0,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u,hu,P,hd,eq⟩ := ih ha
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hb
    refine ⟨u,hu,P+monomial n t,?_,?_⟩
    · have lt : (n : WithBot ℕ) < ((n+1:ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n
      exact (degree_add_le _ _).trans_lt (max_lt (hd.trans lt) ((degree_monomial_le _ _).trans_lt lt))
    · rw [eq,map_add,weighted_monomial,add_assoc]

/-- Nonzero blocks in the quotient by U; mere nonzero coordinates in an
already-paid invariant block are deliberately not counted. -/
noncomputable def escapeSites (c w : Fin s → K) (U : Submodule K (Fin s → K)) : Finset K := by
  classical exact (Finset.univ.image c).filter (fun z => blockMask c z w ∉ U)

private theorem mem_escape_at {i : Fin s} (h : blockMask c (c i) w ∉ U) :
    c i ∈ escapeSites c w U := by
  classical exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem c (Finset.mem_univ _),h⟩

/-- Every degree-n clock head with another unpaid clock iterate requires
strictly more than n numerical sites escaping the core. -/
theorem more_escape_sites (stable : U.map (diag c) ≤ U) (pos : 0<n)
    (outside : ¬ (chain (diag c) U w n).map (diag c) ≤ chain (diag c) U w n) :
    n < (escapeSites c w U).card := by
  classical
  let F := chain (diag c) U w n
  let S := escapeSites c w U
  have hF := (clock_chain_le_iff (T:=diag c) (U:=U) (w:=w) n).mp le_rfl
  have unpaid : (diag c^n) w ∉ F := by
    intro h
    apply outside
    apply (le_sup_right : F.map (diag c) ≤ F⊔F.map (diag c)).trans
    change chain (diag c) U w n ⊔ _ ≤ _
    rw [clock_chain_next stable pos,chain]
    exact sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).2 h)
  by_contra! small
  let P := Lagrange.interpolate S id (fun z => z^n)
  have matchP (z : K) (hz : z∈S) : P.eval z=z^n :=
    Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) hz
  have deg : P.natDegree < n := by
    by_cases h : P=0
    · simpa [h] using pos
    exact ((natDegree_lt_iff_degree_lt h).2
      (Lagrange.degree_interpolate_lt (fun z:K=>z^n) (Set.injOn_id _))).trans_le small
  have polyMem : weightedEval c w P ∈ F := by
    rw [P.as_sum_range' n deg,map_sum]
    exact F.sum_mem (fun k hk => by rw [weighted_monomial]; exact F.smul_mem _ (hF.2 k (Finset.mem_range.mp hk)))
  let g (z : K) := if blockMask c z w ∈ U then (z^n-P.eval z) • blockMask c z w else 0
  have hg (z : K) : g z ∈ U := by
    dsimp only [g]
    split
    next h => exact U.smul_mem _ h
    next => exact U.zero_mem
  have mask := clock_mask_invariant (fun v (hv : v∈U) => stable (Submodule.mem_map_of_mem hv))
  have corr := assembleBlocks_mem c mask g hg
  have ident : (diag c^n) w = assembleBlocks c g + weightedEval c w P := by
    ext i
    rw [clock_power_value,Pi.add_apply,assembleBlocks_apply,weightedEval_apply]
    by_cases h : blockMask c (c i) w ∈ U
    · simp [g,h,blockMask]; ring
    · rw [matchP _ (mem_escape_at h)]
      simp [g,h]
  exact unpaid (ident ▸ F.add_mem (hF.1 corr) polyMem)

/-- A column supported at a single clock, lying in a long enough head
chart, belongs to its core. The quotient-fibre convention makes a
normalisation hypothesis unnecessary. -/
theorem localized_mem (stable : U.map (diag c) ≤ U)
    (many : n < (escapeSites c w U).card) (hx : x∈chain (diag c) U w n)
    {z : K} (localAt : ∀ i, c i ≠ z → x i=0) : x∈U := by
  classical
  obtain ⟨u,hu,P,d,expr⟩ := exists_poly hx
  let S := (escapeSites c w U).erase z
  have hc : n ≤ S.card := le_trans (by omega) (Finset.pred_card_le_card_erase (s:=escapeSites c w U) (a:=z))
  have mask := clock_mask_invariant (fun v (hv : v∈U) => stable (Submodule.mem_map_of_mem hv))
  have van (a : K) (ha : a∈S) : P.eval a=0 := by
    have ha' := Finset.mem_erase.mp ha
    have eq : P.eval a • blockMask c a w = -blockMask c a u := by
      ext i
      by_cases hi : c i=a
      · have zero := localAt i (hi ▸ ha'.1)
        have val := congrFun expr i
        rw [zero,Pi.add_apply,weightedEval_apply,hi] at val
        simpa [blockMask,hi] using (eq_neg_of_add_eq_zero_right val.symm)
      · simp [blockMask,hi]
    by_contra h
    apply (Finset.mem_filter.mp ha'.2).2
    apply (U.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr h)).mp
    rw [eq]; exact U.neg_mem (mask a u hu)
  have pz := eq_zero_of_degree_lt_of_eval_finset_eq_zero S
    (d.trans_le (by exact_mod_cast hc)) van
  simpa [expr,pz] using hu

/-- The product of a core vector and a true lower-grade defect cannot
leave the core when the genuine product grade has the displayed chart. -/
theorem core_mul {A : Matrix (Fin s) (Fin s) K} {j k : ℕ}
    (stable : U.map (diag (nodes A)) ≤ U) (inside : U ≤ zeroSpace A j)
    (many : n < (escapeSites (nodes A) w U).card)
    (band : zeroSpace A (j+k) ≤ chain (diag (nodes A)) U w n)
    {u v : Fin s → K} (hu : u∈U) (hv : v∈zeroSpace A k) : u*v∈U := by
  let c := nodes A
  have mask := clock_mask_invariant (fun t (ht : t∈U) => stable (Submodule.mem_map_of_mem ht))
  let g (z : K) := blockMask c z u * v
  have each (z : K) : g z∈U := by
    apply localized_mem stable many (band (zeroSpace_mul (inside (mask z u hu)) hv)) (z:=z)
    intro i h
    simp [blockMask, h]
  have eq : assembleBlocks c g=u*v := by ext i; simp [g,blockMask]
  exact eq ▸ assembleBlocks_mem c mask g each

end HeadFiber
end RKResearch.Certified.Graded
