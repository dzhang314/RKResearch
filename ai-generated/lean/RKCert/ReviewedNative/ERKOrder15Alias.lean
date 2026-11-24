module

public import RKCert.ReviewedNative.ERKOrder15PaidFrame

@[expose] public section

/-! # The actual order-15 alias and no-alias chart at their first grades -/
namespace RKResearch.Certified.Graded

open RKResearch Reverse Module Polynomial
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}
variable {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1)→K}

private theorem coefficient_band_in_marked_tree {a j : ℕ} (le : a≤j) :
    (coeffEval A a).range ≤ markedTreeSpace A b j := by
  rintro _ ⟨t,rfl⟩
  exact (show treeSpace A j≤markedTreeSpace A b j from le_sup_left)
    (treeSpace_mono A le (coeffEval_mem_treeSpace A a t))

private theorem coeff_eq_zero_of_polynomial_separated {j : ℕ}
    {V : Submodule K (Fin (s+1)→K)}
    (none : ∀ P : K[X],P.natDegree≤j → evalNodes A P∈V → P=0)
    (a : Fin (j+1)→K) (hv : coeffEval A j a∈V) : a=0 := by
  have eq := none (ofFn (j+1) a) (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) a))
    (by rwa [OneOff.evalNodes_ofFn])
  ext i
  have h := congrArg (fun Q:K[X]=>Q.coeff i.val) eq
  simpa only [ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero,Pi.zero_apply] using h

theorem order15_escape_separated_six (ha : ∀ i k,i ≤ k → A i k=0) (ho : HasOrder A b 15)
    (F : Order15PaidFrame A b) (a : Fin 7→K)
    (h : coeffEval A 6 a∈order15FirstEscape A b) : a=0 :=
  marked_coeff_separated ha ho F.lastActive (by have := F.size;omega) (by decide) (by decide) a
    (F.escapePaid h)

/-- A degree-seven alias already forces the first reverse seed to be zero.
The unmarked next-grade Cauchy budget separates through degree seven. -/
theorem order15_unmarked_escape_separated_seven (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (F : Order15PaidFrame A b) (z : firstSeed A b≠0)
    (a : Fin 8→K) (h : coeffEval A 7 a∈order15FirstEscape A b) : a=0 := by
  have hx : coeffEval A 7 a∈zeroSpace A 8 := by
    simpa only [markedDefectSpace,terminalMark,ite_eq_right z,sup_bot_eq] using F.escapePaid h
  exact coeff_separated_next ha ho (q:=7) (by decide) a hx

structure Order15FirstEscapeChart (A : Matrix (Fin (s+1)) (Fin (s+1)) K)
    (b : Fin (s+1)→K) (a : ℕ) (G : K[X]) : Prop where
  chartType : a=7 ∨ (a=6 ∧ firstSeed A b=0)
  degree : G.natDegree=a+1
  paid : evalNodes A G∈order15FirstEscape A b
  lowSeparation : ∀ P : K[X],P.natDegree≤a → evalNodes A P∈order15FirstEscape A b → P=0
  decomposition :
    markedTreeSpace A b (a+1)=(coeffEval A a).range ⊔ order15FirstEscape A b
  rank : finrank K (markedTreeSpace A b (a+1))=a+9+terminalDebit A b

/-- In the unique alias case the physical marked E7 is already full. With
no degree-seven alias, the physical marked E8 is full instead. The
polynomial in either chart is earned by actual stage evaluation. -/
theorem order15_first_escape_chart_of_frame (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (F : Order15PaidFrame A b) :
    ∃ (a : ℕ) (G : K[X]), Order15FirstEscapeChart A b a G := by
  let W := order15FirstEscape A b
  have low6 := eval_eq_zero_of_coeff_separated (V:=W) (order15_escape_separated_six ha ho F)
  by_cases has_alias : ∃ G : K[X],G.natDegree≤7 ∧ evalNodes A G∈W ∧ G≠0
  · obtain ⟨G,dg,gW,gn⟩:=has_alias
    have gd : G.natDegree=7 := by
      by_contra h
      exact gn (low6 G (by omega) gW)
    have mark : firstSeed A b=0 := by
      by_contra z
      exact gn (eval_eq_zero_of_coeff_separated
        (order15_unmarked_escape_separated_seven ha ho F z) G gd.le gW)
    let Q := markedDefectSpace A b 7
    have nQ : evalNodes A G∉Q := by
      intro h
      exact gn (eval_eq_zero_of_coeff_separated
        (marked_coeff_separated ha ho F.lastActive (by have := F.size;omega)
          (q:=7) (j:=7) (by decide) (by decide)) G gd.le h)
    have edge : W=Q⊔Submodule.span K {evalNodes A G} := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact sup_le (sup_le_sup le_sup_left le_rfl)
          ((Submodule.span_singleton_le_iff_mem ..).mpr gW)
      · rw [Submodule.finrank_sup_span_singleton nQ]
        have q := F.defectRank
        have w := F.escapeRank
        change finrank K Q=_ at q
        change finrank K W=_ at w
        omega
    have hW : W≤markedTreeSpace A b 7 := by
      rw [edge]
      refine sup_le (sup_le_sup (zeroSpace_le_treeSpace A 7) le_rfl)
        ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
      exact (show treeSpace A 7≤markedTreeSpace A b 7 from le_sup_left)
        (evalNodes_mem_treeSpace A G gd.le)
    have inc := sup_le (coefficient_band_in_marked_tree (A:=A) (b:=b) (a:=6) (j:=7) (by decide)) hW
    have r := rank_coeff_sup_of_separated W (order15_escape_separated_six ha ho F)
    have ww : finrank K W=8+terminalDebit A b := F.escapeRank
    have he := (Submodule.eq_of_le_of_finrank_le inc (by have := F.rankMid;omega)).symm
    exact ⟨6,G,Or.inr ⟨rfl,mark⟩,gd,gW,low6,he,F.rankMid⟩
  · have none (P : K[X]) (pd : P.natDegree≤7) (hm : evalNodes A P∈W) : P=0 := by
      by_contra ne
      exact has_alias ⟨P,pd,hm,ne⟩
    have sep := coeff_eq_zero_of_polynomial_separated none
    have wc : W≤markedTreeSpace A b 8 :=
      F.escapePaid.trans (sup_le_sup (zeroSpace_le_treeSpace A 8) le_rfl)
    have inc := sup_le (coefficient_band_in_marked_tree (A:=A) (b:=b) (a:=7) (j:=8) (by decide)) wc
    have r := rank_coeff_sup_of_separated W sep
    have ww : finrank K W=8+terminalDebit A b := F.escapeRank
    have up := F.upper 8 (by decide)
    have he := (Submodule.eq_of_le_of_finrank_le inc (by omega)).symm
    have rk : finrank K (markedTreeSpace A b 8)=16+terminalDebit A b := by rw [he,r,ww]; omega
    let X8 : K[X] := X^8
    have mx : evalNodes A X8∈markedTreeSpace A b 8 :=
      (show treeSpace A 8≤markedTreeSpace A b 8 from le_sup_left)
        (evalNodes_mem_treeSpace A X8 (by simp [X8]))
    rw [he] at mx
    obtain ⟨_,⟨a,rfl⟩,u,hu,eq⟩:=Submodule.mem_sup.mp mx
    let P := ofFn 8 a
    let G := X8-P
    have pd : P.natDegree≤7 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
    have xd : X8.natDegree=8 := by simp [X8]
    have gd : G.natDegree=8 := by
      change (X8-P).natDegree=8
      rw [natDegree_sub_eq_left_of_natDegree_lt (by omega),xd]
    have gpaid : evalNodes A G=u := by
      change evalNodes A (X8-P)=u
      have pa : evalNodes A P=coeffEval A 7 a := OneOff.evalNodes_ofFn A 7 a
      rw [map_sub,pa,←eq]
      abel
    exact ⟨7,G,Or.inl rfl,gd,gpaid.symm ▸ hu,none,he,rk⟩

/-- Exactly one alias line: once the degree-seven first escape exists,
every other paid polynomial up to degree seven is its scalar multiple. -/
theorem order15_first_escape_alias_line (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (F : Order15PaidFrame A b) {G : K[X]}
    (gd : G.natDegree=7) (gm : evalNodes A G∈order15FirstEscape A b)
    (P : K[X]) (pd : P.natDegree≤7) (pm : evalNodes A P∈order15FirstEscape A b) :
    ∃ α : K, P=C α*G := by
  have gn : G≠0 := by intro h; rw [h,natDegree_zero] at gd; contradiction
  have cn : G.coeff 7≠0 := by
    rw [←gd,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr gn
  let α := P.coeff 7/G.coeff 7
  let R := P-C α*G
  have rd : R.natDegree≤6 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro n hn
    have eq : R.coeff n=P.coeff n-α*G.coeff n := by simp [R,coeff_C_mul]
    rw [eq]
    by_cases h : n=7
    · subst n
      simp [α,div_mul_cancel₀ _ cn]
    · rw [coeff_eq_zero_of_natDegree_lt (show P.natDegree<n by omega),
        coeff_eq_zero_of_natDegree_lt (show G.natDegree<n by omega),mul_zero,sub_zero]
  have eva : evalNodes A (C α*G)=α • evalNodes A G := by ext i; simp
  have rm : evalNodes A R∈order15FirstEscape A b := by
    change evalNodes A (P-C α*G)∈_
    rw [map_sub,eva]
    exact (order15FirstEscape A b).sub_mem pm ((order15FirstEscape A b).smul_mem _ gm)
  have h := eval_eq_zero_of_coeff_separated (order15_escape_separated_six ha ho F) R rd rm
  exact ⟨α,sub_eq_zero.mp h⟩

/-- The physical first paid chart no longer has any assumed rank input. -/
theorem order15_first_escape_chart [CharZero K] (ha : ∀ i k,i ≤ k → A i k=0)
    (ho : HasOrder A b 15) (cap : s+1≤22) :
    ∃ (a : ℕ) (G : K[X]), Order15PaidFrame A b ∧ Order15FirstEscapeChart A b a G := by
  have F := order15_paid_frame ha ho cap
  obtain ⟨a,G,C⟩ := order15_first_escape_chart_of_frame ha ho F
  exact ⟨a,G,F,C⟩

end
end RKResearch.Certified.Graded
