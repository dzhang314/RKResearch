module

public import RKCert.ReviewedNative.ERKOrderTwelveReverseRows

public section

/-! # Native Appendix A: the rank-one reverse escape at order twelve

The localized quadratic line leads to a native strictly causal two-node
row system. Paid reflected moments provide an active coordinate outside
any four specified clock values, contradicting the two-node confinement.
-/
namespace RKResearch.Certified.Graded.ERK12
open RKResearch Module Reverse Reverse.TwoNode RKCert.Endpoint
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}

/-- Paid reflected moments see an active weight outside a small set of
clock values, without needing nonzero individual weights or distinct rows. -/
theorem reflected_active_avoid {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {p : ℕ} (ho : HasOrder p A b) (T : Finset K) (card : T.card<p/2) :
    ∃ i, b i≠0 ∧ reflectedClock A i∉T := by
  classical
  by_contra! all
  let U : Submodule K (Fin s → K) := ⊥
  have mask : MaskInvariant (reflectedClock A) U := by
    intro z v hv
    have e : v=0 := (Submodule.mem_bot K).mp hv
    subst v
    apply (Submodule.mem_bot K).mpr
    ext i
    simp [blockMask]
  have mass (v : Fin s → K) (hv : v∈U) : ∑ i,v i=0 := by
    have e : v=0 := (Submodule.mem_bot K).mp hv
    simp [e]
  have lower := reverse_failed_clock_blocks (r:=p/2) ho U mask mass (by omega)
  have sub : failedNodes (reflectedClock A) b U s ⊆ T := by
    intro z hz
    by_contra outside
    apply (mem_failedNodes.mp hz).2
    refine ⟨0,U.zero_mem,fun i _ same => ?_⟩
    have zero : b i=0 := by
      by_contra live
      exact outside (same ▸ all i live)
    simp [zero]
  exact (not_le_of_gt card) (lower.trans (Finset.card_le_card sub))

variable [CharZero K]

/-- Homogeneous change of feature for the one-node-supported quadratic jet. -/
theorem reduce_reverse_rows {N : (Fin s → K) →ₗ[K] (Fin s → K)} {y v d g : (Fin s → K)} {a : K}
    (ha : a≠0) (r : ReverseRows N y v d g a) :
    TwoNodeRows N y (powerWeight y v 1+(2/a) • d) (a⁻¹ • g) := by
  let h := powerWeight y v 1+(2/a) • d
  let G := a⁻¹ • g
  have hval (i) : h i=y i*v i+(2/a)*d i := by simp [h,powerWeight]
  have scaled (k:ℕ) : powerWeight y h k=powerWeight y v (k+1)+((2/a)*a^k) • d := by
    ext i
    simp only [powerWeight,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [hval]
    by_cases he : y i=a
    · rw [he]; ring
    · rw [r.support i he]; ring
  have dG : diag y G=a⁻¹ • diag y g := by ext i; simp [G]; ring
  obtain ⟨b,eb⟩:=r.cubic
  obtain ⟨q,l,eq⟩:=r.quartic
  obtain ⟨k,e,ek⟩:=r.advance
  obtain ⟨m,f,z,em⟩:=r.shifted
  change TwoNodeRows N y h G
  refine ⟨?_,⟨a*(b+2),?_⟩,⟨a*(q+2*a),a*l,?_⟩,⟨k,e,?_⟩,⟨m,f,z,?_⟩⟩
  · intro i; change N (powerWeight y v 1+(2/a) • d) i=_
    rw [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,r.quadratic,hval]
    change _= _+2*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp
    · rw [r.support i he]; field_simp; ring
  · intro i
    rw [scaled 1,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,eb,hval]
    change _= _+_*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp; ring
    · rw [r.support i he]; field_simp; ring
  · intro i
    rw [scaled 2,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,r.next,eq,hval]
    change _= _+_*(a⁻¹*g i)
    by_cases he : y i=a
    · rw [he]; field_simp; ring
    · rw [r.support i he]; field_simp; ring
  · intro i; simp only [G,map_smul,Pi.smul_apply,smul_eq_mul,ek]; ring
  · intro i; rw [dG,map_smul,Pi.smul_apply,smul_eq_mul,em]
    change _= _*(a⁻¹*g i); ring


/-- The one-dimensional actual reverse flag at level one escapes the
physical reflected clock. No assumption on a ghost or unused weight enters. -/
theorem back_one_noninvariant {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b) (S : Saturation A b) :
    ¬ (back A b 1).map (diag (reflectedClock A))≤back A b 1 := by
  classical
  intro inv
  obtain ⟨a,a0,rows⟩ := localized_reverse_rows ha ho S inv
  let y := reflectedClock A
  let d := reverseResidual A b 1
  let g := mat A.transpose d
  let h := powerWeight y b 1+(2/a) • d
  have val (i) : h i=y i*b i+(2/a)*d i := by simp [h,powerWeight]
  have loc (i) (hi : y i≠a) : d i=0 := rows.support i hi
  have zero (i) (hi : y i=0) : h i=0 := by
    rw [val,loc i (by rw [hi]; exact a0.symm),hi]
    ring
  apply two_node_confinement Fin.revPerm (mat A.transpose) (causal_transpose ha) y h
    (a⁻¹ • g) (reduce_reverse_rows a0 rows) zero
  intro t u
  let T : Finset K := {0,a,t,u}
  have card : T.card≤4 := calc
    T.card ≤ ({a,t,u}:Finset K).card+1 := Finset.card_insert_le ..
    _ ≤ (({t,u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
    _ ≤ ((({u}:Finset K).card+1)+1)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le ..) _) _
    _ = 4 := by simp
  obtain ⟨i,bi,hi⟩ := reflected_active_avoid ho T (by omega)
  have avoid : y i≠0 ∧ y i≠a ∧ y i≠t ∧ y i≠u := by
    change y i∉({0,a,t,u}:Finset K) at hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
  exact ⟨i,by rw [val,loc i avoid.2.1,mul_zero,add_zero]; exact mul_ne_zero avoid.1 bi,avoid.2.2⟩

/-- Paid annihilator duality transfers the reverse line's escape to the
original ninth tree grade, for the later forward head argument. -/
theorem saturated_e9_escape {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b) (S : Saturation A b) :
    ¬(treeSpace A 9).map (diag (nodes A))≤treeSpace A 9 :=
  tree_escape_of_reverse_escape (reverse_seven_nine ha ho S (terminal_band ha ho S)).back1
    (back_one_noninvariant ha ho S)

/-- The one remaining rank is earned by the physical forward clock
image of grade nine. Thus the actual grade-ten tree space is the entire
original stage space. -/
theorem saturated_e10_top {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b) (S : Saturation A b) :
    treeSpace A 10=⊤ := by
  have R := reverse_seven_nine ha ho S (terminal_band ha ho S)
  have out := saturated_e9_escape ha ho S
  have lo := tree_rank_lt_of_clock_escape out
  change finrank K (treeSpace A 9)<finrank K (treeSpace A 10) at lo
  have hi := S.caps 10 (by decide)
  have rank := R.e9Rank
  have size := S.size
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun K]
  omega

/-- Appendix A conclusion using only the actual order and stage cap. This
does not assert the separate final forward head contradiction. -/
theorem actual_e10_top {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b) (cap : s≤17) :
    treeSpace A 10=⊤ := by
  cases s with
  | zero =>
    have chain := RKResearch.Certified.explicit_order_le_stages ha ho
    omega
  | succ s => exact saturated_e10_top ha ho (saturation_of_order ha ho cap)

end RKResearch.Certified.Graded.ERK12
