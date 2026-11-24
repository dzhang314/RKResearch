module
public import RKCert.ReviewedNative.OrderNineGradeFive
public import RKCert.ReviewedNative.OrderedNodalGain
public import RKCert.ReviewedNative.ClockBlockDetection
public import RKCert.ReviewedNative.ReflectedPolynomialBudget

@[expose] public section

/-! # The terminal unit spends the anchored reverse rank slot at order nine -/
namespace RKResearch.Certified.Graded.OneOff
open RKResearch Module Polynomial Reverse RKCert.Endpoint
open scoped Classical Matrix

variable {K : Type*} [Field K] [CharZero K] {s p : ℕ}

/-- Three paid reflected power moments fail on at least two nonzero
clock blocks. Only the jointly masked lift lemma is used. -/
theorem two_failed_of_three_moments (c v : Fin s → K) (U : Submodule K (Fin s → K))
    (hm : MaskInvariant c U) (hmass : ∀u∈U, ∑i,u i=0)
    (m1 : ∑i,(c i)^1*v i=1/2) (m2 : ∑i,(c i)^2*v i=1/3)
    (m3 : ∑i,(c i)^3*v i=1/4) :
    2 ≤ (failedNodes c v U s).card := by
  classical
  by_contra! h
  obtain ⟨a,ha⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega :
    (failedNodes c v U s).card≤1)
  have placed (Q : K[X]) (h0 : Q.eval 0=0) (hA : Q.eval a=0) :
      weightedEval c v Q ∈ U := by
    obtain ⟨w,hw,hh⟩ := exists_masked_prefix_lift c v hm s Q h0 (fun z hz => by
      have e := Finset.mem_singleton.mp (ha hz)
      simpa only [e] using hA)
    have he : w=weightedEval c v Q := by
      ext i
      simpa only [weightedEval_apply] using hh i i.isLt
    exact he ▸ hw
  have h₂ := hmass _ (placed (X*(X-C a)) (by simp) (by simp))
  have h₃ := hmass _ (placed (X^2*(X-C a)) (by simp) (by simp))
  have k2 : ((∑i, c i^2*v i) - a*(∑i,c i*v i))=0 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    convert h₂ using 1
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  have k3 : ((∑i, c i^3*v i) - a*(∑i,c i^2*v i))=0 := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    convert h₃ using 1
    apply Finset.sum_congr rfl
    intro i _
    simp
    ring
  simp only [pow_one] at m1
  rw [m1,m2] at k2
  rw [m2,m3] at k3
  apply (one_ne_zero : (1:K)≠0)
  linear_combination 36*k3-24*k2

variable {T : Matrix (Fin s) (Fin s) K} {w : Fin s → K}

/-- The native backwards primitive residual lies in the annihilator at
exactly the monomial moment budget. -/
theorem reverse_primitive_paid (ho : HasOrder T w p) (j : ℕ) (P : K[X]) (q : ℕ)
    (dP : P.natDegree ≤ q) (pay : j+q+2 ≤ p) :
    mat T.transpose (weightedEval (reflectedClock T) w P) -
      weightedEval (reflectedClock T) w (primitive P) ∈ annih (treeSpace T j) := by
  let W := weightedEval (reflectedClock T) w
  let D := (mat T.transpose).comp W-W.comp primitive
  have evalm (n : ℕ) (a : K) : W (monomial n a)=a • reflectedStageWeight T w n := by
    ext i
    simp only [W,weightedEval_apply,eval_monomial,Pi.smul_apply,smul_eq_mul,reflectedStageWeight]
    ring
  have mem (n : ℕ) (hn : n ≤ q) (a : K) :
      D (monomial n a) ∈ annih (treeSpace T j) := by
    have u : ((n+1:ℕ):K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have d := reflectedStageRow_annih ho j n (by omega)
    have v := (annih (treeSpace T j)).smul_mem (a/((n+1:ℕ):K)) d
    rw [reflectedStageRow,smul_sub,smul_smul,div_mul_cancel₀ _ u] at v
    change mat T.transpose (W (monomial n a)) - W (primitive (monomial n a)) ∈ _
    rw [primitive_monomial,evalm,evalm,map_smul]
    exact v
  change D P ∈ _
  rw [P.as_sum_range' (q+1) (by omega),map_sum]
  exact (annih (treeSpace T j)).sum_mem
    (fun n hn => mem n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) _)

variable {A : Matrix (Fin 12) (Fin 12) K} {b : Fin 12 → K}

theorem order9_grade_five_clock_noninvariant (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder A b 9) (full : finrank K (treeSpace A 5)=10) :
    ¬ (treeSpace A 5).map (diag (nodes A)) ≤ treeSpace A 5 := by
  intro inv
  let U := annih (treeSpace A 5)
  let last : Fin 12 := Fin.last 11
  let Z := zeroAt (annih (treeSpace A 4)) last
  let c := reflectedClock A
  have after (i : Fin 12) (hi : last < i) : False := by
    change 11 < i.val at hi
    have bound := i.isLt
    omega
  obtain ⟨_,one,v5,v4,_,_⟩ := orderNine_rank_five_full ha ho full
  have uZ : U ≤ Z := by
    intro w hw
    exact mem_zeroAt.mpr
      ⟨annih_antitone (treeSpace_mono A (by decide : 4≤5)) hw,
        (row_coordinate w last).symm.trans (mem_annih.mp hw _ v5)⟩
  have move (v : Fin 12 → K) (hv : v∈U) : mat A.transpose v∈Z := by
    apply mem_zeroAt.mpr
    refine ⟨annih_map_transpose (mat_treeSpace A 4) (Submodule.mem_map_of_mem hv),?_⟩
    exact transpose_tail_zero ha (t:=last) (fun i hi=> (after i hi).elim) le_rfl
  have clock (v : Fin 12 → K) (hv : v∈U) : diag c v ∈ U := by
    have e : diag c v = v-diag (nodes A) v := by
      ext i
      simp only [c,reflectedClock,diag_apply,Pi.sub_apply,Pi.one_apply,sub_mul,one_mul]
    rw [e]
    exact U.sub_mem hv (annih_map_diag (Submodule.map_le_iff_le_comap.mp inv)
      (Submodule.mem_map_of_mem hv))
  have mas (v : Fin 12 → K) (hv : v∈U) : ∑i,v i=0 := by
    simpa only [row_apply,dotProduct,Pi.one_apply,mul_one] using
      mem_annih.mp hv _ (one_mem_treeSpace A 5)
  have mm (k : ℕ) (pay : k+1≤9) :
      ∑i,(c i)^k*b i = ((k+1:ℕ):K)⁻¹ := by
    have e : (∑i,(c i)^k*b i)=reflectedProbe A b 0 k 1 := by
      simp only [row_apply,dotProduct,Pi.one_apply,pow_zero,mul_one,c]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e,←one_div]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))).mpr
    simpa only [mul_comm] using reflected_power_mass ho k pay
  have mask := clock_mask_invariant clock
  have fail := two_failed_of_three_moments c b U mask mas
    (by simpa [one_div] using mm 1 (by decide))
    (by simpa [one_div] using mm 2 (by decide))
    (by simpa [one_div] using mm 3 (by decide))
  have pay (P : K[X]) (hP : P.natDegree+1≤2*2) :
      mat A.transpose (weightedEval c b P)-weightedEval c b (primitive P)∈Z := by
    apply mem_zeroAt.mpr
    refine ⟨reverse_primitive_paid ho 4 P 3 (by omega) (by decide),?_⟩
    have zz : mat A.transpose (weightedEval c b P) last=0 :=
      transpose_tail_zero ha (t:=last) (fun i hi=> (after i hi).elim) le_rfl
    have cc : c last=0 := by
      change (1:K)-nodes A (Fin.last 11)=0
      rw [one,sub_self]
    have ep : (primitive P).eval 0=0 := by rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]
    rw [Pi.sub_apply,zz,weightedEval_apply,cc,ep,zero_mul,sub_zero]
  have shrink := ordered_hermite_outgoing Fin.revPerm _ (causal_transpose ha)
    c b U Z mask uZ move 2 fail pay
  have E4 := (order9_forward_chart ha ho (by decide)).2.2.2.2
  have uR := finrank_annih (treeSpace A 5)
  have wR := finrank_annih (treeSpace A 4)
  have zR : finrank K Z+1=finrank K (annih (treeSpace A 4)) :=
    finrank_zeroAt_annih (treeSpace A 4) last v4
  rw [Fintype.card_fin] at uR wR
  change finrank K (treeSpace A 5)+finrank K U=12 at uR
  omega

end RKResearch.Certified.Graded.OneOff
