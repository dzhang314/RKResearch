module

public import RKCert.ReviewedNative.ERKOrderTwelveTerminalBand

public section

/-! # Localize a putatively invariant native order-twelve reverse line

All reverse rows are the actual transpose and reflected powers of the
reviewed tableau. The invariant quadratic line forces a physical
one-clock support; the remaining three ranks are a single paid head.
-/
namespace RKResearch.Certified.Graded.ERK12

open RKResearch Module Reverse RKCert.OneEscape
open scoped Matrix

variable {K : Type*} [Field K] {s : ℕ}

/-- Actual reflected residual, divided by k+1 to be in primitive units. -/
def reverseResidual (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (k : ℕ) : Fin s → K :=
  ((k+1:ℕ):K)⁻¹ • reflectedStageRow A b k

theorem reverseResidual_eq (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (k : ℕ)
    (hk : ((k+1:ℕ):K)≠0) :
    reverseResidual A b k=mat A.transpose (reflectedStageWeight A b k)-
      ((k+1:ℕ):K)⁻¹ • reflectedStageWeight A b (k+1) := by
  rw [reverseResidual,reflectedStageRow,smul_sub,smul_smul,inv_mul_cancel₀ hk,one_smul]
  rfl

/-- The greatest physical index with live reflected clock has a nonzero
quadratic residual there, by strict transpose causality. -/
theorem reverse_first_pivot {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {p : ℕ}
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder p A b) (hp : 2≤p) :
    ∃ i : Fin s, reflectedClock A i≠0 ∧ b i≠0 ∧
      (∀ j, i<j → reflectedClock A j*b j=0) ∧
      reverseResidual A b 1 i= -((2:K)⁻¹)*(reflectedClock A i)^2*b i ∧
      reverseResidual A b 1 i≠0 := by
  classical
  let y := reflectedClock A
  let v := diag y b
  have live : v≠0 := by
    intro e
    apply reflected_target_ne_zero ho hp
    change row v 1=0
    rw [e]
    simp
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by
    by_contra! h
    exact live (funext h)
  let S := Finset.univ.filter (fun j : Fin s => v j≠0)
  obtain ⟨i,hi,hm⟩ := Finset.exists_max_image S id
    ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have vLive : y i*b i≠0 := (Finset.mem_filter.mp hi).2
  have before (j : Fin s) (hj : i<j) : v j=0 := by
    by_contra hn
    exact (not_le_of_gt hj) (hm j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have z : mat A.transpose v i=0 :=
    causal_transpose ha i v (fun j hj => before j (Fin.rev_lt_rev.mp hj))
  have two : (2:K)≠0 := by
    simpa using (ho.natCast_isUnit (by decide : 0<(2:ℕ)) hp).ne_zero
  have weight : reflectedStageWeight A b 1=v := by
    ext j
    simp [v,y,reflectedStageWeight,mul_comm]
  have d : reverseResidual A b 1 i=-((2:K)⁻¹)*(y i)^2*b i := by
    rw [reverseResidual_eq A b 1 (by simpa using two),weight,Pi.sub_apply,z]
    simp only [Pi.smul_apply,smul_eq_mul,reflectedStageWeight,Nat.reduceAdd,Nat.cast_ofNat,y]
    ring
  have u := mul_ne_zero_iff.mp vLive
  exact ⟨i,u.1,u.2,before,d,d ▸
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero two)) (pow_ne_zero _ u.1)) u.2⟩

private theorem join_next {U Z : Submodule K (Fin s → K)} {T : (Fin s → K) →ₗ[K] (Fin s → K)}
    (hu : U≤Z) (ht : U.map T≤Z) (hne : ¬U.map T≤U)
    (rank : finrank K Z≤finrank K U+1) : Z=U⊔U.map T := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (sup_le hu ht)
  have lt : U < U⊔U.map T := lt_of_le_of_ne le_sup_left (fun eq => hne (le_sup_right.trans eq.ge))
  have g := Submodule.finrank_lt_finrank_of_lt lt
  omega

structure LocalizedReverseChart (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) : Prop where
  first : back A b 1=K ∙ reverseResidual A b 1
  support : ∃ a : K, a≠0 ∧ ∀ i, reflectedClock A i≠a → reverseResidual A b 1 i=0
  nextOut : mat A.transpose (reverseResidual A b 1)∉back A b 1
  chart : ∀ n≤3, back A b (n+1)=chain (diag (reflectedClock A))
    (K ∙ reverseResidual A b 1) (mat A.transpose (reverseResidual A b 1)) n
  cubic : reverseResidual A b 2∈back A b 2
  quartic : reverseResidual A b 3∈back A b 3

variable [CharZero K] {A : Matrix (Fin (s+1)) (Fin (s+1)) K} {b : Fin (s+1) → K}

omit [CharZero K] in
theorem residual_mem_own_flag (S : Saturation A b) {n : ℕ} (pos : 1≤n) (pay : n≤4) :
    reverseResidual A b n∈back A b n := by
  rw [(S.backExact n pay).2]
  have e := adjointFlag_credit (A:=A) (b:=b) (monomialCredit A b) (n-1)
    (monomial_mem_credit (A:=A) (b:=b) (n-1) n (by omega))
  rw [show n-1+1=n by omega] at e
  exact (primitiveBack A b n).smul_mem _ e

/-- If the first measured reverse line is clock-invariant, its normalized
quadratic seed and the actual transpose of that seed give the full chart. -/
theorem localized_reverse_chart (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 12 A b)
    (S : Saturation A b) (hc : (back A b 1).map (diag (reflectedClock A))≤back A b 1) :
    LocalizedReverseChart A b := by
  let d := reverseResidual A b 1
  let U := K ∙ d
  let N := mat A.transpose
  let Y := diag (reflectedClock A)
  let g := N d
  let B := back A b
  have s0 : B 0=⊥ := by
    change (K ∙ firstSeed A b)=⊥
    rw [S.firstZero,Submodule.span_zero_singleton]
  have du : U=K ∙ quadraticSeed A b := by
    change (K ∙ ((2:K)⁻¹ • reflectedStageRow A b 1))=_
    rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
  have s1 : B 1=U := by
    change B 0 ⊔ (B 0).map N ⊔ (B 0).map Y ⊔ (K ∙ quadraticSeed A b)=U
    rw [s0,du]
    simp
  have hcy : U.map Y≤U := s1 ▸ hc
  have line (v : Fin (s+1) → K) : (K ∙ v).map N=K ∙ N v := by
    rw [Submodule.map_span,Set.image_singleton]
  have s2 : B 2=U⊔(K ∙ g) := by
    change B 1 ⊔ (B 1).map N ⊔ (B 1).map Y ⊔ (K ∙ quadraticSeed A b)=_
    rw [s1,←du,show U.map N=K ∙ g from line d]
    exact le_antisymm (sup_le (sup_le le_rfl (hcy.trans le_sup_left)) le_sup_left)
      (le_sup_left.trans le_sup_left)
  have rank1 := (S.backExact 1 (by decide)).1
  have rank2 := (S.backExact 2 (by decide)).1
  have next : g∉U := by
    intro hg
    have same : B 2=B 1 := by
      rw [s2,s1,sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr hg)]
    change finrank K (B 2)=2 at rank2
    rw [same,rank1] at rank2
    contradiction
  have step (n : ℕ) (lo : 2≤n) (hi : n<4) : B (n+1)=B n⊔(B n).map Y := by
    apply join_next (adjointFlag_le_succ (pairCredit A b) n)
      (adjointFlag_clock (pairCredit A b) n) (reverse_clock_escape ha ho S lo hi)
    have a := (S.backExact n (by omega)).1
    have e := (S.backExact (n+1) (by omega)).1
    change finrank K (back A b (n+1))≤finrank K (back A b n)+1
    omega
  have flag (n : ℕ) (hn : n≤3) : B (n+1)=chain Y U g n := by
    induction n with
    | zero => exact s1
    | succ n ih =>
      by_cases hn0 : n=0
      · subst n
        simpa [chain] using s2
      · rw [step (n+1) (by omega) (by omega),ih (by omega),clock_chain_next hcy (by omega)]
  have hd : d∈U := Submodule.mem_span_singleton_self _
  obtain ⟨a,ae⟩ := Submodule.mem_span_singleton.mp (hcy (Submodule.mem_map_of_mem hd))
  have loc (i : Fin (s+1)) (hi : reflectedClock A i≠a) : d i=0 := by
    have e := congrFun ae i
    change a*d i=reflectedClock A i*d i at e
    exact (mul_eq_zero.mp (show (a-reflectedClock A i)*d i=0 by rw [sub_mul,e,sub_self])).resolve_left
      (sub_ne_zero.mpr hi.symm)
  obtain ⟨i,hi,_,_,_,di⟩ := reverse_first_pivot ha ho (by decide)
  have a0 : a≠0 := by
    intro az
    exact di (loc i (az ▸ hi))
  refine ⟨s1,⟨a,a0,loc⟩,?_,flag,residual_mem_own_flag S (by decide) (by decide),
    residual_mem_own_flag S (by decide) (by decide)⟩
  change g∉B 1
  rwa [s1]

end RKResearch.Certified.Graded.ERK12
