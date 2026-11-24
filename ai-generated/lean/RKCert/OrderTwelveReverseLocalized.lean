module
public import RKCert.OrderTwelveReverseChart

@[expose] public section

/-! # Physical rank-one reduction for the reversed order-twelve tableau

The clock, transpose, and weight vector are the actual ones. The suffixes
are read from right to left; no density or sign hypotheses on the weights
are used. L2, L3, L4 and L5 have zero-based indices one through four.
-/
namespace RKCert.Paired.OrderTwelve
open RKCert.Paired RKCert.Paired.ReverseHull RKCert.OneEscape Module
variable {K : Type*} [Field K] {s : ℕ}

/-- Primitive residual of power k, normalized by k+1 to match formal integration. -/
def reverseResidual (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ) : Vec K s :=
  ((k+1:ℕ):K)⁻¹ • reflected A b k

theorem reverseResidual_eq (A : Fin s → Fin s → K) (b : Vec K s) (k : ℕ)
    (hk : ((k+1:ℕ):K)≠0) :
    reverseResidual A b k=transMat A (reflWeight A b k)-
      ((k+1:ℕ):K)⁻¹ • reflWeight A b (k+1) := by
  rw [reverseResidual,reflected,smul_sub,smul_smul,inv_mul_cancel₀ hk,one_smul]

theorem reflected_one_seed (A : Fin s → Fin s → K) (b : Vec K s) :
    reflected A b 1=backSeed2 A b := by
  have h1 : reflWeight A b 1=diag (mirror A) b := by
    ext i; simp [reflWeight,reflNode,mirror]
  have h2 : reflWeight A b 2=diag (mirror A) (diag (mirror A) b) := by
    ext i; simp [reflWeight,reflNode,mirror,pow_two,mul_assoc]
  change (2:K) • transMat A (reflWeight A b 1) - reflWeight A b 2 = _
  rw [h1,h2]; rfl

theorem reverseResidual_mem {A : Fin s → Fin s → K} {b : Vec K s} {p j k : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hk:k≤3) (hp:j+k+2≤p) :
    reverseResidual A b k∈annih (treeSpace A j) :=
  (annih _).smul_mem _ (reflected_annih ho hk hp)

theorem back_map_transpose (A : Fin s → Fin s → K) (b : Vec K s) (n : ℕ) :
    (back A b n).map (transMat A) ≤ back A b (n+1) :=
  le_sup_right.trans (le_sup_left.trans le_sup_left)

theorem back_map_clock (A : Fin s → Fin s → K) (b : Vec K s) (n : ℕ) :
    (back A b n).map (diag (mirror A)) ≤ back A b (n+1) := le_sup_right.trans le_sup_left

private theorem join_next {U Z : Submodule K (Vec K s)} {T : Vec K s →ₗ[K] Vec K s}
    (hu : U≤Z) (ht : U.map T≤Z) (hne : ¬U.map T≤U)
    (hr : finrank K Z≤finrank K U+1) : Z=U⊔U.map T := by
  symm; apply Submodule.eq_of_le_of_finrank_le (sup_le hu ht)
  have hlt : U < U⊔U.map T := lt_of_le_of_ne le_sup_left (fun he => hne (le_trans le_sup_right he.ge))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-- The first genuinely active reflected nonzero clock has a nonzero quadratic residual.
In physical indexing this is the *greatest* such active index, not necessarily the last row. -/
theorem reverse_first_pivot {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hp : 2≤p) :
    ∃ i : Fin s, mirror A i≠0 ∧ b i≠0 ∧
      (∀ j, i<j → mirror A j*b j=0) ∧
      reverseResidual A b 1 i= -((2:K)⁻¹)*(mirror A i)^2*b i ∧
      reverseResidual A b 1 i≠0 := by
  classical
  let y := mirror A
  let v := diag y b
  have ht : v≠0 := by
    intro h
    apply back_target_nonzero ho hp
    change row v 1=0
    rw [h]
    simp [row_apply]
  obtain ⟨i,hi⟩ : ∃ i, v i≠0 := by
    by_contra! h
    exact ht (funext h)
  let S := Finset.univ.filter (fun j : Fin s => v j≠0)
  obtain ⟨i,hi,hm⟩ := Finset.exists_max_image S id ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hv : y i*b i≠0 := (Finset.mem_filter.mp hi).2
  have hbefore (j : Fin s) (hj : i<j) : v j=0 := by
    by_contra hn
    exact (not_le_of_gt hj) (hm j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have hz : transMat A v i=0 := causal_transpose ha i v (fun j hj => hbefore j (Fin.rev_lt_rev.mp hj))
  have htwo : (2:K)≠0 := by simpa using cast_ne_zero_of_budget ho (n:=2) (by decide) hp
  have hd : reverseResidual A b 1 i= -((2:K)⁻¹)*(y i)^2*b i := by
    simp only [reverseResidual,reflected_one_seed,backSeed2,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
    change (2:K)⁻¹*(2*transMat A v i-y i*(y i*b i))=_
    rw [hz]
    ring
  have hh := mul_ne_zero_iff.mp hv
  exact ⟨i,hh.1,hh.2,hbefore,hd,hd ▸ mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero htwo)) (pow_ne_zero _ hh.1)) hh.2⟩

/-- Linear-algebra output for a putatively invariant reverse quadratic line. -/
structure LocalizedReverseChart (A : Fin s → Fin s → K) (b : Vec K s) : Prop where
  first : back A b 1=K ∙ reverseResidual A b 1
  support : ∃ a : K, a≠0 ∧ ∀ i, mirror A i≠a → reverseResidual A b 1 i=0
  next_out : transMat A (reverseResidual A b 1)∉back A b 1
  chart : ∀ n≤3, back A b (n+1)=
    chain (diag (mirror A)) (K ∙ reverseResidual A b 1) (transMat A (reverseResidual A b 1)) n
  cubic : reverseResidual A b 2∈back A b 2
  quartic : reverseResidual A b 3∈back A b 3

variable [CharZero K]

/-- A localized L2 at true order twelve has one real physical quadratic seed and
one transpose-born head, with no other directions available through L5. -/
theorem localized_reverse_chart {A : Fin (s+1) → Fin (s+1) → K} {b : Vec K (s+1)}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 12) (hs : Saturation A b)
    (hc : (back A b 1).map (diag (mirror A))≤back A b 1) : LocalizedReverseChart A b := by
  let d := reverseResidual A b 1
  let U := K ∙ d
  let N := transMat A
  let Y := diag (mirror A)
  let g := N d
  let B := back A b
  have s0 : B 0=⊥ := by
    change Submodule.span K {backSeed1 A b}=⊥
    rw [hs.backZero,Submodule.span_zero_singleton]
  have du : U=K ∙ backSeed2 A b := by
    change (K ∙ ((2:K)⁻¹ • reflected A b 1))=_
    rw [reflected_one_seed,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
  have s1 : B 1=U := by
    change B 0 ⊔ (B 0).map N ⊔ (B 0).map Y ⊔ (K ∙ backSeed2 A b)=U
    rw [s0,du]; simp
  have hcy : U.map Y≤U := s1 ▸ hc
  have line (w : Vec K (s+1)) : (K ∙ w).map N = K ∙ N w := by
    rw [Submodule.map_span,Set.image_singleton]
  have s2 : B 2=U⊔(K ∙ g) := by
    change B 1 ⊔ (B 1).map N ⊔ (B 1).map Y ⊔ (K ∙ backSeed2 A b)=_
    rw [s1,←du,show U.map N=K ∙ g from line d]
    exact le_antisymm (sup_le (sup_le le_rfl (hcy.trans le_sup_left)) le_sup_left) (le_sup_left.trans le_sup_left)
  have hgrank := hs.backRank 2 (by decide)
  have hdrank := hs.backRank 1 (by decide)
  change finrank K (B 2)=2 at hgrank
  change finrank K (B 1)=1 at hdrank
  have hgn : g∉U := by
    intro hg
    have hr : B 2=B 1 := by rw [s2,s1,sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem ..).mpr hg)]
    rw [hr,hdrank] at hgrank
    contradiction
  have echelon (n : ℕ) (hn : n≤3) :
      B (n+1)=chain Y U g n := by
    obtain ⟨bn,bn2⟩ := (show (¬ (B 2).map Y≤B 2) ∧ (¬ (B 3).map Y≤B 3) from
      ⟨(reverse_seven_nine ha ho hs).noninvariantBack2,(reverse_seven_nine ha ho hs).noninvariantBack3⟩)
    have step (k : ℕ) (hk : k=2 ∨ k=3) : B (k+1)=B k ⊔ (B k).map Y := by
      apply join_next (back_le_succ A b k) (back_map_clock A b k)
      · rcases hk with rfl|rfl <;> assumption
      · have a := hs.backRank k (by omega)
        have e := hs.backRank (k+1) (by omega)
        change finrank K (back A b (k+1))≤finrank K (back A b k)+1
        omega
    induction n with
    | zero => exact s1
    | succ n ih =>
      by_cases hz : n=0
      · subst n; simpa [chain] using s2
      · have ek : n+1=2 ∨ n+1=3 := by omega
        rw [step _ ek,ih (by omega),chain_sup_map hcy (by omega)]
  have hdU : d∈U := Submodule.mem_span_singleton_self _
  obtain ⟨a,hae⟩ := Submodule.mem_span_singleton.mp (hcy (Submodule.mem_map_of_mem hdU))
  have loc (i) (hn : mirror A i≠a) : d i=0 := by
    have h := congrFun hae i
    change a*d i=mirror A i*d i at h
    exact (mul_eq_zero.mp (show (a-mirror A i)*d i=0 by rw [sub_mul,h,sub_self])).resolve_left
      (sub_ne_zero.mpr hn.symm)
  obtain ⟨i,hi,_,_,_,hdi⟩ := reverse_first_pivot ha ho (by decide)
  have ha0 : a≠0 := by
    intro hz
    exact hdi (loc i (hz ▸ hi))
  have hc' := reverse_seven_nine ha ho hs
  refine ⟨s1,⟨a,ha0,loc⟩,?_,echelon,?_,?_⟩
  · change g∉B 1; rw [s1]; exact hgn
  · rw [hc'.back2]; exact reverseResidual_mem ho (by decide) (by decide)
  · rw [hc'.back3]; exact reverseResidual_mem ho (by decide) (by decide)

end RKCert.Paired.OrderTwelve
