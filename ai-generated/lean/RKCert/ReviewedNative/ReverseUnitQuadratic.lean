module

public import RKCert.ReviewedNative.TerminalCapacity
public import RKCert.ReviewedNative.ReverseClockGain
public import RKCert.ReviewedNative.NativeClockStaircase
public import RKCert.ReviewedNative.ReflectedPolynomialBudget
public import RKCert.ReviewedNative.ReverseTwoNodeNative
public import RKCert.ReviewedNative.WeightedClockBand

@[expose] public section

/-! # A paid native quadratic reverse seed has at least two physical clocks

The neutral original-matrix port uses the already checked two-node
chronology. The row conversion is at the level of vectors and linear
maps only, with no import of old tableau or rooted-tree order. The rank
and clock escapes remain explicit earned hypotheses of the short flag. -/
namespace RKResearch.Certified.Graded.Reverse.UnitQuadratic
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock RKCert.OneEscape
open RKResearch.Certified.Graded.Reverse.TwoNode
open scoped Classical Matrix

noncomputable section
variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}

set_option maxRecDepth 3500
set_option maxHeartbeats 800000

/-- Paid reflected moments see an active weight outside a small set of
clock values, without needing nonzero individual weights or distinct rows. -/
private theorem reflected_active_avoid {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
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

abbrev normalizedResidual (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ) :=
    (((k+1:ℕ):K)⁻¹ : K) • reflectedStageRow A b k

omit [CharZero K] in
private theorem reflected_weights_eq_powerWeight (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ) :
    reflectedStageWeight A b k=powerWeight (reflectedClock A) b k := by
  ext i; simp [powerWeight,mul_comm]

private theorem normalized_residual_apply (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) (k : ℕ)
    (i : Fin s) :
    normalizedResidual A b k i=
      mat A.transpose (powerWeight (reflectedClock A) b k) i -
        (reflectedClock A i)^(k+1)*b i/((k+1:ℕ):K) := by
  have nz : ((k+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  unfold normalizedResidual reflectedStageRow
  rw [smul_sub,smul_smul,inv_mul_cancel₀ nz,one_smul,
    reflected_weights_eq_powerWeight,reflected_weights_eq_powerWeight]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,powerWeight,mat_apply,div_eq_mul_inv]
  ring

omit [CharZero K] in
private theorem first_zero_eq_transpose (zero : firstSeed A b=0) :
    mat A.transpose b=diag (reflectedClock A) b := by
  have h0 : reflectedStageWeight A b 0=b := by ext i; simp [reflectedStageWeight]
  have h1 : reflectedStageWeight A b 1=diag (reflectedClock A) b := by ext i; simp [mul_comm]
  change ((0+1:ℕ):K) • mat A.transpose (reflectedStageWeight A b 0) - reflectedStageWeight A b (0+1)=0 at zero
  rw [Nat.zero_add,Nat.cast_one,one_smul,h0,h1] at zero
  exact sub_eq_zero.mp zero

private theorem greatest_reflected_pivot (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 2≤p) :
    ∃ i : Fin s, reflectedClock A i≠0 ∧ b i≠0 ∧
      (∀ j, i<j → reflectedClock A j*b j=0) ∧
      normalizedResidual A b 1 i= -((2:K)⁻¹)*(reflectedClock A i)^2*b i ∧
      normalizedResidual A b 1 i≠0 := by
  let y := reflectedClock A
  let v := diag y b
  have ht : v≠0 := by
    intro h
    have eq : reflectedProbe A b 0 1 (1 : Fin s→K) = row v 1 := by
      simp only [row_apply,dotProduct,diag_apply,Pi.one_apply,pow_zero,pow_one,mul_one,v]
      exact Finset.sum_congr rfl (fun i _=>mul_comm _ _)
    have e := reflected_power_mass ho 1 (by omega)
    rw [eq,h] at e
    simp at e
  obtain ⟨i,hi⟩ : ∃i,v i≠0 := by by_contra! h; exact ht (funext h)
  let S := Finset.univ.filter (fun j : Fin s=> v j≠0)
  obtain ⟨i,hi,hm⟩ := Finset.exists_max_image S id ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  have hv : y i*b i≠0 := (Finset.mem_filter.mp hi).2
  have before (j : Fin s) (hj : i<j) : v j=0 := by
    by_contra hn
    exact (not_le_of_gt hj) (hm j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩))
  have w1 : powerWeight y b 1=v := by ext j; simp [v,powerWeight]
  have zz : mat A.transpose v i=0 := transpose_tail_zero ha before le_rfl
  have e : normalizedResidual A b 1 i= -((2:K)⁻¹)*(y i)^2*b i := by
    rw [normalized_residual_apply]
    change mat A.transpose (powerWeight y b 1) i- y i^2*b i/2=_
    rw [w1,zz]
    ring
  have nz := mul_ne_zero_iff.mp hv
  have res : normalizedResidual A b 1 i≠0 := by
    rw [e]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (by norm_num))) (pow_ne_zero _ nz.1)) nz.2
  exact ⟨i,nz.1,nz.2,before,e,res⟩

/-- A single row system, in either orientation. The actual comparison order
enters through the causal operator and the separate pivot statement. -/
private structure ReverseRows (N : (Fin s → K) →ₗ[K] (Fin s → K)) (y v d g : (Fin s → K)) (a : K) : Prop where
  support : ∀ i, y i≠a → d i=0
  base : N v=diag y v
  next : N d=g
  quadratic : ∀i, N (powerWeight y v 1) i=y i^2*v i/2+d i
  cubic : ∃ k : K, ∀i, N (powerWeight y v 2) i=y i^3*v i/3+(2*a/3)*d i+k*g i
  quartic : ∃ k l : K, ∀i, N (powerWeight y v 3) i=y i^4*v i/4+a^2/2*d i+(k+l*y i)*g i
  advance : ∃ k l : K, ∀i, N g i=(k+l*y i)*g i
  shifted : ∃ k l m : K, ∀i, N (diag y g) i=(k+l*y i+m*y i^2)*g i

/-- Homogeneous change of feature for the one-node-supported quadratic jet. -/
private theorem reduce_reverse_rows {N : (Fin s → K) →ₗ[K] (Fin s → K)} {y v d g : (Fin s → K)} {a : K}
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

private structure LocalizedReverseChart (A : Matrix (Fin s) (Fin s) K) (b : (Fin s→K)) : Prop where
  first : back A b 1=K ∙ normalizedResidual A b 1
  support : ∃ a : K, a≠0 ∧ ∀ i, reflectedClock A i≠a → normalizedResidual A b 1 i=0
  next_out : mat A.transpose (normalizedResidual A b 1)∉back A b 1
  chart : ∀ n≤3, back A b (n+1)=
    chain (diag (reflectedClock A)) (K ∙ normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) n
  cubic : normalizedResidual A b 2∈back A b 2
  quartic : normalizedResidual A b 3∈back A b 3



omit [CharZero K] in
private theorem short_reverse_join {U Z : Submodule K ((Fin s→K))} {T : (Fin s→K) →ₗ[K] (Fin s→K)}
    (hu : U≤Z) (ht : U.map T≤Z) (hne : ¬U.map T≤U)
    (hr : finrank K Z≤finrank K U+1) : Z=U⊔U.map T := by
  symm; apply Submodule.eq_of_le_of_finrank_le (sup_le hu ht)
  have hlt : U < U⊔U.map T := lt_of_le_of_ne le_sup_left (fun he => hne (le_trans le_sup_right he.ge))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

private theorem localized_reverse_chart_of_ranks (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:2≤p) (seedZero:firstSeed A b=0)
    (ranks:∀n≤4,finrank K (back A b n)=n)
    (nc2:¬(back A b 2).map (diag (reflectedClock A))≤back A b 2)
    (nc3:¬(back A b 3).map (diag (reflectedClock A))≤back A b 3)
    (hcubic:normalizedResidual A b 2∈back A b 2)
    (hquartic:normalizedResidual A b 3∈back A b 3)
    (hc:(back A b 1).map (diag (reflectedClock A))≤back A b 1) : LocalizedReverseChart A b := by
  let d := normalizedResidual A b 1
  let U := K ∙ d
  let N := mat A.transpose
  let Y := diag (reflectedClock A)
  let g := N d
  let B := back A b
  have s0 : B 0=⊥ := by
    change Submodule.span K {firstSeed A b}=⊥
    rw [seedZero,Submodule.span_zero_singleton]
  have du : U=K ∙ quadraticSeed A b := by
    change (K ∙ ((2:K)⁻¹ • quadraticSeed A b))=_
    rw [Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr (by norm_num))]
  have s1 : B 1=U := by
    change B 0 ⊔ (B 0).map N ⊔ (B 0).map Y ⊔ (K ∙ quadraticSeed A b)=U
    rw [s0,du]; simp
  have hcy : U.map Y≤U := s1 ▸ hc
  have line (w : (Fin s→K)) : (K ∙ w).map N = K ∙ N w := by
    rw [Submodule.map_span,Set.image_singleton]
  have s2 : B 2=U⊔(K ∙ g) := by
    change B 1 ⊔ (B 1).map N ⊔ (B 1).map Y ⊔ (K ∙ quadraticSeed A b)=_
    rw [s1,←du,show U.map N=K ∙ g from line d]
    exact le_antisymm (sup_le (sup_le le_rfl (hcy.trans le_sup_left)) le_sup_left) (le_sup_left.trans le_sup_left)
  have hgrank := ranks 2 (by decide)
  have hdrank := ranks 1 (by decide)
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
      ⟨nc2,nc3⟩)
    have step (k : ℕ) (hk : k=2 ∨ k=3) : B (k+1)=B k ⊔ (B k).map Y := by
      apply short_reverse_join (adjointFlag_le_succ (A:=A) (b:=b) (pairCredit A b) k) (adjointFlag_clock (A:=A) (b:=b) (pairCredit A b) k)
      · rcases hk with rfl|rfl <;> assumption
      · have a := ranks k (by omega)
        have e := ranks (k+1) (by omega)
        change finrank K (back A b (k+1))≤finrank K (back A b k)+1
        omega
    induction n with
    | zero => exact s1
    | succ n ih =>
      by_cases hz : n=0
      · subst n; simpa [chain] using s2
      · have ek : n+1=2 ∨ n+1=3 := by omega
        rw [step _ ek,ih (by omega),clock_chain_next hcy (by omega)]
  have hdU : d∈U := Submodule.mem_span_singleton_self _
  obtain ⟨a,hae⟩ := Submodule.mem_span_singleton.mp (hcy (Submodule.mem_map_of_mem hdU))
  have loc (i) (hn : reflectedClock A i≠a) : d i=0 := by
    have h := congrFun hae i
    change a*d i=reflectedClock A i*d i at h
    exact (mul_eq_zero.mp (show (a-reflectedClock A i)*d i=0 by rw [sub_mul,h,sub_self])).resolve_left
      (sub_ne_zero.mpr hn.symm)
  obtain ⟨i,hi,_,_,_,hdi⟩ := greatest_reflected_pivot ha ho hp
  have ha0 : a≠0 := by
    intro hz
    exact hdi (loc i (hz ▸ hi))
  exact ⟨s1,⟨a,ha0,loc⟩,by change g∉B 1;rw [s1];exact hgn,echelon,hcubic,hquartic⟩

omit [CharZero K] in
private theorem short_chart_coeff_one {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 1) :
    ∃ a b : K, ∀ i, v i=a*d i+b*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,fun i => by simp⟩

omit [CharZero K] in
private theorem short_chart_coeff_two {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 2) :
    ∃ a b c : K, ∀ i, v i=a*d i+(b+c*y i)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,hx⟩ := short_chart_coeff_one hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,fun i => by simp [hx]; ring⟩

omit [CharZero K] in
private theorem short_chart_coeff_three {y d g v : (Fin s→K)}
    (hv : v∈chain (diag y) (K ∙ d) g 3) :
    ∃ a b c e : K, ∀ i, v i=a*d i+(b+c*y i+e*(y i)^2)*g i := by
  obtain ⟨x,hx,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,b,c,hx⟩ := short_chart_coeff_two hx
  obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨a,b,c,e,fun i => by simp [hx]; ring⟩

private theorem localized_reverse_rows_of_chart (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:2≤p) (seedZero:firstSeed A b=0) (H:LocalizedReverseChart A b) :
    ∃ a:K,a≠0∧ReverseRows (mat A.transpose) (reflectedClock A) b
      (normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) a := by
  let N := mat A.transpose
  let y := reflectedClock A
  let d := normalizedResidual A b 1
  let g := N d
  let B := back A b
  let Y := diag y
  obtain ⟨a,ha0,hloc⟩ := H.support
  obtain ⟨j,hy,hb,hbefore,hdi,hnj⟩ := greatest_reflected_pivot ha ho hp
  have hya : y j=a := by by_contra h; exact hnj (hloc j h)
  have pw (k : ℕ) (hk : 0<k) (i : Fin s) (hi : j < i) : powerWeight y b k i=0 := by
    have h := hbefore i hi
    rcases mul_eq_zero.mp h with h|h
    · change (reflectedClock A i)^k*b i=0; rw [h,zero_pow (by omega),zero_mul]
    · simp [powerWeight,h]
  have pn (k : ℕ) (hk : 0<k) (i : Fin s) (hi : j ≤ i) : N (powerWeight y b k) i=0 :=
    causal_transpose ha i _ (fun t h => pw k hk t (lt_of_le_of_lt hi (Fin.rev_lt_rev.mp h)))
  have primitive (k : ℕ) (i : Fin s) :
      N (powerWeight y b k) i = y i^(k+1)*b i/((k+1:ℕ):K)+normalizedResidual A b k i := by
    have h := normalized_residual_apply A b k i
    change normalizedResidual A b k i=N (powerWeight y b k) i-y i^(k+1)*b i/((k+1:ℕ):K) at h
    rw [h]
    ring
  have hd0 (i : Fin s) (hi : j < i) : d i=0 := by
    have he := primitive 1 i
    have hz := pw 2 (by decide) i hi
    change y i^2*b i=0 at hz
    rw [pn 1 (by decide) _ hi.le,hz,zero_div,zero_add] at he
    exact he.symm
  have hg0 (i : Fin s) (hi : j ≤ i) : g i=0 :=
    causal_transpose ha i d (fun t h=>hd0 t (lt_of_le_of_lt hi (Fin.rev_lt_rev.mp h)))
  have hng : N g j=0 := causal_transpose ha _ _ (fun _ h=>hg0 _ (Fin.rev_lt_rev.mp h).le)
  have hnyg : N (Y g) j=0 := causal_transpose ha _ _ (fun _ h=>by
    change _*g _=0; rw [hg0 _ (Fin.rev_lt_rev.mp h).le,mul_zero])
  have lc := H.cubic
  have lq := H.quartic
  rw [H.chart 1 (by decide)] at lc
  rw [H.chart 2 (by decide)] at lq
  obtain ⟨c₀,c₁,cc⟩ := short_chart_coeff_one lc
  obtain ⟨q₀,q₁,q₂,qq⟩ := short_chart_coeff_two lq
  have hg2 : g∈B 2 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 1 (Submodule.mem_map_of_mem (by
    change d∈back A b 1
    rw [H.first]; exact Submodule.mem_span_singleton_self _))
  have ng3 : N g∈B 3 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 2 (Submodule.mem_map_of_mem hg2)
  have yg3 : Y g∈B 3 := adjointFlag_clock (A:=A) (b:=b) (pairCredit A b) 2 (Submodule.mem_map_of_mem hg2)
  have ng4 : N (Y g)∈B 4 := adjointFlag_transpose (A:=A) (b:=b) (pairCredit A b) 3 (Submodule.mem_map_of_mem yg3)
  change _∈back A b 3 at ng3
  change _∈back A b 4 at ng4
  rw [H.chart 2 (by decide)] at ng3
  rw [H.chart 3 (by decide)] at ng4
  obtain ⟨n₀,n₁,n₂,nn⟩ := short_chart_coeff_two ng3
  obtain ⟨p₀,p₁,p₂,p₃,pp⟩ := short_chart_coeff_three ng4
  change ∀ i, normalizedResidual A b 2 i=c₀*d i+c₁*g i at cc
  change ∀ i, normalizedResidual A b 3 i=q₀*d i+(q₁+q₂*y i)*g i at qq
  change ∀ i, N g i=n₀*d i+(n₁+n₂*y i)*g i at nn
  change ∀ i, N (Y g) i=p₀*d i+(p₁+p₂*y i+p₃*y i^2)*g i at pp
  change d j= -((2:K)⁻¹)* (y j)^2*b j at hdi
  have c₀e : c₀=2*a/3 := by
    apply mul_right_cancel₀ hnj
    have e := primitive 2 j
    rw [pn _ (by decide) _ le_rfl,cc,hg0 _ le_rfl,mul_zero,add_zero] at e
    change 0=y j^3*b j/3+c₀*d j at e
    change c₀*d j=(2*a/3)*d j
    calc c₀*d j = -(y j^3*b j/3) := by linear_combination -e
         _ = _ := by rw [hdi,hya]; ring
  have q₀e : q₀=a^2/2 := by
    apply mul_right_cancel₀ hnj
    have e := primitive 3 j
    rw [pn _ (by decide) _ le_rfl,qq,hg0 _ le_rfl,mul_zero,add_zero] at e
    change 0=y j^4*b j/4+q₀*d j at e
    change q₀*d j=(a^2/2)*d j
    calc q₀*d j = -(y j^4*b j/4) := by linear_combination -e
         _ = _ := by rw [hdi,hya]; ring
  have n₀e : n₀=0 := by
    have e:=nn j; rw [hng,hg0 _ le_rfl,mul_zero,add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hnj
  have p₀e : p₀=0 := by
    have e:=pp j; rw [hnyg,hg0 _ le_rfl,mul_zero,add_zero] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hnj
  refine ⟨a,ha0,hloc,first_zero_eq_transpose seedZero,rfl,fun i => primitive 1 i,⟨c₁,?_⟩,
    ⟨q₁,q₂,?_⟩,⟨n₁,n₂,?_⟩,⟨p₁,p₂,p₃,?_⟩⟩
  · intro i
    calc N (powerWeight y b 2) i = _ := primitive 2 i
         _ = _ := by rw [cc,c₀e]; ring
  · intro i
    calc N (powerWeight y b 3) i = _ := primitive 3 i
         _ = _ := by rw [qq,q₀e]; ring
  · simpa only [n₀e,zero_mul,zero_add] using nn
  · simpa only [p₀e,zero_mul,zero_add] using pp

private theorem localized_reverse_rows_impossible (ha:∀i j,i≤j → A i j=0) (ho:HasOrder p A b)
    (hp:10≤p) (H:∃ a:K,a≠0∧ReverseRows (mat A.transpose) (reflectedClock A) b
      (normalizedResidual A b 1) (mat A.transpose (normalizedResidual A b 1)) a) : False := by
  classical
  obtain ⟨a,ha0,r⟩:=H
  let y := reflectedClock A
  let d := normalizedResidual A b 1
  let g := mat A.transpose d
  let h := powerWeight y b 1+(2/a) • d
  have val (i) : h i=y i*b i+(2/a)*d i := by simp [h,powerWeight]
  have loc (i) (hi : y i≠a) : d i=0 := r.support i hi
  have rz : ∀i,y i=0→h i=0 := by
    intro i hi
    rw [val,loc i (by rw [hi]; exact ha0.symm),hi]; ring
  apply two_node_confinement Fin.revPerm (mat A.transpose) (causal_transpose ha) y h
    (a⁻¹ • g) (reduce_reverse_rows ha0 r) rz
  intro t u
  let T : Finset K := {0,a,t,u}
  have card : T.card≤4 := calc
    T.card ≤ ({a,t,u}:Finset K).card+1 := Finset.card_insert_le ..
    _ ≤ (({t,u}:Finset K).card+1)+1 := Nat.add_le_add_right (Finset.card_insert_le ..) _
    _ ≤ ((({u}:Finset K).card+1)+1)+1 := Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le ..) _) _
    _ = 4 := by simp
  obtain ⟨i,bi,hi⟩ := reflected_active_avoid ho T (by omega)
  have hh : y i≠0 ∧ y i≠a ∧ y i≠t ∧ y i≠u := by
    change y i∉({0,a,t,u}:Finset K) at hi
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hi
  exact ⟨i,by rw [val,loc i hh.2.1,mul_zero,add_zero]; exact mul_ne_zero hh.1 bi,hh.2.2⟩



/-- No localized one-dimensional quadratic reverse line can sustain
the three following paid native ranks and the two extra monomial rows. -/
theorem localized_native_reverse_impossible (ha : ∀i j,i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 10≤p) (seedZero : firstSeed A b=0)
    (ranks : ∀n≤4,finrank K (back A b n)=n)
    (nc2 : ¬(back A b 2).map (diag (reflectedClock A))≤back A b 2)
    (nc3 : ¬(back A b 3).map (diag (reflectedClock A))≤back A b 3)
    (h2 : normalizedResidual A b 2∈back A b 2)
    (h3 : normalizedResidual A b 3∈back A b 3) :
    ¬(back A b 1).map (diag (reflectedClock A))≤back A b 1 := by
  intro stable
  have C := localized_reverse_chart_of_ranks ha ho (by omega) seedZero ranks nc2 nc3 h2 h3 stable
  exact localized_reverse_rows_impossible ha ho pay
    (localized_reverse_rows_of_chart ha ho (by omega) seedZero C)

/-- The actual unit-rank initial flag and its two already paid escapes. -/
structure UnitFrame (A : Matrix (Fin s) (Fin s) K) (b : Fin s→K) : Prop where
  firstZero : firstSeed A b=0
  rankExact : ∀ n≤4, finrank K (back A b n)=n ∧ back A b n=primitiveBack A b n
  clockEscape : ∀ n, 2≤n → n≤3 →
    ¬(primitiveBack A b n).map (diag (reflectedClock A))≤primitiveBack A b n

omit [CharZero K] in
private theorem residual_in_flag (F : UnitFrame A b) {n : ℕ} (pos : 1≤n) (pay : n≤4) :
    normalizedResidual A b n∈back A b n := by
  rw [(F.rankExact n pay).2]
  have h := adjointFlag_credit (A:=A) (b:=b) (monomialCredit A b) (n-1)
    (monomial_mem_credit (A:=A) (b:=b) (n-1) n (by omega))
  rw [show n-1+1=n by omega] at h
  exact (primitiveBack A b n).smul_mem _ h

omit [CharZero K] in
private theorem reverse_quadratic_line (zero : firstSeed A b=0) :
    back A b 1=K ∙ quadraticSeed A b := by
  have h : back A b 0=⊥ := by
    change Submodule.span K {firstSeed A b}=⊥
    rw [zero,Submodule.span_zero_singleton]
  change back A b 0 ⊔ (back A b 0).map (mat A.transpose) ⊔
    (back A b 0).map (diag (reflectedClock A)) ⊔ (K ∙ quadraticSeed A b)=_
  rw [h]
  simp

/-- For any ordered numbering and any characteristic-zero field, the
quadratic seed cannot occupy only one reflected clock. Zero sites are
excluded by the first paid rank. -/
theorem quadratic_sites_ge_two (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b)
    (pay : 10≤p) (F : UnitFrame A b) :
    2≤(weightedSites (reflectedClock A) (quadraticSeed A b)).card := by
  let y := reflectedClock A
  let d := quadraticSeed A b
  have line : back A b 1=K ∙ d := reverse_quadratic_line F.firstZero
  have nz : d≠0 := by
    intro h
    have q := (F.rankExact 1 (by decide)).1
    rw [line,h,Submodule.span_zero_singleton,finrank_bot] at q
    contradiction
  obtain ⟨i,hi⟩ : ∃ i,d i≠0 := by
    by_contra! h
    exact nz (funext h)
  have pos : 0<(weightedSites y d).card :=
    Finset.card_pos.mpr ⟨y i,mem_weightedSites.mpr ⟨i,hi,rfl⟩⟩
  by_contra! small
  change (weightedSites y d).card<2 at small
  obtain ⟨a,h⟩ := Finset.card_eq_one.mp (by omega : (weightedSites y d).card=1)
  have scale : diag y d=a • d := by
    ext j
    by_cases dz : d j=0
    · simp [dz]
    · have m : y j∈weightedSites y d := mem_weightedSites.mpr ⟨j,dz,rfl⟩
      rw [h,Finset.mem_singleton] at m
      simp [m]
  have escape (n : ℕ) (lo : 2≤n) (hi : n≤3) :
      ¬(back A b n).map (diag y)≤back A b n := by
    rw [(F.rankExact n (by omega)).2]
    exact F.clockEscape n lo hi
  apply localized_native_reverse_impossible ha ho pay F.firstZero
    (fun n hn => (F.rankExact n hn).1) (escape 2 (by decide) (by decide))
    (escape 3 (by decide) (by decide)) (residual_in_flag F (by decide) (by decide))
    (residual_in_flag F (by decide) (by decide))
  rw [line,Submodule.map_span,Set.image_singleton,scale]
  exact (Submodule.span_singleton_le_iff_mem ..).mpr
    ((K ∙ d).smul_mem a (Submodule.mem_span_singleton_self d))

end
end RKResearch.Certified.Graded.Reverse.UnitQuadratic
