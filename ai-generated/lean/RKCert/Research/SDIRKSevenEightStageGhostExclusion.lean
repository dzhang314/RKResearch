module
public import RKCert.Research.SDIRKSevenEightStageTerminal
public import RKCert.ReviewedNative.RationalPrimeNodalSupport
public import RKCert.ReviewedNative.SDIRKSixNormal
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-! # Rational order seven with eight strict stages has no zero weights

The quartic paid stage flag and its two independent visible Legendre
columns make hidden cubic defects invariant under the literal clock.
The first three distinct chronological clocks then force a pure third
stage; its normalized clock would have to be a root of a rationally
rootless cubic. The result does not assume distinct raw abscissae.
-/

namespace RKResearch.Certified.Graded.SDIRKSeven
open RKResearch FiniteRootedTree Module Reverse Polynomial
open SDIRKSix (seed seed_zero comm_one)
open scoped Matrix BigOperators Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8→K} {γ : K}

omit [CharZero K] in
private theorem head₂ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (x : Fin 8→K) :
    mat A x 2=A 2 0*x 0+A 2 1*x 1+γ*x 2 := by
  change (∑ j : Fin 8,A 2 j*x j)=_
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  change A 2 0*x 0+(A 2 1*x 1+(A 2 2*x 2+∑ j:Fin 5,A 2 j.succ.succ.succ*x j.succ.succ.succ))=_
  have z : (∑ j:Fin 5,A 2 j.succ.succ.succ*x j.succ.succ.succ)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have h : (2:Fin 8)<j.succ.succ.succ := by change 2<j.val+1+1+1; omega
    exact mul_eq_zero.mpr (Or.inl (@ha (2:Fin 8) j.succ.succ.succ h))
  rw [z,he,add_zero]
  ring

omit [CharZero K] in
private theorem clock₂ (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) :
    nodes A 2=A 2 0+A 2 1+γ := by
  rw [SDIRKSix.node_mat_one,head₂ ha he]
  simp

omit [CharZero K] in
private theorem front_comm_one (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    mat A (volterra A 1)=volterra A (mat A 1) := by
  have r0 (v : Fin 8→K) : volterra A v 0=-(γ^2)*v 0 := by
    rw [volterra_pivot ha 0 v (fun j hj=>(Fin.not_lt_zero j hj).elim),he]
  have r1 (v : Fin 8→K) :
      volterra A v 1=-(γ^2)*v 1+A 1 0*(nodes A 1-nodes A 0-2*γ)*v 0 := by
    change nodes A 1*mat A v 1-mat A (diag (nodes A) v) 1-mat A (mat A v) 1=_
    simp only [head₀ ha he,head₁ ha he,diag_apply]
    ring
  apply sub_eq_zero.mp
  apply cubic_head_unique ho ha he hγ
  · apply (zeroSpace A 3).sub_mem
    · rw [comm_one,map_neg]
      exact (zeroSpace A 3).neg_mem (mat_zeroSpace ho 2 (by decide) (seed_zero A))
    · have h : mat A (1:Fin 8→K)∈treeSpace A 1 :=
        mat_treeSpace A 0 (Φ_mem_treeSpace A .leaf (by decide))
      exact volterra_treeSpace ho 1 (by decide) h
  · simp only [Pi.sub_apply,head₀ ha he,r0,Pi.one_apply]
    ring
  · simp only [Pi.sub_apply,head₁ ha he,head₀ ha he,r1,r0,Pi.one_apply]
    ring

private theorem front_clocks_distinct (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    nodes A 0≠nodes A 1 ∧ nodes A 2≠nodes A 0 ∧ nodes A 2≠nodes A 1 := by
  have ht := first_tap_ne_zero ho ha he hγ
  have ap : A 2 1 * A 1 0 * (2*nodes A 1-nodes A 0-nodes A 2)=0 := by
    have h := congrFun (front_comm_one ho ha he hγ) 2
    change mat A (volterra A 1) 2 =
      nodes A 2*mat A (mat A 1) 2-mat A (diag (nodes A) (mat A 1)) 2-
        mat A (mat A (mat A 1)) 2 at h
    rw [comm_one,map_neg] at h
    have s₂ : seed A 2 =
        2*(A 2 0*nodes A 0+A 2 1*nodes A 1+γ*nodes A 2)-(nodes A 2)^2 := by
      change 2*mat A (nodes A) 2-nodes A 2*nodes A 2=_
      rw [head₂ ha he,pow_two]
    simp only [Pi.neg_apply,head₂ ha he,head₁ ha he,head₀ ha he,Pi.one_apply,diag_apply,
      seed₀ ha he,seed₁ ha he,s₂,clock₀ ha he,clock₁ ha he,clock₂ ha he] at h ⊢
    linear_combination h
  have a01 : nodes A 0≠nodes A 1 := by
    rw [clock₀ ha he,clock₁ ha he]
    intro e
    apply ht
    linear_combination -e
  refine ⟨a01,?_,?_⟩
  all_goals
    intro eq
    have tap : A 2 1=0 := by
      by_contra h
      have ar := (mul_eq_zero.mp ap).resolve_left (mul_ne_zero h ht)
      rw [eq] at ar
      apply a01
      first | linear_combination -(1/2:K)*ar | linear_combination -ar
    have top := grade_five_top ho ha (fun i => he i ▸ hγ)
    first
    | have tap₀' : A 2 0=0 := by
        rw [clock₂ ha he,clock₀ ha he,tap] at eq
        linear_combination eq
      have same (t : FiniteRootedTree) : Φ t A 2=Φ t A 0 := by
        induction t with
        | leaf => rfl
        | butcherProduct r s hr hs =>
          change Φ r A 2*mat A (Φ s A) 2=Φ r A 0*mat A (Φ s A) 0
          simp only [head₂ ha he,head₀ ha he,tap,tap₀',zero_mul,zero_add,hr,hs]
      exact (by decide : (2:Fin 8)≠0) (SDIRKSix.nodes_detect top same)
    | have tap₀' : A 2 0=A 1 0 := by
        rw [clock₂ ha he,clock₁ ha he,tap] at eq
        linear_combination eq
      have same (t : FiniteRootedTree) : Φ t A 2=Φ t A 1 := by
        induction t with
        | leaf => rfl
        | butcherProduct r s hr hs =>
          change Φ r A 2*mat A (Φ s A) 2=Φ r A 1*mat A (Φ s A) 1
          simp only [head₂ ha he,head₁ ha he,tap,tap₀',zero_mul,add_zero,hr,hs]
      exact (by decide : (2:Fin 8)≠1) (SDIRKSix.nodes_detect top same)

omit [CharZero K] in
private theorem quartic_silent (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) :
    SDIRKSix.silent A b 4 2=zeroSpace A 4 ∧ finrank K (zeroSpace A 4)=4 := by
  let E := treeSpace A 2
  let F := zeroSpace A 4
  let L := (volterra A).comp E.subtype
  have injective : Function.Injective L :=
    (volterra_injective ha hn).comp Subtype.val_injective
  have inc : L.range≤F := by
    rintro _ ⟨v,rfl⟩
    exact volterra_treeSpace ho 2 (by decide) v.property
  have lo := Submodule.finrank_mono inc
  rw [LinearMap.finrank_range_of_inj injective] at lo
  have h₂ := congrArg (fun xs : List ℕ => xs[2]!) (grade_ranks ho ha hn)
  have h₄ := congrArg (fun xs : List ℕ => xs[4]!) (grade_ranks ho ha hn)
  change finrank K E=4 at h₂
  change finrank K E≤finrank K (zeroSpace A 4) at lo
  change finrank K (treeSpace A 4)=7 at h₄
  have top := SDIRKSix.silent_rank ho (a:=4) (q:=2) (by decide) (by decide)
  have inc2 := SDIRKSix.zero_le_silent ho (a:=4) (q:=2) (by decide)
  have rank2 := Submodule.finrank_mono inc2
  refine ⟨(Submodule.eq_of_le_of_finrank_le inc2 (by omega)).symm,?_⟩
  omega

private def shiftedLegendre3 (R : Type*) [CommRing R] : R[X] :=
  C 20*X^3-C 30*X^2+C 12*X-1
private def shiftedLegendre4 (R : Type*) [CommRing R] : R[X] :=
  C 70*X^4-C 140*X^3+C 90*X^2-C 20*X+1

private def legᵢ (q : ℕ) (A : Matrix (Fin 8) (Fin 8) K) : Fin 8→K :=
  if q=3 then coeffEval A 4 (fun j=> if j=0 then -1 else if j=1 then 12 else if j=2 then -30 else if j=3 then 20 else 0)
  else coeffEval A 4 (fun j=> if j=0 then 1 else if j=1 then -20 else if j=2 then 90 else if j=3 then -140 else 70)

omit [CharZero K] in
private theorem leg₃_eval (A : Matrix (Fin 8) (Fin 8) K) (i : Fin 8) :
    legᵢ 3 A i=(shiftedLegendre3 K).eval (nodes A i) := by
  simp only [legᵢ,ite_eq_left rfl,coeffEval_apply,normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    shiftedLegendre3,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_one]
  norm_num [Fin.sum_univ_succ]
  ring

omit [CharZero K] in
private theorem leg₄_eval (A : Matrix (Fin 8) (Fin 8) K) (i : Fin 8) :
    legᵢ 4 A i=(shiftedLegendre4 K).eval (nodes A i) := by
  simp only [legᵢ,show ¬ (4:ℕ)=3 by decide,ite_false,coeffEval_apply,normTree_clockTree,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    shiftedLegendre4,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_one]
  norm_num [Fin.sum_univ_succ]
  ring

private theorem legendre_paid (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (hn : ∀ i,A i i≠0) :
    legᵢ 3 A ∈ zeroSpace A 4 ∧ legᵢ 4 A ∈ zeroSpace A 4 := by
  rw [←(quartic_silent ho ha hn).1]
  constructor <;> apply SDIRKSix.silent_mem.mpr
  · exact ⟨coeffEval_mem_treeSpace _ _ _,fun i => by
      change probe A b i.val (coeffEval A 4 _) = 0
      rw [probe_coeffEval ho (by omega)]
      fin_cases i <;> norm_num [Fin.sum_univ_succ]⟩
  · refine ⟨coeffEval_mem_treeSpace _ _ _,fun i => ?_⟩
    change probe A b i.val (coeffEval A 4 _) = 0
    rw [probe_coeffEval ho (by omega)]
    fin_cases i <;> norm_num [Fin.sum_univ_succ]

private theorem quartic_visible_rank (ho : HasOrder 7 A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i,A i i≠0)
    {T : Finset K} (five : 5≤T.card)
    (cover : ∀ x∈T,∃i : Fin 8,b i≠0 ∧ nodes A i=x) :
    2≤finrank K ((zeroSpace A 4).map (diag b)) := by
  let V := (zeroSpace A 4).map (diag b)
  let g := diag b (legᵢ 3 A)
  let f := diag b (legᵢ 4 A)
  let L : K×K→ₗ[K] (Fin 8→K) :=
    (LinearMap.id.smulRight g).coprod (LinearMap.id.smulRight f)
  obtain ⟨hg,hf⟩ := legendre_paid ho ha hn
  let T' := L.codRestrict V (fun d => V.add_mem
    (V.smul_mem d.1 (Submodule.mem_map_of_mem hg))
    (V.smul_mem d.2 (Submodule.mem_map_of_mem hf)))
  have hin : Function.Injective T' := by
    apply (injective_iff_map_eq_zero _).mpr
    intro t ht
    have h : t.1 • g+t.2 • f=0 := congrArg (fun x : V => x.val) ht
    let Q := C t.1*shiftedLegendre3 K+C t.2*shiftedLegendre4 K
    have hz : Q=0 := by
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ T
      · intro x hx
        obtain ⟨i,hi,rfl⟩ := cover x hx
        have k := congrFun h i
        change t.1*(b i*legᵢ 3 A i)+t.2*(b i*legᵢ 4 A i)=0 at k
        simp only [Q,eval_add,eval_mul,eval_C,←leg₃_eval A i,←leg₄_eval A i]
        apply mul_left_cancel₀ hi
        linear_combination k
      · have cap : Q.natDegree≤4 := by unfold Q shiftedLegendre3 shiftedLegendre4; compute_degree
        omega
    have t₂ : t.2=0 := by
      have h := congrArg (fun p : K[X] => p.coeff 4) hz
      simp only [Q,shiftedLegendre3,shiftedLegendre4,coeff_add,coeff_sub,coeff_C_mul,
        coeff_X_pow,coeff_one,coeff_zero] at h
      norm_num [coeff_X] at h
      exact h
    have t₁ : t.1=0 := by
      have h := congrArg (fun p : K[X] => p.coeff 3) hz
      simp only [Q,t₂,map_zero,zero_mul,add_zero,shiftedLegendre3,
        coeff_add,coeff_sub,coeff_C_mul,coeff_X_pow,coeff_one,coeff_zero] at h
      norm_num [coeff_X] at h
      exact h
    exact Prod.ext t₁ t₂
  simpa only [Module.finrank_prod,CommSemiring.finrank_self] using
    LinearMap.finrank_le_finrank_of_injective hin

/-- Hiding the cubic defects with at least five visible clocks makes
their literal clock multiplication stay in the same cubic space. -/
theorem cubic_clock_invariant_of_hidden (ho : HasOrder 7 A b)
    (ha : A.IsLowerTriangular) (hn : ∀ i,A i i≠0)
    {T : Finset K} (five : 5≤T.card)
    (cover : ∀ x∈T,∃i : Fin 8,b i≠0 ∧ nodes A i=x)
    (hidden : zeroSpace A 3≤ghostSpace b) :
    zeroSpace A 3 ≤ (zeroSpace A 3).comap (diag (nodes A)) := by
  have hV := quartic_visible_rank ho ha hn five cover
  have qr := (quartic_silent ho ha hn).2
  have cr := (grade_three_rank ho ha hn).2
  have h := finrank_map_add_inf_ker (zeroSpace A 4) (diag b)
  rw [←ghostSpace_ker b] at h
  have eq : zeroSpace A 3 = (zeroSpace A 4 ⊓ ghostSpace b) :=
    Submodule.eq_of_le_of_finrank_le (le_inf (zeroSpace_mono A (by decide)) hidden) (by omega)
  intro v hv
  change diag (nodes A) v∈zeroSpace A 3
  rw [eq]
  refine ⟨diag_zeroSpace A 3 hv,mem_ghostSpace.mpr (fun i hi => ?_)⟩
  simp [diag_apply,mem_ghostSpace.mp (hidden hv) i hi]

/-- When the hidden cubic cut is invariant, the third physical row is
pure through size four, even if the third output weight itself vanishes. -/
theorem third_pure_of_hidden_five_clocks (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) {T : Finset K} (five : 5≤T.card)
    (cover : ∀ x∈T,∃i : Fin 8,b i≠0 ∧ nodes A i=x) (hidden : zeroSpace A 3≤ghostSpace b)
    {v : Fin 8→K} (hv : v∈zeroSpace A 3) : v 2=0 := by
  let c := nodes A
  let D (a : K) (x : Fin 8→K) := diag c x-a • x
  have inv := cubic_clock_invariant_of_hidden ho ha (fun i=>he i ▸ hγ) five cover hidden
  have stay (a : K) {x : Fin 8→K} (hx : x∈zeroSpace A 3) : D a x∈zeroSpace A 3 :=
    (zeroSpace A 3).sub_mem (inv hx) ((zeroSpace A 3).smul_mem a hx)
  let w := D (c 0) (D (c 1) v)
  have wF : w∈zeroSpace A 3 := stay _ (stay _ hv)
  have expression (i : Fin 8) : w i=(c i-c 0)*(c i-c 1)*v i := by
    simp only [w,D,diag_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have zw := cubic_head_unique ho ha he hγ wF
    (by rw [expression,sub_self,zero_mul,zero_mul])
    (by rw [expression,sub_self,mul_zero,zero_mul])
  have zz := congrFun zw 2
  rw [expression] at zz
  obtain ⟨_,d₀,d₁⟩ := front_clocks_distinct ho ha he hγ
  apply (mul_eq_zero.mp zz).resolve_left
  exact mul_ne_zero (sub_ne_zero.mpr d₀) (sub_ne_zero.mpr d₁)

omit [CharZero K] in
/-- Every completely pure third physical row satisfies the fixed
Laguerre cubic in its clock normalized by the common diagonal. -/
theorem pure_third_clock_laguerre (ho : HasOrder 7 A b)
    (ha : A.IsLowerTriangular) (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (pure₃ : ∀ v ∈ zeroSpace A 3, v 2=0) :
    (nodes A 2/γ)^3-9*(nodes A 2/γ)^2+18*(nodes A 2/γ)-6=0 := by
  let a := A 2 0
  let d := A 2 1
  let x := nodes A 1
  let y := nodes A 2
  have h0 : a+d+γ=y := (clock₂ ha he).symm
  have h1 : 2*(a*γ+d*x+γ*y)-y^2=0 := by
    have e := pure₃ _ (zeroSpace_mono A (by decide : 2≤3) (seed_zero A))
    change 2*mat A (nodes A) 2-nodes A 2*nodes A 2=0 at e
    rw [head₂ ha he,clock₀ ha he] at e
    simpa only [a,d,x,y,pow_two] using e
  have h2 : 3*(a*γ^2+d*x^2+γ*y^2)-y^3=0 := by
    have e := pure₃ _ (monomialStageDefect_mem A 2)
    change ((2+1:ℕ):K)*mat A (fun i => (nodes A i)^2) 2-(nodes A 2)^3=0 at e
    rw [head₂ ha he,clock₀ ha he] at e
    norm_num at e
    exact e
  have h3 : a*γ^2+d*(4*γ*x-2*γ^2-x^2)=0 := by
    have e := pure₃ _ (mat_zeroSpace ho 2 (by decide) (seed_zero A))
    have z := pure₃ _ (zeroSpace_mono A (by decide : 2≤3) (seed_zero A))
    rw [head₂ ha he,seed₀ ha he,seed₁ ha he,z,mul_zero,add_zero] at e
    have xeq : x=A 1 0+γ := clock₁ ha he
    rw [xeq]
    dsimp [a,d] at *
    linear_combination e
  change (y/γ)^3-9*(y/γ)^2+18*(y/γ)-6=0
  field_simp
  linear_combination -3*h3 - h2 + 6*γ*h1 - 6*γ^2*h0

private theorem rational_two_nonsquare : ¬ IsSquare (2 : ℚ) := by
  exact (Rat.isSquare_natCast_iff (n:=2)).not.mpr Nat.prime_two.not_isSquare

private theorem reduced_pair_not_both_zero {p : ℕ} (hp : ¬ p ∣ 1) (x : ℚ)
    (ha : (x.num : ZMod p) = 0) (hb : (x.den : ZMod p) = 0) : False := by
  apply hp
  have han : p ∣ x.num.natAbs := by
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num p).mp ha
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hbn := (ZMod.natCast_eq_zero_iff x.den p).mp hb
  have hboth := Nat.dvd_gcd han hbn
  simpa only [x.reduced.gcd_eq_one] using hboth

private theorem check_pair_via_vals (p : ℕ) [NeZero p]
    (F : ZMod p → ZMod p → ZMod p)
    (h : ∀ a b : Fin p, F (a.val : ZMod p) (b.val : ZMod p) = 0 →
      (a.val : ZMod p) = 0 ∧ (b.val : ZMod p) = 0)
    {a b : ZMod p} (h₀ : F a b = 0) : a = 0 ∧ b = 0 := by
  have hn : F ((⟨a.val,a.val_lt⟩ : Fin p).val : ZMod p)
      ((⟨b.val,b.val_lt⟩ : Fin p).val : ZMod p) = 0 := by
    simpa only [ZMod.natCast_zmod_val] using h₀
  simpa only [ZMod.natCast_zmod_val] using h ⟨a.val,a.val_lt⟩ ⟨b.val,b.val_lt⟩ hn


private def fold (z : ℚ) : ℚ := z^3 - 9*z^2 + 18*z - 6
private def foldHom {R : Type*} [CommRing R] (a b : R) : R := a^3 - 9*a^2*b + 18*a*b^2 - 6*b^3

set_option maxRecDepth 8192 in
private theorem fold_finite : ∀ a b : Fin 5,
    foldHom (a.val : ZMod 5) (b.val : ZMod 5) = 0 →
      (a.val : ZMod 5) = 0 ∧ (b.val : ZMod 5) = 0 := by
  decide +kernel

private theorem fold_nonzero (x : ℚ) : fold x ≠ 0 := by
  intro hx
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hscale : x * (x.den : ℚ) = (x.num : ℚ) := by
    nth_rw 1 [← x.num_div_den]
    exact div_mul_cancel₀ _ hden
  have hq : foldHom (x.num : ℚ) (x.den : ℚ) = (x.den : ℚ)^3 * fold x := by
    rw [←hscale]
    simp only [foldHom, fold]
    ring
  rw [hx, mul_zero] at hq
  have hZ : foldHom x.num (x.den : ℤ) = 0 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [foldHom, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Int.cast_zero] using hq
  have hp := congrArg (Int.castRingHom (ZMod 5)) hZ
  have hp' : foldHom (x.num : ZMod 5) (x.den : ZMod 5) = 0 := by
    simp only [foldHom, map_add, map_sub, map_mul, map_pow,
      map_ofNat, map_zero, map_natCast] at hp
    simpa only [foldHom, Int.coe_castRingHom] using hp
  obtain ⟨ha,hb⟩ := check_pair_via_vals 5 foldHom fold_finite hp'
  exact reduced_pair_not_both_zero (by decide) x ha hb

private theorem no_rational_laguerre_root (q : ℚ)
    (h : q^3-9*q^2+18*q-6=0) : False := fold_nonzero q h

/-- This is a theorem of the reviewed rooted-tree order, not a solver
chart or a statement about a generic scalar moment surrogate. -/
theorem rational_all_weights_ne_zero
    {A : Matrix (Fin 8) (Fin 8) ℚ} {b : Fin 8→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) : ∀ i,b i≠0 := by
  intro i hi
  have nonempty : 0<(ghostSet b).card := Finset.card_pos.mpr ⟨i,mem_ghostSet.mpr hi⟩
  have hidden := cubic_hidden_of_ghost_no_sqrt_two ho ha he hγ rational_two_nonsquare nonempty
  let T := activeQuadratureSites b (nodes A)
  have five : 5≤T.card := by
    simpa only [T,show min 5 (7-5/2)=5 by decide] using
      ho.prime_floor_activeQuadratureSites_rat 5 (by decide)
  have cover : ∀ x∈T,∃i : Fin 8,b i≠0 ∧ nodes A i=x := by
    intro x hx
    have live := (mem_activeQuadratureSites_iff.mp hx).2
    by_contra h
    push Not at h
    apply live
    apply Finset.sum_eq_zero
    intro j hj
    by_contra bj
    have jx := (@Finset.mem_filter (Fin 8) (fun k => nodes A k=x)
      (Classical.decPred _) _ _).mp hj
    exact h j bj jx.2
  have pure₃ (v : Fin 8→ℚ) (hv : v∈zeroSpace A 3) : v 2=0 :=
    third_pure_of_hidden_five_clocks ho ha he hγ five cover hidden hv
  exact no_rational_laguerre_root _ (pure_third_clock_laguerre ho ha he hγ pure₃)

/-- The only possible eight-stage rational chart has all eight output
weights nonzero, and precisely two of them negative. -/
theorem rational_support_signature
    {A : Matrix (Fin 8) (Fin 8) ℚ} {b : Fin 8→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) :
    (∀ i,b i≠0) ∧ (negativeSet b).card=2 := by
  have act := rational_all_weights_ne_zero ho ha he hγ
  exact ⟨act,exactly_two_negatives_of_all_active ho ha (fun i=>he i ▸ hγ) act⟩

/-- Conditional strict stage floor: a rational seventh-order method
with a zero output weight needs at least nine physical rows. -/
theorem rational_stage_floor_of_ghost {s : ℕ}
    {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0) (hghost : ∃ i,b i=0) : 9≤s := by
  have floor : 8≤s := by
    simpa only [show nonsingularStageFloor 7=8 by decide] using
      nonsingular_stageFloor_field ho ha (fun i=>he i ▸ hγ) (by decide)
  by_contra short
  have e : s=8 := by omega
  subst s
  obtain ⟨i,hi⟩ := hghost
  exact rational_all_weights_ne_zero ho ha he hγ i hi

/-- Conditional strict stage floor: at most one negative output
weight forces at least nine rows over the rationals. -/
theorem rational_stage_floor_of_at_most_one_negative {s : ℕ}
    {A : Matrix (Fin s) (Fin s) ℚ} {b : Fin s→ℚ} {γ : ℚ}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular)
    (he : ∀ i,A i i=γ) (hγ : γ≠0)
    (few : (Finset.univ.filter (fun i => b i<0)).card≤1) : 9≤s := by
  have floor : 8≤s := by
    simpa only [show nonsingularStageFloor 7=8 by decide] using
      nonsingular_stageFloor_field ho ha (fun i=>he i ▸ hγ) (by decide)
  by_contra short
  have e : s=8 := by omega
  subst s
  have sig := (rational_support_signature ho ha he hγ).2
  change (negativeSet b).card≤1 at few
  omega

end
end RKResearch.Certified.Graded.SDIRKSeven
