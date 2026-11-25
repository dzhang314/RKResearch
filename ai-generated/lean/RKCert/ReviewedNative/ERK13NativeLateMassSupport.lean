module

public import RKCert.ReviewedNative.ERK13NativeLateClassChart
public import RKCert.ReviewedNative.ERK13NativeLatePairSpine
import RKCert.ReviewedNative.MergeEqualRows
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Original signed carrier and original output support at the late seam

An all-target selector argument runs on the actual unmarked rank-sixteen
observer. The folded weights are original fiber sums. The terminal split
changes only a clock-one fiber and never creates a new donor stage. -/

namespace RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold

open RKResearch Reverse Polynomial Module PhysicalCensus ERK13OrdinarySquare
open HyperplaneTerminal NativeFinalThree RKCert.OneEscape RKCert.Endpoint
open scoped Classical Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19 → K}
variable {U : Submodule K (Fin 19 → K)} {w : Fin 19 → K}
variable {P R Q G : K[X]}
variable {e : Fin 18 → Fin 19} {r : Fin 19 → Fin 18} {m : Fin 19}
set_option maxHeartbeats 1800000

abbrev LateFibres (A : Matrix (Fin 19) (Fin 19) K)
    (U : Submodule K (Fin 19 → K)) (w : Fin 19 → K)
    (e : Fin 18 → Fin 19) (r : Fin 19 → Fin 18) : Prop :=
  ∀ i t, r i=t ↔ lateLabel A U w i=lateLabel A U w (e t)

private theorem observer_repr {v : Fin 19 → K} (hv : v∈observerBand A U w) :
    ∃ H J : K[X], ∃ z∈U, H.natDegree≤6 ∧ J.natDegree≤5 ∧
      v=evalNodes A H+weightedEval (nodes A) w J+z := by
  obtain ⟨_,⟨a,rfl⟩,x,hx,eq⟩ := Submodule.mem_sup.mp hv
  let H := ofFn 7 a
  have d : H.natDegree≤6 := Nat.le_of_lt_succ (ofFn_natDegree_lt (by decide) a)
  have form : evalNodes A H=coeffEval A 6 a := by
    rw [evalNodes_eq_coeffEval A H d]
    congr 1
    ext i
    exact ofFn_coeff_eq_val_of_lt _ i.isLt
  obtain ⟨z,hz,J,jd,split⟩ := HeadFiber.exists_poly hx
  have bj : J.natDegree<6 := by
    by_cases j0 : J=0
    · simp [j0]
    · exact (natDegree_lt_iff_degree_lt j0).mpr jd
  refine ⟨H,J,z,hz,d,Nat.le_of_lt_succ bj,?_⟩
  rw [←eq,←form,split]
  abel

/-- Every distinct noncore pair is tested, not only a clock-one target
with nonzero mesh. Common roots and the zero polynomial Q are included. -/
theorem noncore_selector_not_in_observer (S : MassClassChart A U w P R Q G)
    {i : Fin 19} (dead : ¬LiveCore.live U i) :
    (labelIndicator (phaseLabel A U w) (phaseLabel A U w i) : Fin 19 → K) ∉
      observerBand A U w := by
  intro sel
  obtain ⟨u,hu,square⟩ := S.square
  obtain ⟨v,hv,mesh⟩ := S.mesh
  let T := noncorePairs A U w
  have meshP (p : K×K) (hp : p∈T) : G.eval p.1=Q.eval p.1*p.2 := by
    obtain ⟨j,dj,rfl⟩ := mem_noncorePairs.mp hp
    have eq := congrFun mesh j
    simpa only [headPair,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live dj hv,add_zero] using eq
  have squareP (p : K×K) (hp : p∈T) : p.2^2=R.eval p.1*p.2+P.eval p.1 := by
    obtain ⟨j,dj,rfl⟩ := mem_noncorePairs.mp hp
    have eq := congrFun square j
    simpa only [headPair,pow_two,Pi.mul_apply,evalNodes_apply,weightedEval_apply,Pi.add_apply,
      LiveCore.val_eq_zero_of_not_live dj hu,add_zero,zero_add,add_comm] using eq
  obtain ⟨H,J,z,hz,dH,dJ,form⟩ := observer_repr sel
  have inside : headPair A w i∈T := mem_noncorePairs.mpr ⟨i,dead,rfl⟩
  have fit (p : K×K) (hp : p∈T) :
      H.eval p.1+J.eval p.1*p.2=(if p=headPair A w i then 1 else 0) := by
    obtain ⟨j,dj,rfl⟩ := mem_noncorePairs.mp hp
    have eq := congrFun form j
    have pairIff := dead_pair_label_iff (A:=A) (w:=w) dj dead
    by_cases pair : headPair A w j=headPair A w i
    · have label := pairIff.mpr pair
      rw [if_pos pair]
      simpa only [headPair,labelIndicator,evalNodes_apply,weightedEval_apply,Pi.add_apply,
        LiveCore.val_eq_zero_of_not_live dj hz,add_zero,if_pos label] using eq.symm
    · have label : phaseLabel A U w j≠phaseLabel A U w i := fun h=>pair (pairIff.mp h)
      rw [if_neg pair]
      simpa only [headPair,labelIndicator,evalNodes_apply,weightedEval_apply,Pi.add_apply,
        LiveCore.val_eq_zero_of_not_live dj hz,add_zero,if_neg label] using eq.symm
  exact NativeQuadraticClassSelector.no_grade_nine_selector S.noncoreCount meshP squareP
    S.gDegree S.qDegree S.rDegree S.pDegree S.leading dH dJ inside fit

private theorem delta_zero_at_or_after (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j=0) {i : Fin 19} (mi : m ≤ i) :
    rowDelta A e r m i=0 := by
  simp only [rowDelta,ha m i mi,ha (e (r m)) i ((chart.earlier m).trans mi),sub_self]

theorem delta_zero_last (chart : PairClasses e r m) (ha : ∀ i j, i ≤ j → A i j=0) :
    rowDelta A e r m (Fin.last 18)=0 :=
  delta_zero_at_or_after chart ha (Fin.le_last m)

private theorem delta_nonzero (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) :
    rowDelta A e r m≠0 := by
  intro zero
  have rows (j : Fin 19) : A (e (r m)) j=A m j :=
    (sub_eq_zero.mp (congrFun zero j)).symm
  obtain ⟨B,z,hB,hO⟩ := exists_merge_equal_rows (n:=18) ha ho
    (lt_of_le_of_ne (chart.earlier m) chart.omitted) rows
  exact (by decide : ¬(19≤18)) (ERK13NativeFirst.stage_floor19 hB hO)

private theorem rho_off_one_ne (ha : ∀ i j, i ≤ j → A i j=0)
    (live : b m≠0) (off : reflectedClock A m≠0)
    (tail : ∀ i, m < i → b i*reflectedClock A i=0) :
    reflectedStageRow A b 1 m≠0 := by
  have cut : mat A.transpose (reflectedStageWeight A b 1) m=0 := by
    change (∑ j : Fin 19, A j m*(b j*reflectedClock A j^1))=0
    simp only [pow_one]
    apply Finset.sum_eq_zero
    intro j _
    by_cases le : j ≤ m
    · rw [ha j m le,zero_mul]
    · rw [tail j (lt_of_not_ge le),mul_zero]
  change (((1+1:ℕ):K)*mat A.transpose (reflectedStageWeight A b 1) m -
    b m*reflectedClock A m^2)≠0
  rw [cut,mul_zero,zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero live (pow_ne_zero _ off))

/-- The actual difference D represents the unique unmarked observer
annihilator modulo the two literal within-class contrasts. -/
theorem observer_annihilator_split (S : MassClassChart A U w P R Q G)
    (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    {rad : ℕ} {V : Submodule K (Fin 19→K)} {v : Fin 19→K}
    (head : ERK13NativeFirst.NativePaidHead A b rad V v)
    (live : b m≠0) (off : reflectedClock A m≠0)
    (tail : ∀ i, m < i → b i*reflectedClock A i=0)
    (inTwo : rowDelta A e r m∈primitiveBack A b 2) :
    annih (observerBand A U w) =
      annih (unmarkedClasses A U w) ⊔ K∙rowDelta A e r m := by
  let D := rowDelta A e r m
  let B := unmarkedClasses A U w
  let J := observerBand A U w
  let rho := reflectedStageRow A b 1
  have dJ : D∈annih J :=
    annih_antitone S.observerPay (primitiveBack_annih ho 9 2 (by decide) inTwo)
  have dOut : D∉annih B := by
    intro dB
    have rank10 :=
      (ERK13NativeFirst.marked_staircase_ranks13 ha ho head seed).1 10 (by decide) (by decide)
    obtain ⟨eq₁,rk₁⟩ := ERK13NativeFirst.exact_marked_reverse13 ha ho
      (ERK13NativeFirst.last_original_active ha ho) seed (by decide : 10≤11) rank10
    change primitiveBack A b 1=annih (markedTreeSpace A b 10) at eq₁
    change finrank K (primitiveBack A b 1)=1 at rk₁
    have dmark : D∈annih (markedTreeSpace A b 10) := by
      rw [late_union_marked S ha ho seed head,annih_sup_coordinate,mem_zeroAt]
      exact ⟨dB,delta_zero_last chart ha⟩
    have rhoM : rho m≠0 := rho_off_one_ne ha live off tail
    have rhoN : rho≠0 := fun z=>rhoM (congrFun z m)
    have rhoMemb : rho∈primitiveBack A b 1 :=
      adjointFlag_credit _ 0 (monomial_mem_credit 0 1 le_rfl)
    have line : primitiveBack A b 1=K∙rho := by
      symm
      apply Submodule.eq_of_le_of_finrank_le
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr rhoMemb
      · rw [finrank_span_singleton rhoN,rk₁]
    rw [←eq₁,line] at dmark
    obtain ⟨c,ce⟩ := Submodule.mem_span_singleton.mp dmark
    have cm : c*rho m=0 := by
      have test := congrFun ce m
      change c*rho m=D m at test
      exact test.trans (delta_zero_at_or_after chart ha le_rfl)
    have cz := (mul_eq_zero.mp cm).resolve_right rhoM
    exact delta_nonzero chart ha ho (by simpa only [cz,zero_smul] using ce.symm)
  change annih J=annih B⊔K∙D
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact sup_le (annih_antitone S.observerInside) ((Submodule.span_singleton_le_iff_mem _ _).mpr dJ)
  · have jCap := finrank_annih J
    have bCap := finrank_annih B
    rw [Fintype.card_fin] at jCap bCap
    have jRank : finrank K J=16 := S.observerRank
    have bRank : finrank K B=17 := S.unmarkedRank
    rw [Submodule.finrank_sup_span_singleton dOut]
    omega

/-- No signed **unmarked** noncore class sum of D is zero. This is an
original coordinate pairing, including both copies before the split. -/
theorem all_noncore_pairings_ne (S : MassClassChart A U w P R Q G)
    (split : annih (observerBand A U w) =
      annih (unmarkedClasses A U w) ⊔ K∙rowDelta A e r m)
    {i : Fin 19} (dead : ¬LiveCore.live U i) :
    row (rowDelta A e r m) (labelIndicator (phaseLabel A U w) (phaseLabel A U w i))≠0 := by
  intro zero
  apply noncore_selector_not_in_observer S dead
  rw [←annih_annih (observerBand A U w)]
  apply mem_annih.mpr
  intro v hv
  rw [split] at hv
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  let f : Fin 19 → K := labelIndicator (phaseLabel A U w) (phaseLabel A U w i)
  change row f (u+c • rowDelta A e r m)=0
  rw [row_apply,dotProduct_comm,add_dotProduct,smul_dotProduct,smul_eq_mul]
  change row u f + c*row (rowDelta A e r m) f=0
  have zu : row u f=0 := mem_annih.mp hu f (phase_indicator_mem i)
  have zd : row (rowDelta A e r m) f=0 := zero
  rw [zu,zd,mul_zero,add_zero]

theorem unmarked_core_mass_zero (S : MassClassChart A U w P R Q G)
    (ho : HasOrder 13 A b) {i : Fin 19} (live : LiveCore.live U i) :
    row b (labelIndicator (phaseLabel A U w) (phaseLabel A U w i))=0 := by
  have pay : probe A b 0 (labelIndicator (phaseLabel A U w) (phaseLabel A U w i))=0 :=
    probe_zeroSpace (k:=0) ho (by decide : 0+4+1≤13)
    (S.coreFour (phase_core_indicator S live))
  simpa only [probe,pow_zero,mul_one] using pay

private theorem core_in_observer : U≤observerBand A U w := by
  have hc := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) 6).mp le_rfl
  exact hc.1.trans le_sup_right

theorem unmarked_core_pairing_zero (S : MassClassChart A U w P R Q G)
    (ho : HasOrder 13 A b) (inTwo : rowDelta A e r m∈primitiveBack A b 2)
    {i : Fin 19} (live : LiveCore.live U i) :
    row (rowDelta A e r m) (labelIndicator (phaseLabel A U w) (phaseLabel A U w i))=0 :=
  mem_annih.mp (primitiveBack_annih ho 9 2 (by decide) inTwo) _
    (S.observerPay (core_in_observer (phase_core_indicator S live)))

theorem fold_at_coordinate (u : Fin 19 → K) (t : Fin 18) :
    foldLinear r u t=row u (fun i=>coordinate (K:=K) t (r i)) := by
  change folded r u t=_
  rw [←row_coordinate (folded r u) t,folded_pair]

theorem nonlast_representative (fibres : LateFibres A U w e r)
    {i : Fin 19} (off : i≠Fin.last 18) : e (r i)≠Fin.last 18 := by
  intro bad
  have eq := (fibres i (r i)).mp rfl
  have bit := congrArg Prod.snd eq
  change decide (i=Fin.last 18)=decide (e (r i)=Fin.last 18) at bit
  have bi : decide (i=Fin.last 18)=false := decide_eq_false_iff_not.mpr off
  have be : decide (e (r i)=Fin.last 18)=true := decide_eq_true_eq.mpr bad
  rw [bi,be] at bit
  cases bit

private theorem support_coordinate_eq (t j : Fin 18) :
    coordinate (K:=K) t j = if j=t then 1 else 0 := by
  classical
  by_cases h : j=t
  · subst j
    simp [coordinate]
  · simp [coordinate,h,Ne.symm h]

/-- A nonterminal marked fiber differs from its unmarked one only at the
literal last row. Either its weight is zero there or that row is outside
the unmarked fiber. These are the exact rules for erasing the mark. -/
theorem fold_eq_unmarked (fibres : LateFibres A U w e r)
    (u : Fin 19 → K) (t : Fin 18) (notLast : e t≠Fin.last 18)
    (quiet : u (Fin.last 18)=0 ∨
      phaseLabel A U w (Fin.last 18)≠phaseLabel A U w (e t)) :
    foldLinear r u t=row u (labelIndicator (phaseLabel A U w) (phaseLabel A U w (e t))) := by
  rw [fold_at_coordinate]
  simp only [row_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp only [labelIndicator]
  rw [support_coordinate_eq]
  by_cases off : i=Fin.last 18
  · subst i
    rcases quiet with z|nl
    · simp only [z,zero_mul]
    · have no : r (Fin.last 18)≠t := by
        intro hp
        exact nl (congrArg Prod.fst ((fibres _ _).mp hp))
      rw [if_neg no,if_neg nl]
  · have pairIff := (fibres i t).trans (late_label_off_last (A:=A) (U:=U) (w:=w) off notLast)
    by_cases eq : r i=t
    · rw [if_pos eq,if_pos (pairIff.mp eq)]
    · have ne : phaseLabel A U w i≠phaseLabel A U w (e t) := fun h=>eq (pairIff.mpr h)
      rw [if_neg eq,if_neg ne]

/-- Off the terminal clock the real core has zero grouped output and zero
grouped carrier. The all-target selector supplies the complementary implication. -/
theorem mass_support_and_offcore (S : MassClassChart A U w P R Q G)
    (fibres : LateFibres A U w e r)
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 13 A b) (seed : firstSeed A b=0)
    (inTwo : rowDelta A e r m∈primitiveBack A b 2)
    (split : annih (observerBand A U w) = annih (unmarkedClasses A U w)⊔K∙rowDelta A e r m) :
    (∀ t, foldLinear r (rowDelta A e r m) t=0 →
      foldLinear r b t*reflectedClock A (e t)=0) ∧
    (∀ t, reflectedClock A (e t)≠0 → foldLinear r (rowDelta A e r m) t≠0 →
      ¬LiveCore.live U (e t)) := by
  have lastY : reflectedClock A (Fin.last 18)=0 := by
    change (1:K)-nodes A (Fin.last 18)=0
    rw [(ERK13NativeFirst.last_original_active ha ho).node_eq_one ha seed,sub_self]
  have quiet (t : Fin 18) (off : reflectedClock A (e t)≠0) :
      e t≠Fin.last 18 ∧ phaseLabel A U w (Fin.last 18)≠phaseLabel A U w (e t) := by
    refine ⟨fun eq=>off (eq.symm ▸ lastY),fun eq=>?_⟩
    have c := (phase_clock_head S eq).1
    exact off (by simpa only [reflectedClock,Pi.sub_apply,Pi.one_apply,c] using lastY)
  constructor
  · intro t zero
    by_cases y : reflectedClock A (e t)=0
    · rw [y,mul_zero]
    obtain ⟨nl,np⟩ := quiet t y
    by_cases li : LiveCore.live U (e t)
    · rw [fold_eq_unmarked fibres b t nl (Or.inr np),unmarked_core_mass_zero S ho li,zero_mul]
    · exact (all_noncore_pairings_ne S split li
        ((fold_eq_unmarked fibres (rowDelta A e r m) t nl (Or.inr np)).symm.trans zero)).elim
  · intro t y nz li
    obtain ⟨nl,np⟩ := quiet t y
    exact nz ((fold_eq_unmarked fibres (rowDelta A e r m) t nl (Or.inr np)).trans
      (unmarked_core_pairing_zero S ho inTwo li))

/-- All fourteen noncore pairs still have a nonzero signed carrier on
some marked fiber. The only split row has D_L=0, even at clock one. -/
theorem fourteen_carrier_sites (S : MassClassChart A U w P R Q G)
    (fibres : LateFibres A U w e r) (chart : PairClasses e r m)
    (ha : ∀ i j, i ≤ j → A i j=0)
    (split : annih (observerBand A U w) = annih (unmarkedClasses A U w)⊔K∙rowDelta A e r m) :
    14≤(unionSupport (foldLinear r b) (fun t=>reflectedClock A (e t))
      (foldLinear r (rowDelta A e r m))).card := by
  classical
  let D := rowDelta A e r m
  let T := unionSupport (foldLinear r b) (fun t=>reflectedClock A (e t)) (foldLinear r D)
  have repl (i : Fin 19) : ∃ j, j≠Fin.last 18 ∧
      phaseLabel A U w j=phaseLabel A U w i := by
    by_cases hi : i=Fin.last 18
    · subst i
      exact exists_terminal_twin S
    · exact ⟨i,hi,rfl⟩
  have inside : noncorePairs A U w ⊆ T.image (fun t=>headPair A w (e t)) := by
    intro p hp
    obtain ⟨i,dead,ip⟩ := mem_noncorePairs.mp hp
    obtain ⟨j,jl,jp⟩ := repl i
    let t := r j
    have same : phaseLabel A U w (e t)=phaseLabel A U w i :=
      (congrArg Prod.fst ((fibres j t).mp rfl)).symm.trans jp
    have eq := fold_eq_unmarked fibres D t (nonlast_representative fibres jl)
      (Or.inl (delta_zero_last chart ha))
    have nz : foldLinear r D t≠0 := by
      rw [eq,same]
      exact all_noncore_pairings_ne S split dead
    have hp' := phase_clock_head S same
    have dPair : headPair A w (e t)=headPair A w i := Prod.ext hp'.1 hp'.2
    have realPair : headPair A w (e t)=p := dPair.trans ip
    exact Finset.mem_image.mpr ⟨t,mem_unionSupport.mpr (Or.inl nz),realPair⟩
  calc
    14=(noncorePairs A U w).card := S.noncoreCount.symm
    _≤(T.image (fun t=>headPair A w (e t))).card := Finset.card_le_card inside
    _≤T.card := Finset.card_image_le

end
end RKResearch.Certified.Graded.ERK13NativeLatePhysicalFold
