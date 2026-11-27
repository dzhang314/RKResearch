module

public import RKCert.ReviewedNative.ERK8PaidCleanShape
public import RKCert.ReviewedNative.ERKTaggedHorizonSupport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! # Actual clean chronological primitive producer, ERK8 four-off

Source-only draft. The expected Marked-side receipts are the literal clean
placement, two interior clean masses, and tag constancy in E5. The actual
quartic terminal profile is an independent E4 prerequisite, not a Newton
transfer assumption. No off-degree drop or scalar contradiction is used here.
-/
namespace RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped BigOperators Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

abbrev lastPhysical : Fin 10 := Fin.last 9

/-- Aggregate only the clean tag, even if an off tag has the same clock. -/
noncomputable def cleanMass (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K) (u : K) : K :=
  ∑ j, if g A j = 0 ∧ nodes A j = u then b j else 0

/-- These are the only placement facts the clean producer consumes.
No ordering of numerical clocks, duplicate row identity, or branch index is used. -/
structure CleanPrimitivePlacement (A : Matrix (Fin 10) (Fin 10) K) (b : Fin 10 → K)
    (iH iX : Fin 10) (z : K) : Prop where
  terminal_clean : g A lastPhysical = 0
  terminal_clock : nodes A lastPhysical = 1
  h_clean : g A iH = 0
  x_clean : g A iX = 0
  before_h : ∀ j, j < iH → g A j=0 → nodes A j=0
  before_x : ∀ j, j < iX → g A j=0 → nodes A j=0 ∨ nodes A j=nodes A iH
  clean_values : ∀ j, g A j=0 →
    nodes A j=0 ∨ nodes A j=nodes A iH ∨ nodes A j=nodes A iX ∨ nodes A j=z ∨ nodes A j=1
  h_mass : cleanMass A b (nodes A iH) ≠ 0
  x_mass : cleanMass A b (nodes A iX) ≠ 0
  tagged5 : treeSpace A 5 ≤ onOffSpace A
  roots : CleanClocks (nodes A iH) (nodes A iX) z
  quartic_id : quartic (nodes A iH) (nodes A iX) z = (X:K[X])*LobattoEight.lobattoCubic

/-- Independent terminal E4 receipt. The chronological/weighted producer
can normalize the pure part to Q using only the ordinary terminal profile. -/
structure CleanTerminalProfile (A : Matrix (Fin 10) (Fin 10) K) (Q R : K[X]) : Prop where
  degR : R.natDegree ≤ 2
  profile : evalNodes A Q+diag (g A) (evalNodes A R)=Q.eval 1 • Pi.single lastPhysical 1

/-- Clean-sender mask on actual rows; not a merged tableau. -/
noncomputable def cleanInput (A : Matrix (Fin 10) (Fin 10) K) (P : K[X]) : Fin 10 → K :=
  fun j => if g A j=0 then P.eval (nodes A j) else 0

private theorem clean_value_congr {v : Fin 10 → K} (tag : v ∈ onOffSpace A)
    {i j : Fin 10} (hi : g A i=0) (hj : g A j=0) (eq : nodes A i=nodes A j) : v i=v j := by
  obtain ⟨f,rfl⟩ := tag
  rw [onOffEval_on A f hi,onOffEval_on A f hj]
  exact congrArg f.1 (Subtype.ext eq)

/-- A paid degree-two selector isolates one clean tagged value. Off emissions
are summed per actual off tag; a coincident clean clock is not discarded. -/
private theorem target_zero_of_paid_cut (ho : HasOrder 8 A b)
    (cancel : ∀ u∈offKnots A, offMass A b u=0)
    {v : Fin 10 → K} (hv : v ∈ zeroSpace A 5) (tag : v ∈ onOffSpace A)
    {i : Fin 10} (hi : g A i=0) (mass : cleanMass A b (nodes A i) ≠ 0)
    (T : K[X]) (hd : T.natDegree ≤ 2) (tn : T.eval (nodes A i) ≠ 0)
    (cut : ∀ j, g A j=0 → nodes A j≠nodes A i → v j*T.eval (nodes A j)=0) : v i=0 := by
  obtain ⟨f,hf⟩ := tag
  let S := offKnots A
  let ofv : K → K := fun u => if hu : u ∈ S then f.2 ⟨u,hu⟩*T.eval u else 0
  have parts (j : Fin 10) : b j*(v j*T.eval (nodes A j)) =
      (if g A j=0 ∧ nodes A j=nodes A i then b j else 0)*(v i*T.eval (nodes A i)) +
      ∑ u∈S, (if g A j≠0 ∧ nodes A j=u then b j else 0)*ofv u := by
    by_cases hj : g A j=0
    · by_cases jc : nodes A j=nodes A i
      · have same : v j=v i := clean_value_congr ⟨f,hf⟩ hj hi jc
        simp [hj,jc,same]
      · simp [hj,jc,cut j hj jc]
    · have hm : nodes A j∈S := mem_offKnots.mpr ⟨j,hj,rfl⟩
      rw [Finset.sum_eq_single (nodes A j)]
      · rw [←hf,onOffEval_off A f hj]
        simp [hj,ofv,hm]
      · intro u _ hu
        simp [Ne.symm hu]
      · intro no
        exact (no hm).elim
  have ofzero : (∑ j : Fin 10, ∑ u∈S, (if g A j≠0 ∧ nodes A j=u then b j else 0)*ofv u)=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro u hu
    rw [←Finset.sum_mul]
    change offMass A b u * ofv u=0
    rw [cancel u hu,zero_mul]
  have mem : v*evalNodes A T∈zeroSpace A 7 :=
    zeroSpace_mul_treeSpace ho (m:=5) (n:=2) (by decide) hv (evalNodes_mem_treeSpace A T hd)
  have pay : probe A b 0 (v*evalNodes A T)=0 :=
    probe_zeroSpace ho (j:=7) (k:=0) (by decide) mem
  have total : (∑ j : Fin 10, b j*(v j*T.eval (nodes A j)))=0 := by
    simpa only [probe,row_apply,dotProduct,pow_zero,mul_one,Pi.mul_apply,evalNodes_apply] using pay
  have total' : (∑ j : Fin 10, b j*(v j*T.eval (nodes A j))) =
      cleanMass A b (nodes A i)*(v i*T.eval (nodes A i)) := by
    simp only [parts,Finset.sum_add_distrib,ofzero,add_zero,cleanMass,Finset.sum_mul]
  rw [total'] at total
  exact (mul_eq_zero.mp ((mul_eq_zero.mp total).resolve_left mass)).resolve_right tn

private theorem clean_value_zero_of_anchors (ho : HasOrder 8 A b)
    (cancel : ∀ u∈offKnots A, offMass A b u=0)
    {v : Fin 10 → K} (hv : v ∈ zeroSpace A 5) (tag : v ∈ onOffSpace A)
    (c0 : g A 0=0) (n0 : nodes A 0=0) (v0 : v 0=0)
    (ct : g A lastPhysical=0) (nt : nodes A lastPhysical=1) (vt : v lastPhysical=0)
    {i : Fin 10} (hi : g A i=0) (mass : cleanMass A b (nodes A i)≠0)
    (u w : K) (nu : nodes A i≠u) (nw : nodes A i≠w)
    (cover : ∀ j, g A j=0 →
        nodes A j=0 ∨ nodes A j=1 ∨ nodes A j=nodes A i ∨ nodes A j=u ∨ nodes A j=w) :
    v i=0 := by
  let T : K[X] := (X-C u)*(X-C w)
  have hd : T.natDegree≤2 := natDegree_mul_le_of_le (natDegree_X_sub_C_le u) (natDegree_X_sub_C_le w)
  have nz : T.eval (nodes A i)≠0 := by
    simp only [T,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_ne_zero (sub_ne_zero.mpr nu) (sub_ne_zero.mpr nw)
  apply target_zero_of_paid_cut ho cancel hv tag hi mass T hd nz
  intro j hj jne
  rcases cover j hj with h0 | ht | he | hu | hw
  · have e := clean_value_congr tag hj c0 (h0.trans n0.symm)
    rw [e,v0,zero_mul]
  · have e := clean_value_congr tag hj ct (ht.trans nt.symm)
    rw [e,vt,zero_mul]
  · exact (jne he).elim
  · simp [T,hu]
  · simp [T,hw]

private theorem last_column_zero (ha : ∀ j l, j≤l → A j l=0) :
    mat A (Pi.single lastPhysical (1:K))=0 := by
  ext i
  change mat A (Pi.single lastPhysical (1:K)) i=0
  refine causal_mat ha i _ (fun j hj => ?_)
  have hne : j≠lastPhysical := by
    intro he
    subst j
    exact (not_lt_of_ge (Fin.le_last i)) hj
  simp [Pi.single_apply,hne,hne.symm]

/-- The terminal constraint puts the whole physical pure primitive column in F5. -/
private theorem quartic_primitive_mem (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2) (Q R : K[X]) (hd : Q.natDegree≤4)
    (F : CleanTerminalProfile A Q R) : evalNodes A (primitive Q) ∈ zeroSpace A 5 := by
  have off : diag (g A) (evalNodes A R) ∈ zeroSpace A 4 := by
    rw [hF]
    exact band_iff.mpr ⟨R,F.degR,rfl⟩
  have step : mat A (diag (g A) (evalNodes A R)) ∈ zeroSpace A 5 :=
    mat_zeroSpace ho 4 (by decide) off
  have dif := primitive_defect_paid ho Q (q:=4) hd (by decide)
  have mem := (zeroSpace A 5).add_mem dif step
  have eq : (mat A (evalNodes A Q)-evalNodes A (primitive Q))+
      mat A (diag (g A) (evalNodes A R))=-(evalNodes A (primitive Q)) := by
    calc
      _ = mat A (evalNodes A Q+diag (g A) (evalNodes A R))-evalNodes A (primitive Q) := by
        rw [map_add]
        abel
      _ = _ := by rw [F.profile,map_smul,last_column_zero ha,smul_zero,zero_sub]
  rw [eq] at mem
  simpa using (zeroSpace A 5).neg_mem mem

private theorem lobatto_primitive_one_ne (ho : HasOrder 8 A b) :
    (primitive ((X:K[X])*LobattoEight.lobattoCubic)).eval 1 ≠ 0 := by
  have n2 := ERK8PaidField.two_ne ho
  have n14 := fourteen_ne ho
  have n3 : (3:K)≠0 := (ho.natCast_isUnit (n:=3) (by decide) (by decide)).ne_zero
  have n4 : (4:K)≠0 := (ho.natCast_isUnit (n:=4) (by decide) (by decide)).ne_zero
  have n5 : (5:K)≠0 := (ho.natCast_isUnit (n:=5) (by decide) (by decide)).ne_zero
  have c0 : ((-1:K)/14)*14=-1 := div_mul_cancel₀ _ n14
  have c1 : ((9:K)/14)*14=9 := div_mul_cancel₀ _ n14
  have c2 : ((-3:K)/2)*2=-3 := div_mul_cancel₀ _ n2
  have e0 : (((-1:K)/14)/2)*2=(-1)/14 := div_mul_cancel₀ _ n2
  have e1 : (((9:K)/14)/3)*3=9/14 := div_mul_cancel₀ _ n3
  have e2 : (((-3:K)/2)/4)*4=(-3)/2 := div_mul_cancel₀ _ n4
  have e3 : ((1:K)/5)*5=1 := div_mul_cancel₀ _ n5
  intro z
  simp only [LobattoEight.lobattoCubic,mul_add,X_mul_monomial,map_add,primitive_monomial,
    eval_add,eval_monomial,one_pow,mul_one,Nat.reduceAdd,Nat.cast_ofNat] at z
  apply n3
  linear_combination 840*z-420*e0-280*e1-210*e2-168*e3-30*c0-20*c1-105*c2

private theorem one_theta_at_both_clean_rows (ha : ∀ j l, j≤l → A j l=0)
    (ho : HasOrder 8 A b) (cancel : ∀ u∈offKnots A, offMass A b u=0)
    {iH iX : Fin 10} {z : K} (L : CleanPrimitivePlacement A b iH iX z)
    {w : Fin 10 → K} (hw : w ∈ zeroSpace A 5)
    (phi_mem : evalNodes A (primitive (quartic (nodes A iH) (nodes A iX) z)) ∈ zeroSpace A 5) :
    ∃ theta,
      w iH=theta*(primitive (quartic (nodes A iH) (nodes A iX) z)).eval (nodes A iH) ∧
      w iX=theta*(primitive (quartic (nodes A iH) (nodes A iX) z)).eval (nodes A iX) := by
  let h := nodes A iH
  let x := nodes A iX
  let phi := primitive (quartic h x z)
  have p1 : phi.eval 1≠0 := by
    change (primitive (quartic (nodes A iH) (nodes A iX) z)).eval 1≠0
    rw [L.quartic_id]
    exact lobatto_primitive_one_ne ho
  let theta := w lastPhysical / phi.eval 1
  let v := w-theta • evalNodes A phi
  have mem : v∈zeroSpace A 5 := (zeroSpace A 5).sub_mem hw ((zeroSpace A 5).smul_mem _ phi_mem)
  have tagged : v∈onOffSpace A := L.tagged5 (zeroSpace_le_treeSpace A 5 mem)
  have c0 : g A 0=0 := origin_zeroSpace (s:=9) ha 2 (mDef_mem A 1)
  have n0 : nodes A (0:Fin 10)=0 := by
    change (∑ j, A 0 j * 1)=0
    exact Finset.sum_eq_zero fun j _ => by rw [ha 0 j (Fin.zero_le _),zero_mul]
  have v0 : v 0=0 := origin_zeroSpace (s:=9) ha 5 mem
  have vt : v lastPhysical=0 := by
    change w lastPhysical-theta*phi.eval (nodes A lastPhysical)=0
    rw [L.terminal_clock]
    dsimp only [theta]
    rw [div_mul_cancel₀ _ p1,sub_self]
  have VH : v iH=0 := by
    apply clean_value_zero_of_anchors ho cancel mem tagged c0 n0 v0
      L.terminal_clean L.terminal_clock vt L.h_clean L.h_mass x z L.roots.h_ne_x L.roots.h_ne_z
    intro j hj
    rcases L.clean_values j hj with c0 | ch | cx | cz | c1
    · exact Or.inl c0
    · exact Or.inr (Or.inr (Or.inl ch))
    · exact Or.inr (Or.inr (Or.inr (Or.inl cx)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr cz)))
    · exact Or.inr (Or.inl c1)
  have VX : v iX=0 := by
    apply clean_value_zero_of_anchors ho cancel mem tagged c0 n0 v0
      L.terminal_clean L.terminal_clock vt L.x_clean L.x_mass h z L.roots.h_ne_x.symm L.roots.x_ne_z
    intro j hj
    rcases L.clean_values j hj with c0 | ch | cx | cz | c1
    · exact Or.inl c0
    · exact Or.inr (Or.inr (Or.inr (Or.inl ch)))
    · exact Or.inr (Or.inr (Or.inl cx))
    · exact Or.inr (Or.inr (Or.inr (Or.inr cz)))
    · exact Or.inr (Or.inl c1)
  change w iH-theta*phi.eval h=0 at VH
  change w iX-theta*phi.eval x=0 at VX
  exact ⟨theta,sub_eq_zero.mp VH,sub_eq_zero.mp VX⟩

private theorem clean_tap_residual_mem (ho : HasOrder 8 A b) (hF : zeroSpace A 4=band A 2)
    (P : K[X]) (hd : P.natDegree≤2) (h : K)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j) :
    evalNodes A (primitive (tapFactor h*P))-mat A (cleanInput A (tapFactor h*P))∈zeroSpace A 5 := by
  let S := tapFactor h*P
  let off := diag (g A) (evalNodes A (tapFactor h))
  have split : evalNodes A S=cleanInput A S+off := by
    ext j
    by_cases hj : g A j=0
    · simp [cleanInput,off,hj]
    · simp [cleanInput,off,S,hj,fit j hj,mul_comm]
  have ofmem : off∈zeroSpace A 4 := by
    rw [hF]
    exact band_iff.mpr ⟨tapFactor h,tapFactor_degree_le h,rfl⟩
  have ofimg : mat A off∈zeroSpace A 5 := mat_zeroSpace ho 4 (by decide) ofmem
  have pd := primitive_defect_paid ho S (q:=4) (natDegree_mul_le_of_le (tapFactor_degree_le h) hd) (by decide)
  have eq : evalNodes A (primitive S)-mat A (cleanInput A S)=
      mat A off-(mat A (evalNodes A S)-evalNodes A (primitive S)) := by
    have act := congrArg (mat A) split
    rw [map_add] at act
    rw [act]
    abel
  change evalNodes A (primitive S)-mat A (cleanInput A S)∈zeroSpace A 5
  rw [eq]
  exact (zeroSpace A 5).sub_mem ofimg pd

/-- The local first-clean XP test is automatic, without a P(0)=0 premise. -/
theorem primitive_X_head_zero_of_clean_prefix_paid (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2) {i : Fin 10} (hi : g A i=0)
    (pre : ∀ j, j < i → g A j=0 → nodes A j=0)
    {P : K[X]} (hd : P.natDegree≤2)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j) :
    (primitive (X*P)).eval (nodes A i)=0 := by
  have dX : (X*P).natDegree≤3 := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) hd
  exact on_primitive_zero_paid ha ho hF hi (X*P) dX
    (diag (nodes A) (g A)) (clean_mixed_defect_paid ho hF hi) (fun j hj => by
      by_cases hj' : g A j=0
      · simp [hj',pre j hj hj']
      · simp [fit j hj'])

/-- Produce the common theta from literal physical clean primitive actions. -/
theorem shared_clean_primitive (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2)
    (cancel : ∀ u∈offKnots A, offMass A b u=0)
    {iH iX : Fin 10} {z : K} (L : CleanPrimitivePlacement A b iH iX z)
    {P R : K[X]} (hd : P.natDegree≤2)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    (term : CleanTerminalProfile A (quartic (nodes A iH) (nodes A iX) z) R) :
    let h := nodes A iH
    let x := nodes A iX
    ∃ theta,
      (primitive (tapFactor h*P)).eval h=theta*(primitive (quartic h x z)).eval h ∧
      (primitive (tapFactor h*P)).eval x=theta*(primitive (quartic h x z)).eval x := by
  let h := nodes A iH
  let x := nodes A iX
  let S := tapFactor h*P
  let w := evalNodes A (primitive S)-mat A (cleanInput A S)
  have hm : w∈zeroSpace A 5 := clean_tap_residual_mem ho hF P hd h fit
  have phi := quartic_primitive_mem ha ho hF (quartic h x z) R (quartic_degree_le h x z) term
  obtain ⟨theta,hh,hx⟩ := one_theta_at_both_clean_rows ha ho cancel L hm phi
  have Hact : mat A (cleanInput A S) iH=0 := by
    refine causal_mat ha iH _ (fun j hj => ?_)
    by_cases hj' : g A j=0
    · simp [cleanInput,hj',S,tapFactor,L.before_h j hj hj']
    · simp [cleanInput,hj']
  have Xact : mat A (cleanInput A S) iX=0 := by
    refine causal_mat ha iX _ (fun j hj => ?_)
    by_cases hj' : g A j=0
    · rcases L.before_x j hj hj' with h0 | hh'
      · simp [cleanInput,hj',S,tapFactor,h0]
      · simp [cleanInput,hj',S,tapFactor,hh',h]
    · simp [cleanInput,hj']
  refine ⟨theta,?_,?_⟩
  · simpa only [w,Pi.sub_apply,evalNodes_apply,Hact,sub_zero] using hh
  · simpa only [w,Pi.sub_apply,evalNodes_apply,Xact,sub_zero] using hx

/-- Paid finite-characteristic clean shape from genuine tagged placement.
In contrast to NormalizedShape, the scale and quadratic term may vanish. -/
theorem raw_clean_shape_from_actual_prefix (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2) (nOff : (offKnots A).card=4)
    {iH iX : Fin 10} {z : K} (L : CleanPrimitivePlacement A b iH iX z)
    {P R : K[X]} (hd : P.natDegree≤2)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    (term : CleanTerminalProfile A (quartic (nodes A iH) (nodes A iX) z) R) :
    ∃ theta k, RawPaidShape P (nodes A iH) (nodes A iX) z theta k := by
  have cancel := offMass_zero_of_head ho fit (by rw [nOff]; decide)
  obtain ⟨theta,Hh,Hx⟩ := shared_clean_primitive ha ho hF cancel L hd fit term
  have XP := primitive_X_head_zero_of_clean_prefix_paid ha ho hF L.h_clean L.before_h hd fit
  have N (u : K) (r : lobattoNumer u=0) : u≠0 := by
    rintro rfl
    simpa [lobattoNumer] using r
  obtain ⟨κ,receipt⟩ := raw_shape_from_primitive ho P hd (N _ L.roots.root_h)
    (N _ L.roots.root_x) L.roots.h_ne_x.symm Hh Hx XP
  exact ⟨theta,κ,receipt⟩

/-- The local first-clean XP test is automatic, without a P(0)=0 premise. -/
theorem primitive_X_head_zero_of_clean_prefix [CharZero K] (ha : ∀ j l, j≤l → A j l=0)
    (hF : zeroSpace A 4=band A 2) {i : Fin 10} (hi : g A i=0)
    (pre : ∀ j, j < i → g A j=0 → nodes A j=0)
    {P : K[X]} (hd : P.natDegree≤2)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j) :
    (primitive (X*P)).eval (nodes A i)=0 := by
  have dX : (X*P).natDegree≤3 := natDegree_mul_le_of_le (show (X:K[X]).natDegree≤1 by simp) hd
  exact on_primitive_zero_of_prefix ha hF hi (X*P) dX
    (diag (nodes A) (g A)) (clean_mixed_defect hF hi) (fun j hj => by
      by_cases hj' : g A j=0
      · simp [hj',pre j hj hj']
      · simp [fit j hj'])


/-- Acyclic native consumer: from literal tagged placement and the terminal
profile, produce both branches' exact shared checked scalar shape inputs. -/
theorem clean_shape_from_actual_prefix [CharZero K] (ha : ∀ j l, j≤l → A j l=0) (ho : HasOrder 8 A b)
    (hF : zeroSpace A 4=band A 2) (nOff : (offKnots A).card=4)
    {iH iX : Fin 10} {z : K} (L : CleanPrimitivePlacement A b iH iX z)
    {P R : K[X]} (hd : P.natDegree≤2) (hnz : P≠0)
    (fit : ∀ j, g A j≠0 → P.eval (nodes A j)=g A j)
    (term : CleanTerminalProfile A (quartic (nodes A iH) (nodes A iX) z) R) :
    ∃ theta k, NormalizedShape P (nodes A iH) (nodes A iX) z theta k := by
  have cancel := offMass_zero_of_head ho fit (by rw [nOff]; decide)
  obtain ⟨theta,Hh,Hx⟩ := shared_clean_primitive ha ho hF cancel L hd fit term
  obtain ⟨k,co⟩ := coefficients_of_clean_tap P hd L.roots Hh Hx
  have XP := primitive_X_head_zero_of_clean_prefix ha hF L.h_clean L.before_h hd fit
  exact ⟨theta,k,normalize_head_of_primitive L.roots hd hnz co XP⟩

end RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
