module

public import RKCert.ReviewedNative.ERK8CharElevenTailSupport

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal reflected tail equation for a seven-off ERK8 tableau

The two reflected tests use the original matrix and output weights.
The cancellation of the two late A-images follows from the degree-seven
weighted defect condition; no complementary-space rank or pointwise
reflected profile is an input. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Polynomial OneOff ERKTaggedHorizon ERK8PaidField LobattoEight RKCert.Endpoint
open scoped Matrix Classical BigOperators

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

private theorem sum_pair_support {u v : Fin 10} (uv : u ≠ v) (F : Fin 10 → K)
    (zero : ∀ i, i ≠ u → i ≠ v → F i = 0) :
    (∑ i, F i) = F u+F v := by
  have e : (∑ i ∈ ({u,v} : Finset (Fin 10)), F i) = ∑ i, F i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ h
    exact zero i (fun e => h (by simp [e])) (fun e => h (by simp [e]))
  rw [←e,Finset.sum_pair uv]

private theorem sum_triple_support {f u v : Fin 10} (fu : f ≠ u) (fv : f ≠ v) (uv : u ≠ v)
    (F : Fin 10 → K) (zero : ∀ i, i ≠ f → i ≠ u → i ≠ v → F i = 0) :
    (∑ i, F i) = F f+F u+F v := by
  have e : (∑ i ∈ ({f,u,v} : Finset (Fin 10)), F i) = ∑ i, F i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ h
    exact zero i (fun e => h (by simp [e])) (fun e => h (by simp [e])) (fun e => h (by simp [e]))
  rw [←e,Finset.sum_insert (by simp [fu,fv]),Finset.sum_pair uv,add_assoc]

/-- Reflected clock powers divided by the exceptional quadratic. -/
noncomputable def highSenderMoment (A : Matrix (Fin 10) (Fin 10) K) (i : Fin 10) (k : ℕ) : K :=
  (1-nodes A i)^k/(exceptionalQuadratic : K[X]).eval (nodes A i)

/-- Last-three moment after cancellation of the early four-clock hull. -/
noncomputable def highTailMoment (A : Matrix (Fin 10) (Fin 10) K) (f u v : Fin 10) (k : ℕ) : K :=
  let term i := (1-nodes A i)^k/((exceptionalQuadratic : K[X]).eval (nodes A i)*
    highTailCofactor A f u v (nodes A i))
  term f+term u+term v

/-- The exact physical tail relation from the two paid reflected rows.
The only nonliteral input is the specified last-three chronology,
including which clean rows can be later than the first tail row. -/
theorem seven_off_paid_reflected_tail
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v) :
    3*(highSenderMoment A u 2-highSenderMoment A v 2)*highTailMoment A f u v 2
      -2*(highSenderMoment A u 1-highSenderMoment A v 1)*highTailMoment A f u v 3=0 := by
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  obtain ⟨lambda,ll,weight⟩ := seven_off_literal_barycentric_weights ha ho p seven three
  let U := highPrefixHull A f u v
  let w := offEval A U
  let Aw := mat A w
  let y (i : Fin 10) := 1-nodes A i
  let q (i : Fin 10) := (exceptionalQuadratic : K[X]).eval (nodes A i)
  let Tu := b u*q u*Aw u
  let Tv := b v*q v*Aw v
  have wf : w ∈ treeSpace A 4 :=
    high_offEval_mem_treeSpace4 ha ho p three H U (highPrefixHull_degree seven three T).le
  have awf : Aw ∈ treeSpace A 5 := mat_treeSpace A 4 wf
  have early (j : Fin 10) (hj : j ≤ f) : Aw j=0 :=
    causal_mat ha j w (fun i hi => high_test_zero_before seven three T (hi.trans_le hj))
  have weightTerm (i : Fin 10) (gi : g A i ≠ 0) (ti : nodes A i ∈ highTailClocks A f u v) :
      b i*U.eval (nodes A i) = lambda/(q i*highTailCofactor A f u v (nodes A i)) := by
    have qn := exceptional_quadratic_ne_off H gi
    have h := (eq_div_iff (mul_ne_zero qn (offCofactor_ne A _))).mp (weight i gi)
    rw [highCofactor_factor T ti] at h
    apply (eq_div_iff (mul_ne_zero qn (highTailCofactor_ne A f u v _))).mpr
    linear_combination h
  have rhs (k : ℕ) : (∑ j : Fin 10, b j*y j^k*w j)=lambda*highTailMoment A f u v k := by
    let F (j : Fin 10) := b j*y j^k*w j
    have eq := sum_triple_support (ne_of_lt T.fu) (ne_of_lt (T.fu.trans T.uv))
      (ne_of_lt T.uv) F (fun j jf ju jv => by
        by_cases gj : g A j=0
        · simp [F,w,offEval,gj]
        rcases T.earlier j gj with he|he|he|he
        · simp [F,show w j=0 from high_test_zero_before seven three T he]
        · exact (jf he).elim
        · exact (ju he).elim
        · exact (jv he).elim)
    have atTail (i : Fin 10) (gi : g A i≠0) (ti : nodes A i∈highTailClocks A f u v) :
        F i = lambda*(y i^k/(q i*highTailCofactor A f u v (nodes A i))) := by
      change b i*y i^k*w i=_
      have he : w i=U.eval (nodes A i) := by simp [w,offEval,gi]
      rw [he,show b i*y i^k*U.eval (nodes A i)=y i^k*(b i*U.eval (nodes A i)) by ring,
        weightTerm i gi ti]
      simp only [div_eq_mul_inv]
      ring
    change (∑ j, F j)=_
    rw [eq,atTail f T.f_off (by simp [highTailClocks]),atTail u T.u_off (by simp [highTailClocks]),
      atTail v T.v_off (by simp [highTailClocks])]
    unfold highTailMoment
    change _ = lambda*(y f^k/(q f*_) + y u^k/(q u*_) + y v^k/(q v*_))
    ring
  have zeroMem : g A * Aw ∈ zeroSpace A 7 :=
    zeroSpace_mul_treeSpace ho (m:=2) (n:=5) (by decide) (mDef_mem A 1) awf
  have zeroPay : probe A b 0 (g A*Aw)=0 := probe_zeroSpace ho (j:=7) (k:=0) (by decide) zeroMem
  have zeroSum : (∑ j : Fin 10, b j*(g A j*Aw j))=0 := by
    simpa only [probe,row_apply,dotProduct,pow_zero,mul_one,Pi.mul_apply] using zeroPay
  have balance : Tu+Tv=0 := by
    have e := sum_pair_support (ne_of_lt T.uv) (fun j => b j*(g A j*Aw j)) (fun j ju jv => by
      by_cases gj : g A j=0
      · simp [gj]
      rcases T.earlier j gj with h|h|h|h
      · simp [early j h.le]
      · simp [early j h.le]
      · exact (ju h).elim
      · exact (jv h).elim)
    have ee := e.symm.trans zeroSum
    rw [←H.fit u T.u_off,←H.fit v T.v_off] at ee
    have h : theta*(Tu+Tv)=0 := by
      dsimp only [Tu,Tv,q]
      linear_combination ee
    exact (mul_eq_zero.mp h).resolve_left H.scale_ne
  have TvEq : Tv = -Tu := by linear_combination balance
  have lhs (k : ℕ) (kp : 0 < k) : (∑ j : Fin 10, b j*y j^k*Aw j)=
      Tu*(highSenderMoment A u k-highSenderMoment A v k) := by
    let F (j : Fin 10) := b j*y j^k*Aw j
    have e := sum_pair_support (ne_of_lt T.uv) F (fun j ju jv => by
      by_cases jle : j ≤ f
      · simp [F,early j jle]
      have hj : f < j := lt_of_not_ge jle
      by_cases gj : g A j=0
      · have j1 := T.early_clean j gj hj
        simp [F,y,j1,zero_pow (Nat.ne_of_gt kp)]
      rcases T.earlier j gj with h|h|h|h
      · exact (not_lt_of_ge hj.le h).elim
      · exact (ne_of_gt hj h).elim
      · exact (ju h).elim
      · exact (jv h).elim)
    have atU : F u=Tu*highSenderMoment A u k := by
      have qn : q u≠0 := exceptional_quadratic_ne_off H T.u_off
      change b u*y u^k*Aw u=(b u*q u*Aw u)*(y u^k/q u)
      rw [←mul_div_assoc]
      exact (eq_div_iff qn).mpr (by ring)
    have atV : F v=Tv*highSenderMoment A v k := by
      have qn : q v≠0 := exceptional_quadratic_ne_off H T.v_off
      change b v*y v^k*Aw v=(b v*q v*Aw v)*(y v^k/q v)
      rw [←mul_div_assoc]
      exact (eq_div_iff qn).mpr (by ring)
    change (∑ j,F j)=_
    rw [e,atU,atV,TvEq]
    ring
  have paid (k : ℕ) (kp : 0 < k) (pay : 4+k+2≤8) :
      ((k+1:ℕ):K)*(Tu*(highSenderMoment A u k-highSenderMoment A v k)) =
      lambda*highTailMoment A f u v (k+1) := by
    have z : row (reflectedStageRow A b k) w=0 := reflectedStageRow_treeSpace ho 4 k pay wf
    rw [reflectedStageRow_pair,sub_eq_zero] at z
    simp only [reflectedProbe,row_apply,dotProduct,pow_zero,mul_one,reflectedClock,
      Pi.sub_apply,Pi.one_apply] at z
    change ((k+1:ℕ):K)*(∑ j : Fin 10,b j*y j^k*Aw j)=
      ∑ j : Fin 10,b j*y j^(k+1)*w j at z
    rw [lhs k kp,rhs (k+1)] at z
    exact z
  have p2 := paid 1 (by decide) (by decide)
  have p3 := paid 2 (by decide) (by decide)
  have z : lambda*(3*(highSenderMoment A u 2-highSenderMoment A v 2)*highTailMoment A f u v 2
      -2*(highSenderMoment A u 1-highSenderMoment A v 1)*highTailMoment A f u v 3)=0 := by
    norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at p2 p3
    linear_combination -3*(highSenderMoment A u 2-highSenderMoment A v 2)*p2
      +2*(highSenderMoment A u 1-highSenderMoment A v 1)*p3
  exact (mul_eq_zero.mp z).resolve_left ll

/-- The final scalar product follows once the actual tail moments have
the specified nonzero ratio; it is not an extra reflected-row input. -/
theorem seven_off_paid_tail_product_of_ratio
    (ha : ∀ i j, i ≤ j → A i j=0) (ho : HasOrder 8 A b) (p : (11:K)=0)
    (seven : (offKnots A).card=7) (three : (cleanKnots A).card=3)
    {f u v : Fin 10} (T : HighPhysicalTail A f u v)
    (nonzero : highTailMoment A f u v 2 ≠ 0)
    (ratio : 2*highTailMoment A f u v 3=highTailMoment A f u v 2) :
    nodes A u*nodes A v=8 := by
  have pay := seven_off_paid_reflected_tail ha ho p seven three T
  have z : highTailMoment A f u v 2*
    (3*(highSenderMoment A u 2-highSenderMoment A v 2)-
       (highSenderMoment A u 1-highSenderMoment A v 1))=0 := by
    linear_combination pay+(highSenderMoment A u 1-highSenderMoment A v 1)*ratio
  have e := (mul_eq_zero.mp z).resolve_left nonzero
  obtain ⟨theta,H⟩ := order8_paid_five_or_seven_exceptional_head ha ho p (Or.inr ⟨seven,three⟩)
  obtain ⟨_,_,uv⟩ := highTailClocks_distinct seven three T
  have qu := exceptional_quadratic_ne_off H T.u_off
  have qv := exceptional_quadratic_ne_off H T.v_off
  rw [exceptionalQuadratic_eval] at qu qv
  apply high_tail_product p uv qu qv
  unfold highSenderMoment at e
  simp only [exceptionalQuadratic_eval,pow_one,div_eq_mul_inv] at e ⊢
  linear_combination e

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_paid_reflected_tail
#print axioms RKResearch.Certified.Graded.ERK8CharEleven.seven_off_paid_tail_product_of_ratio
