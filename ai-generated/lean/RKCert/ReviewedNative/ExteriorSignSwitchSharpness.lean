module

public import RKCert.ReviewedNative.ExteriorSignSwitch
import RKCert.ReviewedNative.OrderedAlternationDegree
import Mathlib.Data.List.Chain
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

@[expose] public section

namespace RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch

open Polynomial
open RKCert.ReviewedNative.FiniteOrderedSigns
open scoped BigOperators Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem finite_positive_below (S : Finset K) (f : K → K) :
    (∀ x∈S, 0<f x) → ∃ e : K, 0<e ∧ ∀ x∈S, e<f x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨1, zero_lt_one, by simp⟩
  | @insert t S off ih =>
      intro positive
      have p : 0<f t := positive t (Finset.mem_insert_self _ _)
      obtain ⟨e, ep, paid⟩ := ih (fun x hx => positive x (Finset.mem_insert_of_mem hx))
      refine ⟨min e (f t/2), lt_min ep (div_pos p (by norm_num)), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with eq | hx
      · subst x
        exact (min_le_right _ _).trans_lt (half_lt_self p)
      · exact (min_le_left _ _).trans_lt (paid x hx)

/-- Pure finite perturbation. Only the one positive anchor is protected;
the perturbed polynomial need not remain interval-positive elsewhere. -/
private theorem strict_exterior_perturbation {S : Finset K} {mu : K → K}
    {A : K[X]} {a : K} (anchor : 0<A.eval a) (active : ∀ x∈S, mu x≠0)
    (weak : ∀ x∈S, mu x*A.eval x≤0) :
    ∃ Q : K[X], Q.natDegree≤A.natDegree ∧ 0<Q.eval a ∧
      ∀ x∈S, mu x*Q.eval x<0 := by
  classical
  let Z := S.filter fun x => A.eval x=0
  let W := (insert a S).filter fun x => A.eval x≠0
  let r : K → K := fun x => if 0<mu x then -1 else 1
  let R := Lagrange.interpolate Z id r
  have A0 : A≠0 := by
    intro z
    rw [z, eval_zero] at anchor
    exact (lt_irrefl (0:K)) anchor
  have zeros : Z⊆A.roots.toFinset := by
    intro x hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots A0).mpr (Finset.mem_filter.mp hx).2)
  have zcard : Z.card≤A.natDegree :=
    (Finset.card_le_card zeros).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  have inj : Set.InjOn (id : K → K) (↑Z : Set K) := by
    intro x _ y _ eq
    exact eq
  have rdeg : R.natDegree ≤ Z.card-1 :=
    Polynomial.natDegree_le_of_degree_le
      (Lagrange.degree_interpolate_le (s:=Z) (v:=id) r inj)
  have atZero (x : K) (hx : x∈Z) : R.eval x=r x := by
    simpa only [R,id_eq] using Lagrange.eval_interpolate_at_node (s:=Z) (v:=id) r inj hx
  have den (x : K) : 0 < |R.eval x| + 1 :=
    add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
  let ratio : K → K := fun x => |A.eval x|/(|R.eval x|+1)
  have rp (x : K) (hx : x∈W) : 0<ratio x :=
    div_pos (abs_pos.mpr (Finset.mem_filter.mp hx).2) (den x)
  obtain ⟨e, ep, small⟩ := finite_positive_below W ratio rp
  let Q := A+C e*R
  have qd : Q.natDegree≤A.natDegree :=
    natDegree_add_le_of_degree_le le_rfl
      ((natDegree_C_mul_le _ _).trans (rdeg.trans ((Nat.sub_le Z.card 1).trans zcard)))
  have tiny (x : K) (hx : x∈insert a S) (live : A.eval x≠0) :
      |e*R.eval x| < |A.eval x| := by
    have ss := (lt_div_iff₀ (den x)).mp (small x (Finset.mem_filter.mpr ⟨hx,live⟩))
    have le : |R.eval x| ≤ |R.eval x|+1 := by
      simpa only [add_zero] using add_le_add_right (zero_le_one : (0:K)≤1) (|R.eval x|)
    rw [abs_mul, abs_of_pos ep]
    exact (mul_le_mul_of_nonneg_left le ep.le).trans_lt ss
  have keeps_pos (x : K) (hx : x∈insert a S) (hp : 0<A.eval x) : 0<Q.eval x := by
    have s := tiny x hx (ne_of_gt hp)
    rw [abs_of_pos hp] at s
    have lb : -|e*R.eval x| ≤ e*R.eval x := neg_abs_le _
    change 0 < (A+C e*R).eval x
    simp only [eval_add,eval_mul,eval_C]
    have lo : -(A.eval x)<e*R.eval x := (neg_lt_neg s).trans_le lb
    simpa only [add_neg_cancel] using add_lt_add_right lo (A.eval x)
  have keeps_neg (x : K) (hx : x∈insert a S) (hn : A.eval x<0) : Q.eval x<0 := by
    have s := tiny x hx (ne_of_lt hn)
    rw [abs_of_neg hn] at s
    have ub : e*R.eval x ≤ |e*R.eval x| := le_abs_self _
    change (A+C e*R).eval x<0
    simp only [eval_add,eval_mul,eval_C]
    have hi : e*R.eval x < -(A.eval x) := ub.trans_lt s
    simpa only [add_neg_cancel] using add_lt_add_right hi (A.eval x)
  refine ⟨Q,qd,keeps_pos a (Finset.mem_insert_self _ _) anchor,?_⟩
  intro x hx
  by_cases z : A.eval x=0
  · have zi : x∈Z := Finset.mem_filter.mpr ⟨hx,z⟩
    have opp : mu x*r x<0 := by
      by_cases pos : 0<mu x
      · simpa only [r,if_pos pos,mul_neg,mul_one] using (neg_lt_zero.mpr pos)
      · have neg : mu x<0 := lt_of_le_of_ne (le_of_not_gt pos) (active x hx)
        simpa only [r,if_neg pos,mul_one] using neg
    change mu x*(A+C e*R).eval x<0
    rw [eval_add,eval_mul,eval_C,z,atZero x zi,zero_add,mul_left_comm]
    exact mul_neg_of_pos_of_neg ep opp
  · have old : mu x*A.eval x<0 :=
      lt_of_le_of_ne (weak x hx) (mul_ne_zero (active x hx) z)
    have mem : x∈insert a S := Finset.mem_insert_of_mem hx
    rcases mul_neg_iff.mp old with ⟨p,n⟩ | ⟨n,p⟩
    · exact mul_neg_of_pos_of_neg p (keeps_neg x mem n)
    · exact mul_neg_of_neg_of_pos n (keeps_pos x mem p)

private def evalFlag (Q : K[X]) (x : K) : Bool := decide (0<Q.eval x)

private theorem anti_flag {mu : K → K} {Q : K[X]} {x : K} (h : mu x*Q.eval x<0) :
    Q.eval x≠0 ∧ evalFlag Q x = !(massFlag mu x) := by
  constructor
  · intro z
    rw [z,mul_zero] at h
    exact (lt_irrefl (0:K)) h
  · rcases mul_neg_iff.mp h with ⟨p,n⟩ | ⟨n,p⟩ <;>
      simp [evalFlag,massFlag,p,not_lt_of_ge n.le]

private theorem sign_flip_neg {Q : K[X]} {a b : K}
    (ha : Q.eval a≠0) (hb : Q.eval b≠0) (flip : evalFlag Q a ≠ evalFlag Q b) :
    Q.eval a*Q.eval b<0 := by
  by_cases pa : 0<Q.eval a <;> by_cases pb : 0<Q.eval b
  · exact (flip (by simp [evalFlag,pa,pb])).elim
  · exact mul_neg_of_pos_of_neg pa (lt_of_le_of_ne (le_of_not_gt pb) hb)
  · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt pa) ha) pb
  · exact (flip (by simp [evalFlag,pa,pb])).elim

private theorem alternating_switch_samples (mu : K → K) (Q : K[X]) (xs : List K) :
    ∀ (a : K) (prev : Bool), Q.eval a≠0 → evalFlag Q a = !prev →
      (∀ x∈xs, mu x*Q.eval x<0) →
      ∃ ys : List K, ys.Sublist xs ∧ ys.length=switchCost mu prev xs ∧
        AlternatingSamples Q (a::ys) := by
  induction xs with
  | nil =>
      intro a prev a0 _ _
      refine ⟨[],List.Sublist.refl [],by simp [switchCost],⟨?_,List.IsChain.singleton _⟩⟩
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact a0
  | cons t ts ih =>
      intro a prev a0 af anti
      have tail : ∀ x∈ts, mu x*Q.eval x<0 :=
        fun x hx => anti x (List.mem_cons.mpr (Or.inr hx))
      by_cases same : massFlag mu t=prev
      · obtain ⟨ys,sub,n,alt⟩ := ih a prev a0 af tail
        refine ⟨ys,List.Sublist.cons t sub,?_,alt⟩
        rw [switchCost,if_pos same,add_zero]
        simpa only [same] using n
      · obtain ⟨t0,tf⟩ := anti_flag (anti t List.mem_cons_self)
        have diff : evalFlag Q a≠evalFlag Q t := by
          rw [af,tf]
          intro eq
          exact same (Bool.not_inj eq.symm)
        obtain ⟨ys,sub,n,alt⟩ := ih t (massFlag mu t) t0 tf tail
        refine ⟨t::ys,List.Sublist.cons_cons t sub,?_,⟨?_,alt.jumps.cons_cons (sign_flip_neg a0 t0 diff)⟩⟩
        · simp only [List.length_cons,switchCost,if_neg same,n]
        · intro x hx
          rcases List.mem_cons.mp hx with eq | hx
          · rwa [eq]
          · exact alt.nonzero x hx

private theorem switch_degree_of_strict_terms (T : Finset K) (mu : K → K) {Q : K[X]} {a : K}
    (ha : a∈Set.Ioo (0:K) 1) (ap : 0<Q.eval a)
    (strict : ∀ x∈exteriorSites T, mu x*Q.eval x<0) :
    exteriorSignSwitchCost T mu≤Q.natDegree := by
  have af : evalFlag Q a= !false := by simp [evalFlag,ap]
  have paidL (x : K) (hx : x∈leftOutward T) : mu x*Q.eval x<0 := by
    obtain ⟨t,le⟩ := mem_leftOutward.mp hx
    exact strict x (Finset.mem_filter.mpr ⟨t,Or.inl le⟩)
  have paidR (x : K) (hx : x∈rightOutward T) : mu x*Q.eval x<0 := by
    obtain ⟨t,le⟩ := mem_rightOutward.mp hx
    exact strict x (Finset.mem_filter.mpr ⟨t,Or.inr le⟩)
  obtain ⟨L,subL,nL,altL⟩ := alternating_switch_samples mu Q (leftOutward T)
    a false (ne_of_gt ap) af paidL
  obtain ⟨R,subR,nR,altR⟩ := alternating_switch_samples mu Q (rightOutward T)
    a false (ne_of_gt ap) af paidR
  let S := L.reverse ++ (a::R)
  have left_lt (x : K) (hx : x∈L.reverse) : x<a :=
    (mem_leftOutward.mp (subL.subset (List.mem_reverse.mp hx))).2.trans_lt ha.1
  have right_gt (x : K) (hx : x∈R) : a<x :=
    ha.2.trans_le (mem_rightOutward.mp (subR.subset hx)).2
  have ldec : L.Pairwise (· > ·) :=
    List.Pairwise.sublist subL ((leftSites T).sortedGT_sort).pairwise
  have rinc : (a::R).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨right_gt,
      List.Pairwise.sublist subR ((rightSites T).sortedLT_sort).pairwise⟩
  have inc : S.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨List.pairwise_reverse.mpr ldec,rinc,?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with eq | hy
    · rw [eq]; exact left_lt x hx
    · exact (left_lt x hx).trans (right_gt y hy)
  have leftChain : (L.reverse++[a]).IsChain (fun x y => Q.eval x*Q.eval y<0) := by
    have reverse : (a::L).reverse.IsChain (fun x y => Q.eval x*Q.eval y<0) :=
      List.isChain_reverse.mpr (altL.jumps.imp (fun x y h => by
        rw [mul_comm (Q.eval y) (Q.eval x)]
        exact h))
    simpa only [List.reverse_cons] using reverse
  have alt : AlternatingSamples Q S := by
    refine ⟨?_,List.isChain_split.mpr ⟨leftChain,altR.jumps⟩⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact altL.nonzero x (List.mem_cons.mpr (Or.inr (List.mem_reverse.mp hx)))
    · exact altR.nonzero x hx
  have count : S.length-1=exteriorSignSwitchCost T mu := by
    simp only [S,List.length_append,List.length_reverse,List.length_cons,nL,nR,
      exteriorSignSwitchCost]
    omega
  have bound := variation_le_natDegree Q S inc
  rw [alt.variation_eq_length,count] at bound
  exact bound

/-- Necessity only needs one interior positive anchor and the literal
weak inequalities at all nonzero exterior groups. -/
theorem exteriorSignSwitchCost_le_degree_at_anchor {T : Finset K} {mu : K → K}
    {A : K[X]} {a : K} (active : ∀ x∈exteriorSites T, mu x≠0)
    (ha : a∈Set.Ioo (0:K) 1) (ap : 0<A.eval a)
    (weak : ∀ x∈exteriorSites T, mu x*A.eval x≤0) :
    exteriorSignSwitchCost T mu≤A.natDegree := by
  obtain ⟨Q,d,pos,terms⟩ := strict_exterior_perturbation ap active weak
  exact (switch_degree_of_strict_terms T mu ha pos terms).trans d

/-- Sharpness among all interval-positive polynomials suppressing the
literal exterior group terms, not just the chosen affine products. -/
theorem exteriorSignSwitchCost_isLeast_degree (T : Finset K) (mu : K → K)
    (active : ∀ x∈exteriorSites T, mu x≠0) :
    IsLeast {d : ℕ | ∃ A : K[X], A.natDegree=d ∧
        (∀ x∈Set.Ioo (0:K) 1, 0<A.eval x) ∧
        (∀ x∈exteriorSites T, mu x*A.eval x≤0)}
      (exteriorSignSwitchCost T mu) := by
  constructor
  · refine ⟨switchMask T mu,switchMask_degree T mu,?_,?_⟩
    · intro x hx
      exact exteriorMask_pos (selected_outside T mu) hx
    · intro x hx
      exact switchMask_exterior_nonpos hx
  · intro d hd
    obtain ⟨A,deg,pos,weak⟩ := hd
    have half : (1/2:K)∈Set.Ioo (0:K) 1 := ⟨by norm_num,by norm_num⟩
    rw [← deg]
    exact exteriorSignSwitchCost_le_degree_at_anchor active half (pos _ half) weak

end
end RKCert.ReviewedNative.FormalSignedQuadrature.ExteriorSwitch
