module

public import RKCert.ReviewedNative.HankelQuarticLegendreObstructions
public import RKCert.ReviewedNative.HankelQuarticFullProfile
public import RKCert.ReviewedNative.HankelNormalGapWitness

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid Legendre join for all seven literal quartic profile exceptions

Unlike a height-only argument, this keeps the same fixed mask `P` and
extracts the polynomial divisibility at the actually observed restart.
The last two all-rise cases use the two-mode band, not invented live
residuals. The pending field receipt and per-width cap are explicit. -/
namespace RKResearch.Certified.Graded.HankelQuarticLegendre

open Polynomial Matrix HankelPaidMonicBasis HankelPaidRestart
open HankelNormalGapWitness HankelQuarticFullProfile
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

def maskedMoment (I : K[X] →ₗ[K] K) (P : K[X]) : K[X] →ₗ[K] K :=
  I.comp (LinearMap.mulLeft K P)

private theorem residual_mask (I : K[X] →ₗ[K] K) (P B : K[X]) (j : ℕ) :
    residual (maskedMoment I P) B j = I (X^j*(P*B)) := by
  change I (P*(X^j*B))=I (X^j*(P*B))
  congr 1
  ring

private theorem sub_mem_degreeLT_of_monic_same {F G : K[X]} {n : ℕ}
    (fm : F.Monic) (gm : G.Monic) (fd : F.natDegree=n) (gd : G.natDegree=n) :
    F-G ∈ degreeLT K n := by
  apply mem_degreeLT.mpr
  rw [degree_lt_iff_coeff_zero]
  intro j nj
  rw [coeff_sub]
  rcases eq_or_lt_of_le nj with e | lt
  · subst j
    have f : F.coeff n=1 := fd ▸ fm.coeff_natDegree
    have g : G.coeff n=1 := gd ▸ gm.coeff_natDegree
    rw [f,g,sub_self]
  · have lf : F.natDegree<j := by rwa [fd]
    have lg : G.natDegree<j := by rwa [gd]
    rw [coeff_eq_zero_of_natDegree_lt lf,coeff_eq_zero_of_natDegree_lt lg,sub_self]

variable {I : K[X] →ₗ[K] K}

private theorem band_multiplies_silent {Q S : K[X]} {n : ℕ}
    (qd : Q ∈ degreeLT K n) (sil : ∀ j<n, I ((X:K[X])^j*S)=0) : I (Q*S)=0 := by
  by_cases q0 : Q=0
  · simp [q0]
  have deg := mem_degreeLT.mp qd
  rw [degree_eq_natDegree q0] at deg
  have nd : Q.natDegree<n := WithBot.coe_lt_coe.mp deg
  have expand : Q*S=∑ j ∈ Finset.range n, (C (Q.coeff j)*X^j)*S := by
    conv_lhs => rw [Q.as_sum_range_C_mul_X_pow' nd,Finset.sum_mul]
  rw [expand,map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [mul_assoc, ←Polynomial.smul_eq_C_mul, map_smul, sil j (Finset.mem_range.mp hj),smul_zero]

/-- Finite pure detector proved from the paid monic modes and their
nonzero norms; it is not an additional receipt field. -/
theorem low_mode_detect (R : PaidLegendre28 I) (n : ℕ) (pay : n≤10) (F : K[X])
    (fd : F ∈ degreeLT K n) (sil : ∀ j<n, I ((X:K[X])^j*F)=0) : F=0 := by
  by_contra f0
  let k := F.natDegree
  let a := F.coeff k
  let Q := F-C a*X^k
  have fdg := mem_degreeLT.mp fd
  rw [degree_eq_natDegree f0] at fdg
  have kn : k<n := WithBot.coe_lt_coe.mp fdg
  have k9 : k≤9 := by omega
  have k10 : k≤10 := by omega
  have a0 : a≠0 := leadingCoeff_ne_zero.mpr f0
  have qd : Q ∈ degreeLT K k := by
    apply mem_degreeLT.mpr
    rw [degree_lt_iff_coeff_zero]
    intro j hj
    change (F-C a*X^k).coeff j=0
    rw [coeff_sub,coeff_C_mul_X_pow]
    by_cases e : j=k
    · subst j; simp [a]
    · have gt : F.natDegree<j := by change k<j; omega
      rw [if_neg e, coeff_eq_zero_of_natDegree_lt gt,sub_self]
  have lk : L K k ∈ degreeLT K n := by
    apply mem_degreeLT.mpr
    rw [degree_eq_natDegree (R.modeMonic k k10).ne_zero,R.modeDegree k k10]
    exact WithBot.coe_lt_coe.mpr kn
  have h0 := band_multiplies_silent lk sil
  have q0 := band_multiplies_silent qd (R.modeSilent k k10)
  have fEq : F=Q+C a*X^k := by dsimp only [Q]; ring
  have aEq : I ((C a*X^k)*L K k)=a*I (X^k*L K k) := by
    rw [mul_assoc,←Polynomial.smul_eq_C_mul,map_smul,smul_eq_mul]
  rw [mul_comm,fEq,add_mul,map_add,q0,aEq,zero_add] at h0
  exact (mul_ne_zero a0 (R.modeNorm k k9)) h0

private theorem pure_mode_of_silent (R : PaidLegendre28 I) (F : K[X])
    {n : ℕ} (pay : n≤10) (fm : F.Monic) (fd : F.natDegree=n)
    (silent : ∀ j<n, I (X^j*F)=0) : F=L K n := by
  apply sub_eq_zero.mp
  apply low_mode_detect R n pay (F-L K n)
    (sub_mem_degreeLT_of_monic_same fm (R.modeMonic n pay) fd (R.modeDegree n pay))
  intro j hj
  rw [mul_sub,map_sub,silent j hj,R.modeSilent n pay j hj,sub_self]

private theorem two_modes_of_silent (R : PaidLegendre28 I) (F : K[X])
    {n : ℕ} (pos : 0<n) (pay : n≤10) (fm : F.Monic) (fd : F.natDegree=n)
    (silent : ∀ j<n-1, I (X^j*F)=0) :
    ∃ a : K, F=L K n+C a*L K (n-1) := by
  let D := F-L K n
  let a := D.coeff (n-1)
  let E := D-C a*L K (n-1)
  have pay' : n-1≤10 := by omega
  have dn : D ∈ degreeLT K n :=
    sub_mem_degreeLT_of_monic_same fm (R.modeMonic n pay) fd (R.modeDegree n pay)
  have ed : E ∈ degreeLT K (n-1) := by
    apply mem_degreeLT.mpr
    rw [degree_lt_iff_coeff_zero]
    intro j hn
    rcases eq_or_lt_of_le hn with e | lt
    · subst j
      have lead : (L K (n-1)).coeff (n-1)=1 := by
        simpa only [R.modeDegree (n-1) pay'] using (R.modeMonic (n-1) pay').coeff_natDegree
      simp only [E,coeff_sub,coeff_C_mul,lead,mul_one,a,sub_self]
    · have dz := (degree_lt_iff_coeff_zero D n).mp (mem_degreeLT.mp dn) j (by omega)
      have lz : (L K (n-1)).coeff j=0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [R.modeDegree (n-1) pay']; exact lt
      simp only [E,coeff_sub,coeff_C_mul,dz,lz,mul_zero,sub_self]
  have es (j : ℕ) (hj : j<n-1) : I (X^j*E)=0 := by
    dsimp only [E,D]
    rw [mul_sub,map_sub,mul_sub,map_sub,silent j hj,R.modeSilent n pay j (by omega),sub_self]
    have h : (X:K[X])^j*(C a*L K (n-1))=a • (X^j*L K (n-1)) := by
      rw [Polynomial.smul_eq_C_mul]; ac_rfl
    rw [h,map_smul,R.modeSilent (n-1) pay' j hj,smul_zero,sub_self]
  have e := low_mode_detect R (n-1) pay' E ed es
  refine ⟨a,?_⟩
  change F-L K n-C a*L K (n-1)=0 at e
  linear_combination e

variable {P : K[X]}
local notation "Jmask" => maskedMoment I P
local notation "νmask" => nullity (maskedMoment I P)

private theorem gap_shape_complete {r t : ℕ} (front : r<8) (start : νmask r=0)
    (tp : 0<t) (pay : r+t≤8) (no : ∀ j, 0<j → j<t → 0<νmask (r+j))
    (next : νmask (r+t)=0) : ∃ B, GapWitness Jmask B r 8 t := by
  obtain ⟨B,g,h⟩ := exists_gap_witness Jmask front start
  have eq := gap_eq_of_next_normal h tp pay no next
  exact ⟨B,eq ▸ h⟩

private theorem gap_shape_drop {r t g : ℕ} (front : r<8) (start : νmask r=0)
    (pay : r+t≤8) (no : ∀ j, 0<j → j≤t → 0<νmask (r+j))
    (drop : νmask (r+t)<t) (digits : t+νmask (r+t)=g) :
    ∃ B, GapWitness Jmask B r 8 g := by
  obtain ⟨B,a,h⟩ := exists_gap_witness Jmask front start
  exact ⟨B,((gap_eq_of_terminal_drop h pay no drop).trans digits) ▸ h⟩

private theorem max_gap_divisor (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    {r B} (pay : r≤5) (h : GapWitness Jmask B r 8 5) : P∣L K (r+4) := by
  have d : (P*B).natDegree=r+4 := by rw [pm.natDegree_mul h.monic,pd,h.degree,Nat.add_comm]
  have f := pure_mode_of_silent R (P*B) (by omega) (pm.mul h.monic) d (fun j hj => by
    rw [←residual_mask]
    exact h.vanishes j (by omega) (by omega))
  exact ⟨B,f.symm⟩

private theorem near_gap_divisor (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    {r B} (pay : r≤5) (h : GapWitness Jmask B r 8 4) :
    ∃ a : K, a≠0 ∧ P∣L K (r+4)+C a*L K (r+3) := by
  have d : (P*B).natDegree=r+4 := by rw [pm.natDegree_mul h.monic,pd,h.degree,Nat.add_comm]
  obtain ⟨a,eq⟩ := two_modes_of_silent R (P*B) (by omega) (by omega) (pm.mul h.monic) d
    (fun j hj => by rw [←residual_mask]; exact h.vanishes j (by omega) (by omega))
  have id : r+4-1=r+3 := by omega
  rw [id] at eq
  have a0 : a≠0 := by
    intro za
    have pure : P*B=L K (r+4) := by simpa only [za,map_zero,zero_mul,add_zero] using eq
    have test := h.first (by omega)
    apply test
    rw [residual_mask,pure]
    exact R.modeSilent (r+4) (by omega) (r+(4-1)) (by omega)
  exact ⟨a,a0,⟨B,eq.symm⟩⟩

private theorem at_six_rise_divisor (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    (n6 : νmask 6=0) (p7 : νmask 7=1) (p8 : νmask 8=2) :
    ∃ a : K, P∣L K 10+C a*L K 9 := by
  obtain ⟨B,g,h⟩ := exists_gap_witness Jmask (r := 6) (W := 8) (by decide) n6
  have d : (P*B).natDegree=10 := by rw [pm.natDegree_mul h.monic,pd,h.degree]
  have sil (j : ℕ) (hj : j<9) : I (X^j*(P*B))=0 := by
    rw [←residual_mask]
    apply vanishes_of_terminal_rise (t := 2) h (by decide) _ (by exact p8) j (by omega) (by omega)
    intro q qp qt
    interval_cases q <;> simp only [Nat.reduceAdd, p7, p8] <;> decide
  obtain ⟨a,eq⟩ := two_modes_of_silent R (P*B) (n := 10) (by decide) (by decide) (pm.mul h.monic) d sil
  exact ⟨a,⟨B,eq.symm⟩⟩

private theorem initial_five_eq (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    (no : ∀ j, 0<j → j<5 → 0<νmask j) (z5 : νmask 5=0) : P=L K 4 := by
  have z0 : νmask 0=0 := by simp only [nullity,Nat.zero_sub]
  obtain ⟨B,h⟩ := gap_shape_complete (r := 0) (t := 5) (by decide) z0 (by decide) (by decide)
    (by simpa only [zero_add] using no) z5
  have d := max_gap_divisor R pm pd (by decide) h
  have e : L K 4=P := eq_of_monic_of_dvd_of_natDegree_le pm (R.modeMonic 4 (by decide)) d
    (by rw [pd,R.modeDegree 4 (by decide)] <;> decide)
  exact e.symm

private theorem initial_four_eq (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    (no : ∀ j, 0<j → j<4 → 0<νmask j) (z4 : νmask 4=0) :
    ∃ a : K, a≠0 ∧ P=L K 4+C a*L K 3 := by
  have z0 : νmask 0=0 := by simp only [nullity,Nat.zero_sub]
  obtain ⟨B,h⟩ := gap_shape_complete (r := 0) (t := 4) (by decide) z0 (by decide) (by decide)
    (by simpa only [zero_add] using no) z4
  obtain ⟨a,ha,⟨b,e⟩⟩ := near_gap_divisor R pm pd (by decide) h
  have lt : (C a*L K 3).natDegree<(L K 4).natDegree := by
    have q := natDegree_C_mul_le a (L K 3)
    rw [R.modeDegree 3 (by decide)] at q
    rw [R.modeDegree 4 (by decide)]
    omega
  have dm : (L K 4+C a*L K 3).Monic := by
    apply (R.modeMonic 4 (by decide)).add_of_left
    rw [degree_eq_natDegree (R.modeMonic 4 (by decide)).ne_zero]
    exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr lt)
  have bd : (L K 4+C a*L K 3).natDegree=4 := by
    rw [natDegree_add_eq_left_of_natDegree_lt lt,R.modeDegree 4 (by decide)]
  exact ⟨a,ha,(eq_of_monic_of_dvd_of_natDegree_le pm dm ⟨b,e⟩ (by rw [pd,bd] <;> decide)).symm⟩

private theorem decoded {ν : ℕ → ℕ} {a b c d e f g h : ℕ}
    (eq : heights ν 0 8=[a,b,c,d,e,f,g,h]) :
    ν 1=a ∧ ν 2=b ∧ ν 3=c ∧ ν 4=d ∧ ν 5=e ∧ ν 6=f ∧ ν 7=g ∧ ν 8=h := by
  simpa only [heights,List.cons.injEq,and_true] using eq

/-- Every literal bad tape is impossible for this one fixed quartic.
This theorem contains all seven branches of the accepted classifier;
it is not an extra case-exclusion argument passed by a caller. -/
theorem no_bad_paid_profile (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4) :
    heights νmask 0 8 ∉ badProfiles := by
  intro tape
  simp only [badProfiles,List.mem_cons,List.not_mem_nil,or_false] at tape
  rcases tape with row | row | row | row | row | row | row
  · -- 5,5*: a completed initial gap and a genuine dropped terminal height
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    have p := initial_five_eq R pm pd (by intro j jp jq; interval_cases j <;> omega) d5
    obtain ⟨B,h⟩ := gap_shape_drop (r := 5) (t := 3) (g := 5) (by decide) d5 (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d6, d7, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
    have tail := max_gap_divisor R pm pd (by decide) h
    rw [p] at tail
    exact no_five_five R tail
  · -- 4,5*: a mixed initial quartic
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    obtain ⟨a,ha,p⟩ := initial_four_eq R pm pd (by intro j jp jq; interval_cases j <;> omega) d4
    obtain ⟨B,h⟩ := gap_shape_drop (r := 4) (t := 4) (g := 5) (by decide) d4 (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d5, d6, d7, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
    have tail := max_gap_divisor R pm pd (by decide) h
    rw [p] at tail
    exact no_four_five R ha tail
  · -- 5,4*: compare the near-max band under the even pure divisor
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    have p := initial_five_eq R pm pd (by intro j jp jq; interval_cases j <;> omega) d5
    obtain ⟨B,h⟩ := gap_shape_drop (r := 5) (t := 3) (g := 4) (by decide) d5 (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d6, d7, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
    obtain ⟨a,_,tail⟩ := near_gap_divisor R pm pd (by decide) h
    rw [p] at tail
    exact no_five_four R a tail
  · -- 1,4,5*: two genuinely forced placements of the same fixed mask
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    obtain ⟨B1,h1⟩ := gap_shape_complete (r := 1) (t := 4) (by decide) d1 (by decide) (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d2, d3, d4] <;> decide) d5
    obtain ⟨a,ha,p1⟩ := near_gap_divisor R pm pd (by decide) h1
    obtain ⟨B2,h2⟩ := gap_shape_drop (r := 5) (t := 3) (g := 5) (by decide) d5 (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d6, d7, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
    have p2 := max_gap_divisor R pm pd (by decide) h2
    exact no_one_four_five R pm pd ha p1 p2
  · -- 1,5,≥4*: only the terminal silent two-mode band is required
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    obtain ⟨B1,h1⟩ := gap_shape_complete (r := 1) (t := 5) (by decide) d1 (by decide) (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d2, d3, d4, d5] <;> decide) d6
    have p1 := max_gap_divisor R pm pd (by decide) h1
    obtain ⟨a,p2⟩ := at_six_rise_divisor R pm pd d6 d7 d8
    exact no_one_five_rise R pm pd a p1 p2
  · -- 4,1,5*: completion at width four and positive terminal drop after five
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    obtain ⟨a,ha,p⟩ := initial_four_eq R pm pd (by intro j jp jq; interval_cases j <;> omega) d4
    obtain ⟨B,h⟩ := gap_shape_drop (r := 5) (t := 3) (g := 5) (by decide) d5 (by decide)
      (by
        intro j jp jq
        interval_cases j <;> simp only [Nat.reduceAdd, d6, d7, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
      (by simp only [Nat.reduceAdd, d8] <;> decide)
    have tail := max_gap_divisor R pm pd (by decide) h
    rw [p] at tail
    exact no_four_one_five R ha tail
  · -- 5,1,≥4*: reflection of literal divisibility, not of an unobserved residual
    obtain ⟨d1,d2,d3,d4,d5,d6,d7,d8⟩ := decoded row
    have p := initial_five_eq R pm pd (by intro j jp jq; interval_cases j <;> omega) d5
    obtain ⟨a,tail⟩ := at_six_rise_divisor R pm pd d6 d7 d8
    rw [p] at tail
    exact no_five_one_rise R a tail

/-- Exact paid scalar endpoint: after the genuine corank cap and the
explicit field modal receipt, the sum of eight actual ranks is ≥28.
No assumption of rank, split roots or profile exclusion is hidden. -/
theorem full_paid_rank_ge_28 (R : PaidLegendre28 I) (pm : P.Monic) (pd : P.natDegree=4)
    (cap : ∀ w≤8, νmask w≤2) :
    28 ≤ (hankel Jmask 1).rank+(hankel Jmask 2).rank+(hankel Jmask 3).rank+
      (hankel Jmask 4).rank+(hankel Jmask 5).rank+(hankel Jmask 6).rank+
      (hankel Jmask 7).rank+(hankel Jmask 8).rank := by
  have start : νmask 0=0 := by simp only [nullity,Nat.zero_sub]
  have steps : RestartsThrough νmask 8 := by
    intro r hr z
    obtain ⟨B,g,h⟩ := exists_gap_witness Jmask hr z
    exact ⟨g,h.positive,h.shape⟩
  have nz := full_nullity_le_eight_of_no_exception νmask start cap steps (no_bad_paid_profile R pm pd)
  unfold nullity at nz
  have r1 := (hankel Jmask 1).rank_le_height
  have r2 := (hankel Jmask 2).rank_le_height
  have r3 := (hankel Jmask 3).rank_le_height
  have r4 := (hankel Jmask 4).rank_le_height
  have r5 := (hankel Jmask 5).rank_le_height
  have r6 := (hankel Jmask 6).rank_le_height
  have r7 := (hankel Jmask 7).rank_le_height
  have r8 := (hankel Jmask 8).rank_le_height
  omega

end
end RKResearch.Certified.Graded.HankelQuarticLegendre
