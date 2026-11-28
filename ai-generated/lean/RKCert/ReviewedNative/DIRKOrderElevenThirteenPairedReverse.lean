module

public import RKCert.ReviewedNative.DIRKOrderElevenThirteenCubicRank
public import RKCert.ReviewedNative.ReverseClockGain
import Mathlib.Tactic.Ring

@[expose] public section

/-! Inclusive weighted reverse rank gain for two clean sampled rows.
This uses the real physical transpose, not a transposed RK order. -/
namespace RKResearch.Certified.Graded.OrderElevenThirteen

open RKResearch Module Polynomial RKCert.Endpoint Reverse
open scoped Matrix Classical

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 13) (Fin 13) K} {b : Fin 13 → K}

/-- Determinant of the two primitive reads of `X(X-a)(X-b)` and its
clock multiple at the two inclusive active nonorigin samples. -/
theorem two_primitive_determinant (a b : K) :
    (a^3*(2*b-a)/12)*(b^4*(5*a-3*b)/60) -
      (a^4*(5*b-3*a)/60)*(b^3*(2*a-b)/12) = a^3*b^3*(a-b)^3/120 := by ring

private theorem two_inclusive_primitive_detect (S : Finset K) (s3 : S.card=3)
    (Q : K[X]) (d : Q.natDegree≤1)
    (zero : ∀ z∈S, (primitive (nodalHull S * Q)).IsRoot z) : Q=0 := by
  let F := primitive (nodalHull S * Q)
  have deriv : F.derivative = nodalHull S * Q := by
    ext k
    rw [coeff_derivative,primitive_coeff_succ]
    simpa only [Nat.cast_add,Nat.cast_one] using
      div_mul_cancel₀ ((nodalHull S * Q).coeff k) (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k) :
        ((k+1:ℕ):K)≠0)
  by_contra nz
  have fnz : F≠0 := by
    intro fz
    rw [fz,map_zero] at deriv
    exact (mul_ne_zero (monic_nodalHull S).ne_zero nz) deriv.symm
  have sq (z : K) (hz : z∈S) : (X-C z)^2 ∣ F := by
    apply (le_rootMultiplicity_iff fnz).mp
    apply (one_lt_rootMultiplicity_iff_isRoot fnz).mpr
    exact ⟨zero z hz,by rw [deriv]; simp [IsRoot,nodalHull_eval_of_mem hz]⟩
  have div : nodalHull S ^ 2 ∣ F := by
    rw [nodalHull,←Finset.prod_pow]
    exact Finset.prod_dvd_of_coprime (fun a _ b _ hn =>
      (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hn).isUnit).pow) sq
  apply fnz (eq_zero_of_dvd_of_natDegree_lt div ?_)
  have deg := primitive_natDegree_le (natDegree_mul_le (p:=nodalHull S) (q:=Q))
  change F.natDegree≤_ at deg
  rw [natDegree_pow,natDegree_nodalHull,s3]
  rw [natDegree_nodalHull,s3] at deg
  omega

/-- The two nonorigin clean reverse samples and the actual removable
weighted part. In the two-pair chart `d` is `b` on the four pair
rows and zero off them. The cutoff retains the diagonal. -/
structure PairedReverseCut (A : Matrix (Fin 13) (Fin 13) K) (b : Fin 13 → K) where
  earlier : Fin 13
  later : Fin 13
  chronological : earlier < later
  dirtyWeight : Fin 13 → K
  earlierLive : b earlier≠0
  laterLive : b later≠0
  earlierNonorigin : reflectedClock A earlier≠0
  laterNonorigin : reflectedClock A later≠0
  distinct : reflectedClock A earlier≠reflectedClock A later
  earlierClean : ∀ v∈annih (treeSpace A 6), v earlier=0
  laterClean : ∀ v∈annih (treeSpace A 6), v later=0
  mask : ∀ P : K[X],
    weightedEval (reflectedClock A) dirtyWeight P∈annih (treeSpace A 6)
  cutoff : ∀ k≥earlier, b k=dirtyWeight k ∨ reflectedClock A k=0 ∨
    reflectedClock A k=reflectedClock A earlier ∨ reflectedClock A k=reflectedClock A later

/-- The invariant two-pair mask's genuine reverse degree-five gains
do not fit after debiting the live endpoint. The full rank-census
hypotheses remain explicit. -/
theorem no_paired_reverse_cut (ha : A.IsLowerTriangular) (ho : HasOrder 11 A b)
    (N : Normalized A b) (Cut : PairedReverseCut A b) : False := by
  classical
  let t : Fin 13 := Fin.last 12
  let U := annih (treeSpace A 6)
  let Z := zeroAt (annih (treeSpace A 5)) t
  let y := reflectedClock A
  let i := Cut.earlier
  let j := Cut.later
  let S : Finset K := {0,y i,y j}
  let H := nodalHull S
  let W := weightedEval y b
  let M := weightedEval y Cut.dirtyWeight
  let T := mat A.transpose
  have i0 : y i≠0 := Cut.earlierNonorigin
  have j0 : y j≠0 := Cut.laterNonorigin
  have ij : y i≠y j := Cut.distinct
  have s3 : S.card=3 := by simp [S,ij,Ne.symm i0,Ne.symm j0]
  have hH : H.natDegree=3 := (natDegree_nodalHull S).trans s3
  have h0 : H.eval 0=0 := nodalHull_eval_of_mem (by simp [S])
  have hi : H.eval (y i)=0 := nodalHull_eval_of_mem (by simp [S])
  have hj : H.eval (y j)=0 := nodalHull_eval_of_mem (by simp [S])
  let D : (Fin 2 → K) →ₗ[K] (Fin 13 → K) :=
    ((T.comp (W-M)) - (W.comp primitive)).comp ((LinearMap.mulLeft K H).comp (ofFn 2))
  have eqD (q : Fin 2 → K) :
      D q=T (W (H*ofFn 2 q)-M (H*ofFn 2 q))-W (primitive (H*ofFn 2 q)) := rfl
  have R := rank_census ha ho N
  have hU : U≤Z := by
    intro v hv
    apply mem_zeroAt.mpr
    refine ⟨annih_antitone (treeSpace_mono A (by decide : 5≤6)) hv,?_⟩
    have e := mem_annih.mp hv _ R.terminalInSix
    rwa [row_coordinate] at e
  have uT (v : Fin 13 → K) (hv : v∈U) : T v∈Z := by
    apply mem_zeroAt.mpr
    refine ⟨annih_map_transpose (mat_treeSpace A 5) (Submodule.mem_map_of_mem hv),?_⟩
    rw [show T=mat A.transpose from rfl,mat_apply,Matrix.mulVec_apply_eq_sum]
    exact Finset.sum_eq_zero fun k _ => by rw [Matrix.transpose_apply,R.terminalColumn,zero_mul]
  have ht : LastActive b t := ⟨R.terminalWeight,fun k h => False.elim
    ((not_lt_of_ge (Fin.le_last k)) h)⟩
  have hZ (q : Fin 2 → K) : D q∈Z := by
    let P := H*ofFn 2 q
    have deg : P.natDegree≤4 := by
      have dQ := ofFn_natDegree_lt (by decide : 0<2) q
      exact natDegree_mul_le.trans (by rw [hH]; omega)
    have prim : T (W P)-W (primitive P) ∈ primitiveBack A b 4 :=
      reverse_primitive_next 3 P deg
    have wZ : T (W P)-W (primitive P) ∈ Z := by
      apply mem_zeroAt.mpr
      exact ⟨primitiveBack_annih ho 5 4 (by decide) prim,
        mem_tailZero.mp (ht.dirk_primitiveBack_tail ha N.d1 N.d2 4 prim) t le_rfl⟩
    have cZ : T (M P)∈Z := uT _ (Cut.mask P)
    rw [eqD,show H*ofFn 2 q=P from rfl,map_sub,sub_right_comm]
    exact Z.sub_mem wZ cZ
  have rcoef (q : Fin 2 → K) (k : Fin 13) (hk : i≤k) :
      (W (H*ofFn 2 q)-M (H*ofFn 2 q)) k=0 := by
    rcases Cut.cutoff k hk with w|w|w|w
    · simp [W,M,w]
    · change y k=0 at w
      simp [W,M,w,h0]
    · change y k=y i at w
      simp [W,M,w,hi]
    · change y k=y j at w
      simp [W,M,w,hj]
  have sampled (q : Fin 2 → K) (k : Fin 13) (hk : i≤k) :
      D q k = -((primitive (H*ofFn 2 q)).eval (y k)*b k) := by
    have zero : T (W (H*ofFn 2 q)-M (H*ofFn 2 q)) k=0 := by
      rw [show T=mat A.transpose from rfl,mat_apply,Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : k≤l
      · rw [rcoef q l (hk.trans hl),mul_zero]
      · rw [Matrix.transpose_apply,ha (lt_of_not_ge hl),zero_mul]
    rw [eqD,Pi.sub_apply,zero,zero_sub,show W=weightedEval y b from rfl,weightedEval_apply]
  have independent (q : Fin 2 → K) (hq : D q∈U) : q=0 := by
    have u := Cut.earlierClean _ hq
    have v := Cut.laterClean _ hq
    rw [sampled q i le_rfl,neg_eq_zero] at u
    rw [sampled q j Cut.chronological.le,neg_eq_zero] at v
    have e1 : (primitive (H*ofFn 2 q)).IsRoot (y i) :=
      (mul_eq_zero.mp u).resolve_right Cut.earlierLive
    have e2 : (primitive (H*ofFn 2 q)).IsRoot (y j) :=
      (mul_eq_zero.mp v).resolve_right Cut.laterLive
    have dz := two_inclusive_primitive_detect S s3 (ofFn 2 q)
      (by have := ofFn_natDegree_lt (by decide : 0<2) q; omega) (fun z hz => by
        change (primitive (H*ofFn 2 q)).IsRoot z
        simp only [S,Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl|rfl
        · change (primitive (H*ofFn 2 q)).eval 0=0
          rw [←coeff_zero_eq_eval_zero,primitive_coeff_zero]
        · exact e1
        · exact e2)
    exact injective_ofFn _ (by rwa [map_zero])
  have gain := finrank_add_of_independent_mod hU D hZ independent
  have cap := finrank_zeroAt_annih (treeSpace A 5) t R.terminalOutFive
  have n5 := finrank_annih (treeSpace A 5)
  have n6 := finrank_annih (treeSpace A 6)
  rw [Fintype.card_fin,R.e5] at n5
  rw [Fintype.card_fin,R.e6] at n6
  change finrank K U+2≤finrank K Z at gain
  change 11+finrank K U=13 at n6
  change finrank K Z+1=finrank K (annih (treeSpace A 5)) at cap
  omega

end RKResearch.Certified.Graded.OrderElevenThirteen
