module

public import RKCert.ReviewedNative.OrderedOriginMirroredChronology
import RKCert.ReviewedNative.OneWeightOrderedSigns
import RKCert.ReviewedNative.OrderedAlternationDegree

@[expose] public section

/-! # An algebraic negative-first-clock exclusion

The removed negative factor is strictly positive in the global window.
A second negative factor would itself give a positive square test.
This proof uses ordered finite samples, not root existence or a real closure. -/
namespace RKCert.ReviewedNative.OriginSignedSquares

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem multiply_positive_mask {P M : K[X]} {S : Set K} {n : ℕ}
    (H : HasAlternationsOn P S n) (positive : ∀ x∈S, 0<M.eval x) :
    HasAlternationsOn (P*M) S n := by
  obtain ⟨xs,inc,inS,alt,rank⟩ := H.alternating_samples
  apply HasAlternationsOn.of_alternating_samples inc inS _ rank
  refine ⟨?_,?_⟩
  · intro x hx
    rw [eval_mul]
    exact mul_ne_zero (alt.nonzero x hx) (positive x (inS x hx)).ne'
  · apply alt.jumps.imp_of_mem_imp
    intro x y hx hy jump
    simp only [eval_mul]
    calc
      (P.eval x*M.eval x)*(P.eval y*M.eval y) =
          (P.eval x*P.eval y)*(M.eval x*M.eval y) := by ring
      _ < 0 := mul_neg_of_neg_of_pos jump
        (mul_pos (positive x (inS x hx)) (positive y (inS y hy)))

private theorem no_second_negative {P : K[X]} {u v w q r : K}
    (H : ThreeClockMoments P u v w) (un : u<0) (qn : q<0)
    (perm : threeHull u v w=(X-C u)*(X-C q)*(X-C r)) : False := by
  let L : K[X] := P*(X-C r)
  let B : K[X] := X*(1-X)*(X-C u)*(X-C q)
  let G := B*L^2
  have ldeg : L.natDegree ≤ 6 := natDegree_mul_le_of_le H.degree (natDegree_X_sub_C _).le
  have ln : L≠0 := mul_ne_zero H.live (X_sub_C_ne_zero r)
  have d1 : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  have bd : B.natDegree≤4 := by
    dsimp only [B]
    exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le d1)
        (natDegree_X_sub_C _).le) (natDegree_X_sub_C _).le
  have gd : G.natDegree≤19 :=
    (natDegree_mul_le_of_le bd (natDegree_pow_le_of_le 2 ldeg)).trans (by decide)
  have bPos (x : K) (hx : x∈Set.Ioo (0:K) 1) : 0<B.eval x := by
    simp only [B,eval_mul,eval_X,eval_sub,eval_one,eval_C]
    exact mul_pos (mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
      (sub_pos.mpr (un.trans hx.1))) (sub_pos.mpr (qn.trans hx.1))
  obtain ⟨i,live⟩ := exists_nonzero_grid_sample zero_lt_one ln
    (ldeg.trans_lt (by decide))
  have pos : 0 < integral 0 1 G := by
    refine integral_pos_of_grid_samples zero_lt_one gd ?_ ⟨i,?_⟩
    · intro j
      simp only [G,eval_mul,eval_pow]
      exact mul_nonneg (bPos _ (intervalPoint_mem zero_lt_one j)).le (sq_nonneg _)
    · simp only [G,eval_mul,eval_pow]
      exact mul_pos (bPos _ (intervalPoint_mem zero_lt_one i)) (sq_pos_of_ne_zero live)
  have eq : G=X*(1-X)*P*threeHull u v w*L := by
    rw [perm]
    dsimp only [G,B,L]
    ring
  exact pos.ne' (eq.symm ▸ H.mesh L ldeg)

/-- The first paid primitive cannot be at a negative clock, even when
the other selected knots are not assumed to lie in the unit interval. -/
theorem positiveFirstClock_of_finite_sign : PositiveFirstClock K := by
  intro P u v w H
  by_contra! notpos
  have un : u<0 := lt_of_le_of_ne notpos H.uNe
  have vp : 0≤v := le_of_not_gt fun vn => no_second_negative H un vn rfl
  have wp : 0≤w := H.signed_cut.1.le
  let D : K[X] := (X-C v)*(X-C w)
  let Q := P*D
  let U : K[X] := X*(1-X)*(X-C u)
  have dD : D.natDegree≤2 := natDegree_mul_le_of_le
    (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le
  have qd : Q.natDegree≤7 := natDegree_mul_le_of_le H.degree dD
  have qn : Q≠0 := mul_ne_zero H.live (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
  have uD : U.natDegree≤3 := by
    have d1 : (1-X:K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
    exact natDegree_mul_le_of_le (natDegree_mul_le_of_le natDegree_X.le d1)
      (natDegree_X_sub_C _).le
  have up (x : K) (hx : x∈Set.Ioo (0:K) 1) : 0<U.eval x := by
    simp only [U,eval_mul,eval_sub,eval_X,eval_one,eval_C]
    exact mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) (sub_pos.mpr (un.trans hx.1))
  have globalQ : HasAlternationsOn Q (Set.Ioo (0:K) 1) 7 := by
    apply HasAlternationsOn.of_grid zero_lt_one
    refine grid_variation_of_positive_moments (m:=7) zero_lt_one qn
      (qd.trans_lt (by decide)) (by omega) up ?_
    intro k
    have kd : ((X:K[X])^k.val).natDegree≤6 := by
      rw [natDegree_X_pow]
      exact Nat.le_of_lt_succ k.isLt
    have eq : U*Q*X^k.val=X*(1-X)*P*threeHull u v w*X^k.val := by
      dsimp only [U,Q,D,threeHull]
      ring
    rw [eq]
    exact H.mesh _ kd
  have flip : integral u 0 ((-X)*P)=0 := by
    rw [neg_mul,map_neg,integral_apply,formalPrimitive_eval_zero,zero_sub,neg_neg,
      ←integral_zero_left]
    exact H.first
  have localP : HasAlternationsOn P (Set.Ioo u 0) 1 := by
    apply HasAlternationsOn.of_grid un
    refine grid_variation_of_positive_moments (m:=1) (U := -(X : K[X])) un H.live
      (H.degree.trans_lt (by decide)) ?_ ?_ ?_
    · rw [natDegree_neg,natDegree_X]
      have e := H.degree
      omega
    · intro x hx
      simp only [eval_neg,eval_X]
      exact neg_pos.mpr hx.2
    · intro k
      have kv : k.val=0 := by have e:=k.isLt; omega
      simpa only [kv,pow_zero,mul_one] using flip
  have dpos (x : K) (hx : x∈Set.Ioo u 0) : 0<D.eval x := by
    simp only [D,eval_mul,eval_sub,eval_X,eval_C]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans_le vp))
      (sub_neg.mpr (hx.2.trans_le wp))
  have localQ : HasAlternationsOn Q (Set.Ioo u 0) 1 :=
    multiply_positive_mask localP dpos
  have eight : 8≤Q.natDegree := (localQ.add_open globalQ un.le le_rfl zero_le_one).le_natDegree
  omega

end
end RKCert.ReviewedNative.OriginSignedSquares
