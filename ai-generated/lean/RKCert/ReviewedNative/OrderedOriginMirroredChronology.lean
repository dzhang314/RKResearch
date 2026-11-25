module

public import RKCert.ReviewedNative.OrderedOriginSignedSquares

@[expose] public section

/-! # Pure mirrored chronology for the three-clock signed-square cut

The negative and right-pole smallest-clock exclusions are named inputs.
No ordered-root theorem is treated as already formalized. -/
namespace RKCert.ReviewedNative.OriginSignedSquares

open Polynomial RKCert.Endpoint RKCert.ReviewedNative.PositiveRule19
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

abbrev reflectedProfile (P : K[X]) : K[X] := P.comp (1-X)

theorem reflectedProfile_twice (P : K[X]) : reflectedProfile (reflectedProfile P)=P := by
  change (P.comp (1-X)).comp (1-X)=P
  rw [comp_assoc,show (1-X : K[X]).comp (1-X)=X by
    simp only [sub_comp,one_comp,X_comp]; ring,comp_X]

theorem reflectedProfile_degree (P : K[X]) :
    (reflectedProfile P).natDegree≤P.natDegree := by
  exact natDegree_comp_le.trans (by
    have d : (1-X : K[X]).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
    exact (Nat.mul_le_mul_left _ d).trans_eq (Nat.mul_one _))

theorem reflectedProfile_eval (P : K[X]) (a : K) :
    (reflectedProfile P).eval (1-a)=P.eval a := by
  simp only [reflectedProfile,eval_comp,eval_sub,eval_one,eval_X]
  rw [show 1-(1-a)=a by ring]

private theorem threeHull_reflected (u v w : K) :
    reflectedProfile (threeHull u v w) = -threeHull (1-w) (1-v) (1-u) := by
  simp only [reflectedProfile,threeHull,mul_comp,sub_comp,X_comp,C_comp,map_sub,map_one]
  ring

theorem ThreeClockMoments.mesh_mirrored {P : K[X]} {u v w : K}
    (H : ThreeClockMoments P u v w) (R : K[X]) (rd : R.natDegree≤6) :
    integral 0 1 (X*(1-X)*reflectedProfile P*threeHull (1-w) (1-v) (1-u)*R)=0 := by
  let T := X*(1-X)*P*threeHull u v w*reflectedProfile R
  have orig : integral 0 1 T=0 := H.mesh _ ((reflectedProfile_degree R).trans rd)
  have dq : integral 0 1 (T.comp (1-X))=integral 0 1 T := by
    simpa only [sub_zero] using integral_reflect T (0:K)
  have comp : T.comp (1-X) = -(X*(1-X)*reflectedProfile P*
      threeHull (1-w) (1-v) (1-u)*R) := by
    change reflectedProfile T=_
    have compMul (H J : K[X]) :
        reflectedProfile (H*J)=reflectedProfile H*reflectedProfile J := mul_comp _ _ _
    have compX : reflectedProfile (X : K[X])=1-X := X_comp
    have compX' : reflectedProfile (1-X : K[X])=X := by
      change (1-X : K[X]).comp (1-X)=X
      simp only [sub_comp,one_comp,X_comp]
      ring
    dsimp only [T]
    simp only [compMul,compX,compX',threeHull_reflected,reflectedProfile_twice]
    ring
  rw [comp,map_neg,orig,neg_eq_zero] at dq
  exact dq

structure TwoSidedThreeClockMoments (P : K[X]) (u v w : K) : Prop where
  left : ThreeClockMoments P u v w
  right : ThreeClockMoments (reflectedProfile P) (1-w) (1-v) (1-u)

theorem ThreeClockMoments.two_sided_of_mirrored_prefix {P : K[X]} {u v w : K}
    (H : ThreeClockMoments P u v w)
    (un : (1-u : K)≠0) (vn : (1-v : K)≠0) (wn : (1-w : K)≠0)
    (first : integral 0 (1-w) (X*reflectedProfile P)=0)
    (second : integral 0 (1-w) (X^2*reflectedProfile P)=0)
    (next : integral 0 (1-v) (X*(X-C (1-w))*reflectedProfile P)=0) :
    TwoSidedThreeClockMoments P u v w := by
  have rn : reflectedProfile P≠0 := by
    intro z
    have h := reflectedProfile_twice P
    rw [z] at h
    exact H.live (by simpa using h.symm)
  have reflected_ne {a b : K} (n : a≠b) : 1-a≠1-b :=
    fun eq => n ((sub_right_inj (a:=1)).mp eq)
  refine ⟨H,⟨rn,(reflectedProfile_degree P).trans H.degree,wn,vn,un,
    reflected_ne H.wvNe.symm,reflected_ne H.wuNe.symm,reflected_ne H.vuNe.symm,
    ?_,H.mesh_mirrored,first,second,next⟩⟩
  simpa only [reflectedProfile_eval] using
    (show P.eval w≠0 ∧ P.eval v≠0 ∧ P.eval u≠0 from
      ⟨H.knotLive.2.2,H.knotLive.2.1,H.knotLive.1⟩)

def PositiveFirstClock (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop :=
  ∀ (P : K[X]) (u v w : K), ThreeClockMoments P u v w → 0<u

def NoSmallestClock (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop :=
  ∀ (P : K[X]) (u v w : K), ThreeClockMoments P u v w → 0<u → u<1 → u<v → u<w → False

theorem TwoSidedThreeClockMoments.impossible_of_positive_and_not_smallest
    (positive : PositiveFirstClock K) (smallest : NoSmallestClock K)
    {P : K[X]} {u v w : K} (H : TwoSidedThreeClockMoments P u v w) : False := by
  have u0 := positive P u v w H.left
  have rw0 := positive _ _ _ _ H.right
  have w0 := H.left.signed_cut.1
  have ru0 := H.right.signed_cut.1
  have u1 : u<1 := sub_pos.mp ru0
  have rw1 : 1-w<1 := by
    have e := sub_lt_sub_left w0 (1:K)
    simpa only [sub_zero] using e
  have contra := H.left.signed_cut.2 u0
  have uw : u<w := by
    by_contra! wu
    exact contra.not_ge (mul_nonneg ru0.le (sub_nonneg.mpr wu))
  rcases lt_or_gt_of_ne H.left.vuNe.symm with uv | vu
  · exact smallest P u v w H.left u0 u1 uv uw
  · exact smallest _ _ _ _ H.right rw0 rw1
      (sub_lt_sub_left (vu.trans uw) 1) (sub_lt_sub_left uw 1)

end
end RKCert.ReviewedNative.OriginSignedSquares
