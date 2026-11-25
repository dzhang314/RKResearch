module

public import RKCert.ReviewedNative.OrderedOriginMirroredChronology
public import RKCert.ReviewedNative.ERK17PhysicalPorts
public import RKCert.ReviewedNative.ReversePhysicalPorts
public import RKCert.ReviewedNative.LocalLinearCleanFourChronology
import RKCert.ReviewedNative.OrderedNodalGain

@[expose] public section

/-! # Extract the two actual chronological sides, without a scalar replay

The producer must retain its four actual live rows and its paid affine
reflected trace. Neither is read out of an abstract MeshPorts witness. -/
namespace RKResearch.Certified.ERK17

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse Graded.Reverse.Thin
open RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
open RKCert.ReviewedNative.OriginSignedSquares RKCert.ReviewedNative.PositiveRule19
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s p m : ℕ}

/-- Retain the affine transpose trace on the actual nonzero contrast
rows, including the two factors that really are nonzero there. -/
structure ActualReflectedAffinePacket (A : Matrix (Fin s) (Fin s) K)
    (b W : Fin s → K) (Q : K[X]) : Prop where
  live : ∀ i, W i≠0 → b i≠0 ∧ reflectedClock A i≠0
  trace : ∀ R : K[X], R.natDegree≤1 → ∀ i, W i≠0 →
    mat A.transpose (weightedEval (reflectedClock A) W R) i =
      (primitive (R*(X*Q))).eval (reflectedClock A i)*b i

theorem ActualReflectedAffinePacket.of_contrast
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} (ho : HasOrder p A b)
    {t : Fin s} (tail : reflectedClock A t=0) (col : ∀ i,A i t=0)
    (cover : SupportsComplement A b m t) (Q E : K[X])
    (qpay : m+Q.natDegree+4≤p) (epay : m+E.natDegree+5≤p)
    (on : ∀ i, reverseContrast A b Q E i≠0 →
      quadraticSeed A b i=0 ∧ b i≠0 ∧ reflectedClock A i≠0) :
    ActualReflectedAffinePacket A b (reverseContrast A b Q E) Q := by
  refine ⟨fun i wi => (on i wi).2,fun R rd i wi => ?_⟩
  exact true_port_eval ho tail col cover Q E R (by omega) (by omega) (on i wi).1

private theorem ActualReflectedAffinePacket.suffix_zero
    {A : Matrix (Fin s) (Fin s) K} {b W : Fin s → K} {Q : K[X]}
    (T : ActualReflectedAffinePacket A b W Q)
    (ha : ∀ i j,i≤j→A i j=0) {i : Fin s} (wi : W i≠0)
    (R : K[X]) (rd : R.natDegree≤1)
    (mask : ∀ j,i<j → W j≠0 → R.eval (reflectedClock A j)=0) :
    integral 0 (reflectedClock A i) (R*(X*Q))=0 := by
  have zero : mat A.transpose (weightedEval (reflectedClock A) W R) i=0 := by
    apply causal_transpose ha
    intro j hj
    have lt : i<j := Fin.rev_lt_rev.mp hj
    rw [weightedEval_apply]
    by_cases wz : W j=0
    · rw [wz,mul_zero]
    · rw [mask j lt wz,zero_mul]
  have eq := T.trace R rd i wi
  rw [zero] at eq
  have out := (mul_eq_zero.mp eq.symm).resolve_right (T.live i wi).1
  rw [integral_zero_left,formalPrimitive_eq_native]
  exact out

set_option maxRecDepth 4500
set_option maxHeartbeats 1500000

theorem PhysicalFourPort.actual_two_sided_origin
    {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) K}
    {b W θ : Fin (n+1) → K} {P : K[X]}
    (G : PhysicalFourPort A W θ P)
    (ha : ∀ i j,i≤j → A i j=0)
    (origin : (0:K)∈sites (nodes A) W)
    (rowCount : (active W).card=4)
    (T : ActualReflectedAffinePacket A b W (reflectedProfile P)) :
    ∃ u v w, TwoSidedThreeClockMoments P u v w := by
  classical
  let c := nodes A
  have siteEq : sites c W=weightedSites c W := by
    ext x
    rw [mem_sites,mem_weightedSites]
  have count : (weightedSites c W).card=4 := siteEq ▸ G.cardinal
  let E : FeedChronology c W 4 := feedChronology count
  let row (r : Fin 4) := firstRow c W (E.clock r) (E.site r)
  have spec (r : Fin 4) : W (row r)≠0 ∧ c (row r)=E.clock r :=
    firstRow_spec c W _ _
  have live (r : Fin 4) : W (row r)≠0 := (spec r).1
  have fit (r : Fin 4) : c (row r)=E.clock r := (spec r).2
  have order : StrictMono row := E.ordered
  have injective : Set.InjOn c (active W) :=
    (@Finset.card_image_iff _ _ (active W) c (Classical.decEq K)).mp (G.cardinal.trans rowCount.symm)
  have clockAt0 : c 0=0 := by
    change mat A 1 0=0
    apply causal_mat ha
    intro j hj
    exact ((not_lt_of_ge (Fin.zero_le j)) hj).elim
  have p0 : P.eval 0≠0 := by
    obtain ⟨i,wi,ei⟩ := mem_sites.mp origin
    simpa only [ei] using G.nonzeroAt i wi
  have actual0 : W 0≠0 := fun z => p0 (G.origin z)
  have zeroRank : ∃ r, E.clock r=0 :=
    E.covers 0 (siteEq ▸ origin)
  obtain ⟨r,z⟩ := zeroRank
  have r0 : row r=0 := le_antisymm
    (firstRow_le c W (E.clock r) (E.site r) actual0 (clockAt0.trans z.symm)) (Fin.zero_le _)
  have rz : r=0 := by
    apply le_antisymm _ (Fin.zero_le _)
    apply le_of_not_gt
    intro lt
    have no := order lt
    rw [r0] at no
    exact (not_lt_of_ge (Fin.zero_le _)) no
  have zeroClock : E.clock 0=0 := by simpa only [rz] using z
  have locate (i : Fin (n+1)) (wi : W i≠0) : ∃ j, row j=i := by
    obtain ⟨j,jc⟩ := E.covers (c i) (mem_weightedSites.mpr ⟨i,wi,rfl⟩)
    exact ⟨j,injective ((mem_active W _).mpr (live j)) ((mem_active W _).mpr wi)
      ((fit j).trans jc)⟩
  let u := E.clock 1
  let v := E.clock 2
  let w := E.clock 3
  have offZero {i : Fin 4} (hn : i≠0) : E.clock i≠0 :=
    fun z => hn (E.clock_injective (z.trans zeroClock.symm))
  have allClocks (i : Fin (n+1)) (wi : W i≠0) :
      c i=0 ∨ c i=u ∨ c i=v ∨ c i=w := by
    obtain ⟨j,rfl⟩ := locate i wi
    rw [fit]
    have four : ∀ j : Fin 4, j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by decide
    rcases four j with e|e|e|e
    · exact Or.inl (e.symm ▸ zeroClock)
    · exact Or.inr (Or.inl (congrArg E.clock e))
    · exact Or.inr (Or.inr (Or.inl (congrArg E.clock e)))
    · exact Or.inr (Or.inr (Or.inr (congrArg E.clock e)))
  have mesh (R : K[X]) (rd : R.natDegree≤6) :
      integral 0 1 (X*(1-X)*P*threeHull u v w*R)=0 := by
    let N := threeHull u v w
    let Z := X*N*R
    have nd : N.natDegree≤3 := by
      dsimp only [N,threeHull]
      exact natDegree_mul_le_of_le
        (natDegree_mul_le_of_le (natDegree_X_sub_C _).le (natDegree_X_sub_C _).le)
        (natDegree_X_sub_C _).le
    have zd : Z.natDegree≤10 := natDegree_mul_le_of_le
      (natDegree_mul_le_of_le natDegree_X.le nd) rd
    have q := G.quadrature Z zd
    have sum : (∑ i,Z.eval (c i)*W i)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases wz : W i=0
      · rw [wz,mul_zero]
      rcases allClocks i wz with hit|hit|hit|hit <;> simp [Z,N,threeHull,hit]
    change (formalPrimitive (Z*((1-X)*P))).eval 1=(∑ i,Z.eval (c i)*W i) at q
    rw [sum] at q
    rw [integral_zero_left]
    have eq : X*(1-X)*P*threeHull u v w*R=Z*((1-X)*P) := by dsimp only [Z,N]; ring
    rwa [eq]
  have pastOne (i : Fin (n+1)) (lt : i<row 1) (wi : W i≠0) : c i=0 := by
    obtain ⟨j,rfl⟩ := locate i wi
    have d : j<1 := order.lt_iff_lt.mp lt
    have vj : j.val<1 := d
    have eq : j=0 := Fin.ext (by change j.val=0; omega)
    rw [fit,eq,zeroClock]
  have pastTwo (i : Fin (n+1)) (lt : i<row 2) (wi : W i≠0) : c i=0 ∨ c i=u := by
    obtain ⟨j,rfl⟩ := locate i wi
    have d : j<2 := order.lt_iff_lt.mp lt
    have vj : j.val<2 := d
    have cases : j.val=0 ∨ j.val=1 := by omega
    rw [fit]
    rcases cases with a|a
    · have eq : j=0 := Fin.ext a
      exact Or.inl (eq.symm ▸ zeroClock)
    · have eq : j=1 := Fin.ext a
      exact Or.inr (congrArg E.clock eq)
  have first : integral 0 u (X*P)=0 := by
    have z := G.primitive_zero_of_prefix ha (live 1) X (by simp)
      (fun i lt wi => by rw [eval_X]; exact pastOne i lt wi)
    rw [integral_zero_left]
    change (formalPrimitive _).eval (c (row _)) = 0 at z
    rwa [fit] at z
  have second : integral 0 u (X^2*P)=0 := by
    have z := G.primitive_zero_of_prefix ha (live 1) (X^2)
      (by rw [natDegree_X_pow]) (fun i lt wi => by
        rw [eval_pow,eval_X,show nodes A i = 0 from pastOne i lt wi]
        simp)
    rw [integral_zero_left]
    change (formalPrimitive _).eval (c (row _)) = 0 at z
    rwa [fit] at z
  have next : integral 0 v (X*(X-C u)*P)=0 := by
    have d : (X*(X-C u):K[X]).natDegree≤2 := natDegree_mul_le_of_le
      natDegree_X.le (natDegree_X_sub_C _).le
    have z := G.primitive_zero_of_prefix ha (live 2) (X*(X-C u)) d (by
      intro i lt wi
      change (X*(X-C u)).eval (c i) = 0
      rcases pastTwo i lt wi with e|e <;> simp [e])
    rw [integral_zero_left]
    change (formalPrimitive _).eval (c (row _)) = 0 at z
    rwa [fit] at z
  have fLive (r : Fin 4) : P.eval (E.clock r)≠0 := by
    rw [←fit]
    exact G.nonzeroAt (row r) (live r)
  have left : ThreeClockMoments P u v w :=
    ⟨fun z=>p0 (by rw [z,eval_zero]),G.degree,
      offZero (by decide : (1:Fin 4)≠0),offZero (by decide : (2:Fin 4)≠0),
      offZero (by decide : (3:Fin 4)≠0),E.clock_ne (by decide : (2:Fin 4)≠1),
      E.clock_ne (by decide : (3:Fin 4)≠1),E.clock_ne (by decide : (3:Fin 4)≠2),
      ⟨fLive 1,fLive 2,fLive 3⟩,mesh,first,second,next⟩
  have mirrorClock (r : Fin 4) : reflectedClock A (row r)=1-E.clock r := by
    change 1-c (row r)=_
    rw [fit]
  have mirrorNe (r : Fin 4) : 1-E.clock r≠0 := by
    rw [←mirrorClock]
    exact (T.live _ (live r)).2
  have none (i : Fin (n+1)) (lt : row 3 < i) (wi : W i≠0) : False := by
    obtain ⟨j,rfl⟩ := locate i wi
    have z : (3:Fin 4)<j := order.lt_iff_lt.mp lt
    have jj : 3<j.val := z
    have cap := j.isLt
    omega
  have lastOnly (i : Fin (n+1)) (lt : row 2 < i) (wi : W i≠0) :
      reflectedClock A i=1-w := by
    obtain ⟨j,rfl⟩ := locate i wi
    have d : (2:Fin 4)<j := order.lt_iff_lt.mp lt
    have dj : 2<j.val := d
    have cap := j.isLt
    have j3 : j=3 := Fin.ext (by change j.val=3; omega)
    rw [j3,mirrorClock]
  have right0 := T.suffix_zero ha (live 3) 1 (by simp)
    (fun i lt wi=> (none i lt wi).elim)
  have right1 := T.suffix_zero ha (live 3) X (by simp)
    (fun i lt wi=> (none i lt wi).elim)
  have right2 := T.suffix_zero ha (live 2) (X-C (1-w)) (natDegree_X_sub_C _).le
    (fun i lt wi=>by simp only [eval_sub,eval_X,eval_C,lastOnly i lt wi,sub_self])
  refine ⟨u,v,w,left.two_sided_of_mirrored_prefix (mirrorNe 1) (mirrorNe 2) (mirrorNe 3)
    ?_ ?_ ?_⟩
  · simpa only [mirrorClock,one_mul] using right0
  · rw [show (X:K[X])^2*reflectedProfile P=X*(X*reflectedProfile P) by ring]
    simpa only [mirrorClock] using right1
  · rw [show X*(X-C (1-w))*reflectedProfile P=(X-C (1-w))*(X*reflectedProfile P) by ring]
    simpa only [mirrorClock] using right2

end
end RKResearch.Certified.ERK17
