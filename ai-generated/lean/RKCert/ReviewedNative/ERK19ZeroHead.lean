module

public import RKCert.ReviewedNative.ERK19ZeroHidden
public import RKCert.ReviewedNative.ERK17ContrastCount

public section

/-! # Width 29: the actual zero-seed quintic trace and its physical budget

The reflected contrast is a true signed row, not aggregate atoms.
The measured hidden carrier and the genuine quadratic support leave
room for only four or five reflected contrast sites. The trace is
forced to have degree five before any pencil is considered.
-/
namespace RKResearch.Certified.ERK19

open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKResearch.Certified.Graded.Reverse.Hidden
open RKResearch.Certified.Graded.NativeMoments
open scoped Classical

noncomputable section
variable {K : Type*} [Field K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

abbrev zeroContrastSites (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29 → K) (Q E : K[X]) :=
  weightedSites (reflectedClock A) (reverseContrast A b Q E)

structure Width29ZeroHead (A : Matrix (Fin 29) (Fin 29) K) (b h : Fin 29 → K) (Q E : K[X]) : Prop where
  staircase : FiveHiddenStaircase A 9 (hiddenCarrier A b) h
  quintic : Q.natDegree=5
  auxDegree : E.natDegree≤4
  traceQ : ∀i,quadraticSeed A b i*h i=Q.eval (reflectedClock A i)*quadraticSeed A b i
  traceE : ∀i,reflectedClock A i*b i*h i=E.eval (reflectedClock A i)*quadraticSeed A b i
  fourSites : 4≤(zeroContrastSites A b Q E).card
  fiveRows : (activeRows (reverseContrast A b Q E)).card≤5
  quadraticRows : 18≤(activeRows (quadraticSeed A b)).card
  clean : ∀ i, reverseContrast A b Q E i≠0 → ∀ v∈zeroSpace A 9, v i=0

/-- If the physical contrast has at most four clock values, its nodal
product times the quintic has nine paid X-moments. This is the exact
small-site analytic frontier, not a new scalar exclusion. -/
theorem width29_contrast_nodal_moments (ho : HasOrder 19 A b) {Q E : K[X]}
    (qd : Q.natDegree≤5) (ed : E.natDegree≤4)
    (small : (zeroContrastSites A b Q E).card≤4) :
    ∀ k : Fin 9,
      (primitive (X^k.val*(X*(Q*nodalHull (zeroContrastSites A b Q E))))).eval 1=0 := by
  let Y := reflectedClock A
  let W := reverseContrast A b Q E
  let T := zeroContrastSites A b Q E
  let N := nodalHull T
  change T.card≤4 at small
  have nd : N.natDegree=T.card := natDegree_nodalHull T
  have root (a : K) (ha : a∈T) : N.eval a=0 := nodalHull_eval_of_mem ha
  intro k
  let R : K[X] := X^k.val*N
  have rd : R.natDegree≤k.val+T.card :=
    natDegree_mul_le_of_le (natDegree_X_pow _).le nd.le
  have z : (∑ i,weightedEval Y W R i)=0 :=
    reverse_contrast_vanishes W R (fun a ha => by simp [R,root a ha])
  have e := reverse_contrast_moment ho Q E R (by have := k.isLt; omega)
    (by have := k.isLt; omega)
  rw [z] at e
  rw [show X^k.val*(X*(Q*N))=R*(X*Q) by dsimp only [R];ring]
  exact e.symm

variable [CharZero K]

theorem width29_contrast_sites_ge_four (ho : HasOrder 19 A b)
    {Q E : K[X]} (qn : Q≠0) (qd : Q.natDegree≤5) (ed : E.natDegree≤4) :
    4≤(zeroContrastSites A b Q E).card := by
  let T := zeroContrastSites A b Q E
  let N := nodalHull T
  have nd : N.natDegree=T.card := natDegree_nodalHull T
  have nz : N≠0 := (monic_nodalHull T).ne_zero
  change 4≤T.card
  by_contra! small
  have deg : (Q*N).natDegree≤8 := natDegree_mul_le.trans (by omega)
  have lim : (zeroContrastSites A b Q E).card≤4 := by change T.card≤4; omega
  exact (mul_ne_zero qn nz) (x_moments_detect deg
    (width29_contrast_nodal_moments ho qd ed lim))

omit [CharZero K] in
theorem Width29ZeroHead.four_site_orthogonal
    {h : Fin 29→K} {Q E : K[X]} (H : Width29ZeroHead A b h Q E)
    (ho : HasOrder 19 A b) (four : (zeroContrastSites A b Q E).card=4) :
    (Q*nodalHull (zeroContrastSites A b Q E)).natDegree=9 ∧
      ∀ k : Fin 9,
        (primitive (X^k.val*(X*(Q*nodalHull (zeroContrastSites A b Q E))))).eval 1=0 := by
  have nq : Q≠0 := by intro z; have d := H.quintic; simp [z] at d
  exact ⟨by rw [natDegree_mul nq (monic_nodalHull _).ne_zero,H.quintic,natDegree_nodalHull,four],
    width29_contrast_nodal_moments ho H.quintic.le H.auxDegree four.le⟩

end
end RKResearch.Certified.ERK19

namespace RKResearch.Certified.ERK19
open RKResearch Polynomial Module RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin
open RKResearch.Certified.Graded.Reverse.Hidden
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29 → K}

set_option maxHeartbeats 850000 in
theorem width29_zero_head (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 19 A b)
    (zero : firstSeed A b=0) :
    ∃ (h : Fin 29→K) (Q E : K[X]), Width29ZeroHead A b h Q E := by
  let t := Fin.last 28
  let y := reflectedClock A
  let c := nodes A
  let d := quadraticSeed A b
  let U := hiddenCarrier A b
  let G := blindRows c b d 0 t
  have S := (ordered_width29_frame ha ho).1
  have Z := width29_zero_cover_data ha ho zero
  have F := width29_hidden_frame_from_cover ha ho S Z
  have dim : finrank K U=5 := width29_hidden_rank_five ha ho S Z F
  obtain ⟨h,chart⟩ := five_hidden_staircase ha (by decide) S.separated S.middleDefects
    (width29_F10_cap S) dim F.toNine F.stable
  have zt : y t=0 := by change 1-nodes A t=0; rw [Z.lastClock,sub_self]
  have col (k : Fin 29) : A k t=0 := ha k t (Fin.le_last k)
  have tail : SupportsComplement A b 9 t := supportsComplement_of_cover Z.pointwise
  obtain ⟨Q,E,qd,ed,qfit,efit⟩ := thin_reverse_two_traces ho chart.headGrade
    (by decide) (by decide) (by decide) t zt Z.lastSeed Z.sites Z.pointwise
  have outside : ¬Q.natDegree≤4 := by
    intro short
    have van := ordered_thin_invisible_given_reps ha ho zt col tail Q E short
      (by omega) (by omega) (by omega) (by omega) qfit efit
    exact chart.outside (actual_defect_hidden ha ho (by decide) chart.headGrade
      (fun i => (van i).1) (fun i => (van i).2))
  have five : Q.natDegree=5 := by omega
  have qn : Q≠0 := by intro e; simp [e] at five
  let W := reverseContrast A b Q E
  have act (i : Fin 29) (w : W i≠0) :
      d i=0 ∧ y i≠0 ∧ b i≠0 ∧ Q.eval (y i)≠0 ∧ h i=0 :=
    reverse_contrast_true_support qfit efit i w
  have wzeroT : W t=0 := by by_contra n; exact (act t n).2.1 zt
  have wzeroD (i : Fin 29) (dn : d i≠0) : W i=0 := by by_contra n; exact dn (act i n).1
  have wzeroG (i : Fin 29) (ig : i∈G) : W i=0 := by
    obtain ⟨_,_,d0,b0⟩ := (mem_blindRows i).mp ig
    have eq : y i*b i=0 := by simpa [y,reflectedClock] using b0
    change (weightedEval y b (X*Q)-weightedEval y d E) i=0
    simp only [Pi.sub_apply,weightedEval_apply,eval_mul,eval_X,d0,mul_zero,sub_zero]
    linear_combination Q.eval (y i)*eq
  have enough : 9≤(weightedSites y d).card := Z.sites
  have quadRows : 18≤(activeRows d).card := by
    apply RKResearch.Certified.ERK17.signed_fiber_payment y d 9 enough
    intro P pd
    have e := seed_eval_mass ho P (by omega)
    simpa only [weightedEval_apply,mul_comm] using e
  have bill := carrier_contrast_budget (w:=W) Z.lastLive Z.lastSeed wzeroT wzeroD wzeroG
  change finrank K U+(activeRows d).card+(activeRows W).card+1≤29 at bill
  have rows : (activeRows W).card≤5 := by omega
  refine ⟨h,Q,E,⟨chart,five,ed,qfit,efit,width29_contrast_sites_ge_four ho qn qd ed,
    rows,quadRows,fun i wi v hv => ?_⟩⟩
  rw [chart.midpoint] at hv
  obtain ⟨u,hu,P,_,eq⟩ := HeadFiber.exists_poly hv
  have product : (y i*b i)*u i=0 := by
    simpa [y,reflectedClock] using Hidden.carrier_mirror_weight_zero Z.lastClock hu i
  have uz := (mul_eq_zero.mp product).resolve_left (mul_ne_zero (act i wi).2.1 (act i wi).2.2.1)
  rw [eq,Pi.add_apply,uz,weightedEval_apply,(act i wi).2.2.2.2,mul_zero,add_zero]

end
end RKResearch.Certified.ERK19

