module

public import RKCert.ReviewedNative.CrossedPositiveTailRoots
public import RKCert.ReviewedNative.CrossedGaussianReflection
public import RKCert.ReviewedNative.FiniteGaussianScalarLift
public import RKCert.ReviewedNative.ERKOrder16WeakFiveMoments
public import RKCert.ReviewedNative.GuardedGroupedMoments
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Actual weak-five crossed positive-tail phase, up to the root source

Draft. The checked Moment packet and its paid signed law are unchanged.
The last geometric hypothesis is the open-unit crossed phase of the
monic normalization, not a sign assertion in an extension.
-/
namespace RKCert.ReviewedNative.WeakFiveCrossedPositiveTail

open Polynomial Set
open RKCert.ReviewedNative.PositiveRule19
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.CrossedPositiveTailRoots
open RKCert.ReviewedNative.FiniteGaussianNodalLift
open RKCert.ReviewedNative.FiniteGaussianGridPositivity
open RKCert.ReviewedNative.FiniteGaussianLocalizer
open RKCert.ReviewedNative.CrossedGaussianSignedAdapter
open RKCert.ReviewedNative.CrossedGaussianScalarLift
open RKCert.ReviewedNative.CrossedGaussianReflection
open RKCert.ReviewedNative.CrossedGaussianEndpointBridge
open RKCert.ReviewedNative.WeakFive16
open scoped BigOperators

noncomputable section
variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L]

private theorem map_four_marks (e : K →+* L) (z h a u : K) :
    (fourMarks z h a u).map (⟨e,e.injective⟩ : K ↪ L) =
      fourMarks (e z) (e h) (e a) (e u) := by
  simp only [fourMarks,Finset.map_insert,Finset.map_singleton]
  rfl

private theorem rational_sample_bounds {x : K} (hx : x ∈ rationalSamples K) :
    0≤x ∧ x≤1 := by
  simp only [rationalSamples,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num

private theorem rational_samples_on_base (e : K →+* L) (B : L[X])
    (base : ∀ x ∈ Icc (0:K) 1, 0≤B.eval (e x)) :
    ∀ y ∈ rationalSamples L, 0≤B.eval (uncenterPoint y) := by
  have mapped : (rationalSamples K).map e = rationalSamples L := by
    simp only [rationalSamples,List.map_cons,List.map_nil,map_zero,map_one,map_div₀,map_ofNat]
  intro y hy
  rw [← mapped] at hy
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
  have hb := rational_sample_bounds hx
  have hm : uncenterPoint (e x) = e (uncenterPoint x) := by
    simp only [uncenterPoint,map_div₀,map_add,map_one,map_ofNat]
  rw [hm]
  apply base
  constructor <;> unfold uncenterPoint <;> linarith only [hb.1,hb.2]

private theorem grid_on_base (e : K →+* L) (B : L[X])
    (base : ∀ x ∈ Icc (0:K) 1, 0≤B.eval (e x))
    {l : K} (l0 : 0≤l) (l1 : l<1) :
    ∀ i : Fin 19, 0≤B.eval (intervalPoint (e l) 1 i) := by
  simpa only [map_one] using intervalGrid_nonneg_of_base e B
    (fun x hx₀ hx₁ => base x ⟨hx₀,hx₁⟩) l0 (le_refl (1:K)) l1

private theorem flip_nonneg_on_base (e : K →+* L) (B : L[X])
    (base : ∀ x ∈ Icc (0:K) 1, 0≤B.eval (e x)) :
    ∀ x ∈ Icc (0:K) 1, 0≤(flipPoly B).eval (e x) := by
  intro x hx
  have inside : 1-x ∈ Icc (0:K) 1 :=
    ⟨sub_nonneg.mpr hx.2,sub_le_self _ hx.1⟩
  simpa only [flipPoly_eval,flipClock,map_sub,map_one] using base (1-x) inside

/-- No new RK theorem is consumed here: use the actual signed degree-nine
packet and both pairs of endpoint moments of the monic profile. In either
orientation the earlier endpoint bridge consumes only one of the pairs. -/
theorem no_crossed_monic_phase_of_signed_packet (e : K →+* L) (ord : StrictMono e)
    {p : K[X]} {z h a u : K} (phase : CrossedSignPhase p z h a u)
    (monic : p.Monic) (degree : p.natDegree=4) (source : UnitRootSource e p)
    {μ : K → K} (law : ExactRule (unitMoment p) (fourMarks z h a u) id μ 9)
    (f₁ : integral 0 u (X*p)=0) (f₂ : integral 0 u (X^2*p)=0)
    (b₁ : integral z 1 ((1-X)*p)=0) (b₂ : integral z 1 ((1-X)^2*p)=0) :
    False := by
  obtain ⟨r,s,B,R⟩ := root_residual_of_crossed_phase e ord phase monic degree source
  let P := p.map e
  let ν (y : L) := e (μ (Function.invFun e y))
  have mappedLaw : ExactRule (unitMoment P) (fourMarks (e z) (e h) (e a) (e u)) id ν 9 := by
    have lift := unitMoment_map_signedRule e p (μ' := ν) (fun x _ => by
      dsimp only [ν]
      rw [Function.leftInverse_invFun e.injective x]) law
    simpa only [P,map_four_marks] using lift
  have f₁L : integral 0 (e u) (X*P)=0 := by
    have x := congrArg (fun c : K => e c) f₁
    rw [← integral_map e 0 u (X*p)] at x
    simpa only [map_zero,Polynomial.map_mul,map_X,P] using x
  have f₂L : integral 0 (e u) (X^2*P)=0 := by
    have x := congrArg (fun c : K => e c) f₂
    rw [← integral_map e 0 u (X^2*p)] at x
    simpa only [map_zero,Polynomial.map_mul,Polynomial.map_pow,map_X,P] using x
  have b₁L : integral (e z) 1 ((1-X)*P)=0 := by
    have x := congrArg (fun c : K => e c) b₁
    rw [← integral_map e z 1 ((1-X)*p)] at x
    simpa only [map_zero,map_one,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,
      map_X,P] using x
  have b₂L : integral (e z) 1 ((1-X)^2*P)=0 := by
    have x := congrArg (fun c : K => e c) b₂
    rw [← integral_map e z 1 ((1-X)^2*p)] at x
    simpa only [map_zero,map_one,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,
      Polynomial.map_one,map_X,P] using x
  have ez0 : 0<e z := by simpa only [map_zero] using ord phase.z0
  have eu1 : e u<1 := by simpa only [map_one] using ord phase.u1
  have u0 : 0<u := phase.z0.trans (phase.zh.trans (phase.ha.trans phase.au))
  have z1 : z<1 := phase.zh.trans (phase.ha.trans (phase.au.trans phase.u1))
  by_cases orientation : B.eval 1 ≤ B.eval 0
  · exact crossed_interior_positive_tail_contradiction (e z) r (e h) (e a) s (e u) P B ν
      ez0 R.zr R.rh (ord phase.ha) R.as' R.su eu1 R.factor R.monic R.degree orientation
      (rational_samples_on_base e B R.baseNonneg)
      (by simpa only [map_zero] using grid_on_base e B R.baseNonneg (le_refl (0:K)) zero_lt_one)
      (grid_on_base e B R.baseNonneg u0.le phase.u1) mappedLaw f₁L f₂L
  · have BN := flip_nonneg_on_base e B R.baseNonneg
    have RL := exact_flip_rule mappedLaw
    rw [flip_fourMarks] at RL
    have znew : 0<flipClock (e u) := by unfold flipClock; linarith only [eu1]
    have unew : flipClock (e z)<1 := by unfold flipClock; linarith only [ez0]
    have tail : ∀ i : Fin 19, 0≤(flipPoly B).eval (intervalPoint (flipClock (e z)) 1 i) := by
      simpa only [flipClock,map_sub,map_one] using grid_on_base e (flipPoly B) BN
        (sub_nonneg.mpr z1.le) (show 1-z<1 by linarith only [phase.z0])
    exact crossed_interior_positive_tail_contradiction
      (flipClock (e u)) (flipClock s) (flipClock (e a)) (flipClock (e h))
      (flipClock r) (flipClock (e z)) (flipPoly P) (flipPoly B) (ν ∘ flipClock)
      znew (flipClock_order R.su) (flipClock_order R.as') (flipClock_order (ord phase.ha))
      (flipClock_order R.rh) (flipClock_order R.zr) unew
      (flip_crossed_factor P B r s R.factor) (flip_monic_quadratic B R.monic R.degree)
      ((flipPoly_degree B).trans R.degree) (flip_oriented B (le_of_not_ge orientation))
      (rational_samples_on_base e (flipPoly B) BN)
      (by simpa only [map_zero] using grid_on_base e (flipPoly B) BN (le_refl (0:K)) zero_lt_one)
      tail RL (flip_forward_first P (e z) b₁L) (flip_forward_second P (e z) b₂L)

def monicProfile (q : K[X]) : K[X] := q*C (q.leadingCoeff⁻¹)

theorem monicProfile_monic (q : K[X]) (qn : q ≠ 0) : (monicProfile q).Monic :=
  monic_mul_leadingCoeff_inv qn

theorem monicProfile_degree (q : K[X]) (qn : q ≠ 0) :
    (monicProfile q).natDegree = q.natDegree :=
  natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr qn))

private theorem normalize_zero (q F : K[X]) (l r : K)
    (paid : integral l r (F*q)=0) : integral l r (F*monicProfile q)=0 := by
  have eq : F*monicProfile q = C (q.leadingCoeff⁻¹)*(F*q) := by unfold monicProfile; ring
  rw [eq,moment_C_mul,paid,mul_zero]

theorem signed_rule_normalize {q : K[X]} {old : Finset K} {μ : K → K} {d : ℕ}
    (law : GroupedUnitMoments (X*(1-X)) q old μ d) :
    ExactRule (unitMoment (monicProfile q)) old id
      (fun x => q.leadingCoeff⁻¹*μ x) d := by
  intro F fd
  have eq : (unitWeight K*monicProfile q)*F =
      C (q.leadingCoeff⁻¹)*((X*(1-X))*q*F) := by unfold monicProfile unitWeight; ring
  rw [unitMoment_apply,eq,moment_C_mul,law F fd,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [id_eq,mul_assoc]

/-- Direct attachment to the checked weak-five shape and its original
guarded signed moment law, with a phase on the monic profile. -/
theorem no_actual_crossed_positive_tail_of_signed_law (e : K →+* L) (ord : StrictMono e)
    {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) (degree : q.natDegree=4)
    (phase : CrossedSignPhase (monicProfile q) (c 4) (c 3) (c 2) (c 1))
    (source : UnitRootSource e (monicProfile q)) {μ : K → K}
    (law : GroupedUnitMoments (X*(1-X)) q (fourMarks (c 4) (c 3) (c 2) (c 1)) μ 9) :
    False :=
  no_crossed_monic_phase_of_signed_packet e ord phase (monicProfile_monic q M.qNonzero)
    ((monicProfile_degree q M.qNonzero).trans degree) source (signed_rule_normalize law)
    (normalize_zero q X 0 (c 1) M.forwardFirst)
    (normalize_zero q (X^2) 0 (c 1) M.forwardSecond)
    (normalize_zero q (1-X) (c 4) 1 M.reverseFirst)
    (normalize_zero q ((1-X)^2) (c 4) 1 M.reverseSecond)

/-- Reuse an already constructed nodal rule on the remainder. This
separate extension spends the two extra *quotient* tests paid at the
old four nodes; the Lagrange construction itself is not repeated. -/
private theorem exact_over_larger_quotients
    {J : K[X] →ₗ[K] K} {s : Finset K} {μ : K → K} {d b : ℕ}
    (someNode : s.Nonempty) (law : ExactRule J s id μ d) (low : s.card-1 ≤ d)
    (orthog : ∀ Q : K[X], Q.natDegree ≤ b → J (Lagrange.nodal s id*Q)=0) :
    ExactRule J s id μ (s.card+b) := by
  intro P pd
  let N : K[X] := Lagrange.nodal s id
  let R := P %ₘ N
  let Q := P /ₘ N
  have monic : N.Monic := Lagrange.nodal_monic
  have nd : N.natDegree=s.card := Lagrange.natDegree_nodal
  have n1 : N≠1 := by
    intro h
    rw [h,natDegree_one] at nd
    exact (Nat.ne_of_gt someNode.card_pos) nd.symm
  have rd : R.natDegree ≤ d := by
    have lt := natDegree_modByMonic_lt P monic n1
    change R.natDegree < N.natDegree at lt
    omega
  have qd : Q.natDegree ≤ b := by
    change (P /ₘ N).natDegree ≤ b
    rw [natDegree_divByMonic P monic,nd]
    omega
  have hP : P = R+N*Q := (modByMonic_add_div P N).symm
  have hJ : J P = J R := by
    rw [hP,map_add]
    change J R+J (Lagrange.nodal s id*Q)=J R
    rw [orthog Q qd,add_zero]
  rw [hJ,law R rd]
  apply Finset.sum_congr rfl
  intro x hx
  rw [show R.eval (id x)=P.eval (id x) by
    change (P %ₘ N).eval (id x)=P.eval (id x)
    have nd0 : N.eval (id x)=0 := Lagrange.eval_nodal_at_node hx
    rw [modByMonic_eq_sub_mul_div,eval_sub,eval_mul,nd0,zero_mul,sub_zero]]

/-- The checked weak-five nodal annihilations already determine a signed
degree-nine rule at the four marked clocks. This recovers the rule if
the checked packet was saved after eliminating its masses. -/
theorem Moments.exists_signed_four_rule {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) :
    ∃ μ : K → K, GroupedUnitMoments (X*(1-X)) q
      (fourMarks (c 4) (c 3) (c 2) (c 1)) μ 9 := by
  let old := fourMarks (c 4) (c 3) (c 2) (c 1)
  have nc {i j : Fin 5} (h : i≠j) : c i≠c j := fun eq => h (M.clockSimple eq)
  have hn₂ : c 2 ∉ ({c 1} : Finset K) := by simp [nc (by decide : (2:Fin 5)≠1)]
  have hn₃ : c 3 ∉ ({c 2,c 1} : Finset K) := by
    simp [nc (by decide : (3:Fin 5)≠2),nc (by decide : (3:Fin 5)≠1)]
  have hn₄ : c 4 ∉ ({c 3,c 2,c 1} : Finset K) := by
    simp [nc (by decide : (4:Fin 5)≠3),nc (by decide : (4:Fin 5)≠2),
      nc (by decide : (4:Fin 5)≠1)]
  have n : old.card=4 := by
    unfold old fourMarks
    rw [Finset.card_insert_of_notMem hn₄,Finset.card_insert_of_notMem hn₃,
      Finset.card_insert_of_notMem hn₂,Finset.card_singleton]
  have node : old.Nonempty := ⟨c 4,by simp [old,fourMarks]⟩
  have nd : Lagrange.nodal old id = nodalTail c Z := by
    unfold old fourMarks
    rw [Lagrange.nodal_insert_eq_nodal hn₄,Lagrange.nodal_insert_eq_nodal hn₃,
      Lagrange.nodal_insert_eq_nodal hn₂,Lagrange.nodal_eq]
    simp only [Finset.prod_singleton,id_eq,nodalTail,M.middleFactor]
    ring
  have ort (P : K[X]) (pd : P.natDegree≤5) : unitMoment q (Lagrange.nodal old id*P)=0 := by
    rw [unitMoment_apply,nd]
    simpa only [unitWeight,mul_assoc] using M.weightedMoments P pd
  let μ := cardinalMass (unitMoment q) old id
  have initial : ExactRule (unitMoment q) old id μ (2*old.card-1) :=
    gaussian_exact_of_annihilates (unitMoment q) old id Function.injective_id.injOn
      (fun P pd => ort P (pd.trans (by rw [n] <;> decide)))
  have wide : ExactRule (unitMoment q) old id μ (old.card+5) :=
    exact_over_larger_quotients node initial (by omega) ort
  refine ⟨μ,?_⟩
  intro P pd
  simpa only [unitMoment_apply,unitWeight,id_eq] using wide P (by simpa only [n] using pd)

/-- The full checked scalar packet suffices, in either residual
orientation. The only extra field hypothesis is the root source. -/
theorem no_actual_crossed_positive_tail (e : K →+* L) (ord : StrictMono e)
    {q Z : K[X]} {c : Fin 5 → K} (M : Moments q Z c) (degree : q.natDegree=4)
    (phase : CrossedSignPhase (monicProfile q) (c 4) (c 3) (c 2) (c 1))
    (source : UnitRootSource e (monicProfile q)) : False := by
  obtain ⟨μ,law⟩ := Moments.exists_signed_four_rule M
  exact no_actual_crossed_positive_tail_of_signed_law e ord M degree phase source law

end
end RKCert.ReviewedNative.WeakFiveCrossedPositiveTail
