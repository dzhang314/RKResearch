module

public import RKCert.ReviewedNative.SDIRK118LiteralClaimPin

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11

open RKResearch RKResearch.FiniteRootedTree
open RKResearch.Certified.Graded (mat)
open RKResearch.Certified.PaidDefectBridge
open RKResearch.Certified.PaidDefectBridge.ChartInstantiation
open RKResearch.Certified.PaidDefectBridge.ForwardChart (V polyProject pivot)
open RKResearch.Certified.PaidDefectBridge.ReverseChart
open RKResearch.Certified.PaidDefectBridge.SDIRK118 (PolyBound V6 V8 wDot)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ClaimPin
open RKResearch.Certified.PaidDefectBridge.SDIRK118.LiteralAssembly (Geometry ideal oldIx rev_restrict)
open RKResearch.Certified.PaidDefectBridge.SDIRK118.ScalarBindings
open scoped Matrix BigOperators FiniteRootedTree

/-- Physical reverse nodes and defect for the actual four old slots.
The argument cStar is immaterial to these two vectors. -/
def reverseClock (s t : ℝ) : V ℝ := (zAt s)⁻¹ • uAt s t

def reverseG (s : ℝ) : V ℝ := ((zAt s)⁻¹ ^ 2) • gAt s 0

/-- Physical forward nodes and defect for the actual four old slots. -/
def forwardClock (M : MonomialBasis) (s t cStar : ℝ) : V ℝ :=
  (zAt s)⁻¹ • uAt s (dAt M s t cStar)

def forwardG (M : MonomialBasis) (s t cStar : ℝ) : V ℝ :=
  let d := dAt M s t cStar
  ((zAt s)⁻¹ ^ 2) • gAt s (gdAt s (etaAt s) d)

/-- Exact primitive/cardinal obligations on the literal scalar data.
None of these is a tree/word/order assertion. -/
structure ScalarLeaves (g : Geometry ℝ) : Prop where
  mass : ∀ i, g.W i ≠ 0
  quadrature : HasQuadratureOrder 8 g.W (g.Ex Polynomial.X)
  clock : ∀ (P : Polynomial ℝ),
    g.Ey ((1 - Polynomial.X) * P) = (g.Ex Polynomial.X) * g.Ey P
  primitiveBound : ∀ (n : ℕ) (P : Polynomial ℝ),
    PolyBound n P → PolyBound (n + 1) (g.I P)
  clockBound : ∀ (n : ℕ) (P : Polynomial ℝ),
    PolyBound n P → PolyBound (n + 1) ((1 - Polynomial.X) * P)
  green : ∀ (H P : Polynomial ℝ) (n m : ℕ),
    PolyBound n H → PolyBound m P → n + m + 1 ≤ 7 →
    wDot g.W (g.Ex H) (g.Ey (g.I P)) = wDot g.W (g.Ex (g.I H)) (g.Ey P)
  missingCell : g.pairing (g.HF 0) (g.KR 1) = 0

private def reverseSite (k : Fin 4) : Fin 6 := ⟨k.val, by have hk := k.isLt; omega⟩

/-- Reverse leaves are literal matrix moments and two primitive evaluation
interfaces. Reverse words through length three are produced below. -/
structure ReverseLeaves (g : Geometry ℝ) (c d : V ℝ) : Prop where
  distinct01 : c 0 ≠ c 1
  distinct02 : c 0 ≠ c 2
  distinct12 : c 1 ≠ c 2
  pivotNe : pivot c d ≠ 0
  lower : g.R.IsLowerTriangular
  diagonal : ∀ i, g.R i i = g.γ
  sum : mat g.R (1 : V ℝ) = c
  moment : mat g.R c = (2 : ℝ)⁻¹ • c ^ 2 + d
  reflectedSites : g.ξ ∘ oldIx = 1 - c
  anchor2 : LocalThree g.R c d 2
  anchor3 : LocalThree g.R c d 3
  evalClock2 : g.Ey Polynomial.X 2 = c 2
  evalClock3 : g.Ey Polynomial.X 3 = c 3
  cubicCardinal : ∀ P : Polynomial ℝ, PolyBound 3 P →
    g.Ey P 2 = 0 → g.Ey P 3 = 0 →
    P = g.Ey P 0 • g.KR 0 + g.Ey P 4 • g.KR 1

def ForwardCubic (g : Geometry ℝ) (t : FiniteRootedTree) : Prop :=
  g.F t = g.Ex (g.F t) 4 • g.HF 0 + g.Ex (g.F t) 5 • g.HF 1

/-- Forward matrix/row and five finite cubic cases. The higher-order
degree gate and the lower-order seeds are derived, not passed. -/
structure ForwardLeaves (g : Geometry ℝ) (c d : V ℝ) : Prop where
  distinct01 : c 0 ≠ c 1
  distinct02 : c 0 ≠ c 2
  distinct12 : c 1 ≠ c 2
  pivotNe : pivot c d ≠ 0
  lower : g.G.IsLowerTriangular
  diagonal : ∀ i, g.G i i = g.γ
  sum : g.G *ᵥ (1 : V ℝ) = c
  moment : g.G *ᵥ c = (2 : ℝ)⁻¹ • c ^ 2 + d
  anchor2 : LocalThree g.G c d 2
  evalClock1 : g.Ex Polynomial.X 1 = c 2
  topA : ForwardCubic g (t3a ◂ t1)
  topB : ForwardCubic g (t3b ◂ t1)
  topC : ForwardCubic g (t2 ◂ t2)
  topD : ForwardCubic g (t1 ◂ t3a)
  topE : ForwardCubic g (t1 ◂ t3b)

/-- The three remaining proof obligations use the actual literal geometry.
They are not generic instances at a tableau selected after the fact. -/
structure LeafCertificates (M : MonomialBasis) (s t cStar : ℝ) : Prop where
  scalar : ScalarLeaves (geometry M s t cStar)
  forward : ForwardLeaves (geometry M s t cStar) (forwardClock M s t cStar)
    (forwardG M s t cStar)
  reverse : ReverseLeaves (geometry M s t cStar) (reverseClock s t) (reverseG s)

private theorem project_bound (c d v : V ℝ) :
    PolyBound 2 (polyProject c d v) := by
  intro j hj
  have j0 : j ≠ 0 := by omega
  have j1 : j ≠ 1 := by omega
  have j2 : j ≠ 2 := by omega
  change (ForwardChart.toPoly (ForwardChart.project c d v)).coeff j = 0
  simp [ForwardChart.toPoly_apply, Polynomial.coeff_one, Polynomial.coeff_X,
    Polynomial.coeff_X_pow, j0, j0.symm, j1, j1.symm, j2, j2.symm]

private theorem profile_bound (g : Geometry ℝ) (cert : ScalarLeaves g) :
    ∀ W, PolyBound W.length (g.chart.profile W) := by
  intro W
  induction W with
  | nil =>
    intro j hj
    have j0 : j ≠ 0 := by simpa using (ne_of_gt hj)
    change (1 : Polynomial ℝ).coeff j = 0
    simp [Polynomial.coeff_one, j0, j0.symm]
  | cons a W ih =>
    cases a
    · exact cert.primitiveBound W.length (g.chart.profile W) ih
    · exact cert.clockBound W.length (g.chart.profile W) ih

/-- At an actual site whose clock is c k, evaluate all old vectors and
their primitives using the shared quadratic frame. These equalities
also give one reverse head step when the reflected clock is used. -/
private theorem bind_anchor
    (M : MonomialBasis) (hM : standardPowers M)
    (R : Matrix (Fin 4) (Fin 4) ℝ) (c d : V ℝ) (k : Fin 4) (γ x : ℝ)
    (hx : x = c k)
    (a01 : c 0 ≠ c 1) (a02 : c 0 ≠ c 2) (a12 : c 1 ≠ c 2) (hp : pivot c d ≠ 0)
    (ha : LocalThree R c d k)
    (hClock : ∀ P : Polynomial ℝ,
      evalAt M x ((1 - Polynomial.X) * P) = (1 - x) * evalAt M x P) :
    AnchorSteps R (1 - c) (polyProject c d) (evalAt M x) (coefficientPrimitive M) ∧
    (∀ v, evalAt M x (polyProject c d v) = v k) ∧
    (∀ v, (mat R v) k - γ * v k =
      evalAt M x (coefficientPrimitive M (polyProject c d v)) -
        γ * evalAt M x (polyProject c d v)) := by
  subst x
  refine anchor_at_polynomials R c d k γ (evalAt M (c k))
    ((evalAt M (c k)).comp (coefficientPrimitive M)) (coefficientPrimitive M)
    a01 a02 a12 hp ha ?_ ?_ ?_ ?_ ?_ ?_ (fun _ => rfl) hClock
  · simpa only [pow_zero] using eval_pow M hM (c k) 0
  · simpa only [pow_one] using eval_pow M hM (c k) 1
  · exact eval_pow M hM (c k) 2
  · have h : evalAt M (c k) (coefficientPrimitive M (Polynomial.X ^ 0)) = c k := by
      rw [primitive_pow M hM 0, map_smul, eval_pow M hM]
      norm_num
    simpa only [pow_zero, LinearMap.comp_apply] using h
  · have h : evalAt M (c k) (coefficientPrimitive M (Polynomial.X ^ 1)) = (c k) ^ 2 / 2 := by
      rw [primitive_pow M hM 1, map_smul, eval_pow M hM]
      norm_num [smul_eq_mul] <;> ring
    simpa only [pow_one, LinearMap.comp_apply] using h
  · have h : evalAt M (c k) (coefficientPrimitive M (Polynomial.X ^ 2)) = (c k) ^ 3 / 3 := by
      rw [primitive_pow M hM 2, map_smul, eval_pow M hM]
      norm_num [smul_eq_mul] <;> ring
    simpa only [pow_one, LinearMap.comp_apply] using h

/-- The four small ideal polynomials in the reviewed rooted-tree model.
No enumerator or full order-eight test is imported. -/
private theorem low_and_top (g : Geometry ℝ) (c d : V ℝ)
    (hP : g.Projf = polyProject c d) (cert : ForwardLeaves g c d) :
    (∀ t, treeSize t ≤ 3 → g.F t = 0) ∧
    (∀ t, treeSize t = 4 → g.F t = g.Ex (g.F t) 4 • g.HF 0 + g.Ex (g.F t) 5 • g.HF 1) := by
  obtain ⟨p1,p2,p3a,p3b⟩ := ForwardChart.project_reviewed_four_columns g.G c d
    cert.distinct01 cert.distinct02 cert.distinct12 cert.pivotNe cert.sum cert.moment
  refine tree_gates_of_small_shapes (fun t => g.F t = 0)
    (fun t => g.F t = g.Ex (g.F t) 4 • g.HF 0 + g.Ex (g.F t) 5 • g.HF 1)
    ?_ ?_ ?_ ?_ cert.topA cert.topB cert.topC cert.topD cert.topE
  · change ideal t1 - g.Projf (Φ t1 g.G) = 0
    rw [hP, p1]
    norm_num [ideal, t1, forestNat, treeGrade, treeSize, FiniteRootedTree.forestFactorial,
      FiniteRootedTree.factorial, FiniteRootedTree.order]
  · change ideal t2 - g.Projf (Φ t2 g.G) = 0
    rw [hP, p2]
    norm_num [ideal, t2, t1, forestNat, treeGrade, treeSize, FiniteRootedTree.forestFactorial,
      FiniteRootedTree.factorial, FiniteRootedTree.order]
  · change ideal t3a - g.Projf (Φ t3a g.G) = 0
    rw [hP, p3a]
    norm_num [ideal, t3a, t2, t1, forestNat, treeGrade, treeSize, FiniteRootedTree.forestFactorial,
      FiniteRootedTree.factorial, FiniteRootedTree.order]
  · change ideal t3b - g.Projf (Φ t3b g.G) = 0
    rw [hP, p3b]
    norm_num [ideal, t3b, t2, t1, forestNat, treeGrade, treeSize, FiniteRootedTree.forestFactorial,
      FiniteRootedTree.factorial, FiniteRootedTree.order]

private theorem seed_bound (g : Geometry ℝ) (c d : V ℝ)
    (hp : g.Projf = polyProject c d) (hLow : ∀ t, treeSize t ≤ 3 → g.F t = 0) :
    ∀ t, PolyBound (treeGrade t) (g.F t) := by
  intro t j hj
  by_cases hn : 2 ≤ treeGrade t
  · have hq := project_bound c d (Φ t g.G) j (by omega)
    have hk : j ≠ treeGrade t := by omega
    change (ideal t - g.Projf (Φ t g.G)).coeff j = 0
    rw [hp, Polynomial.coeff_sub, hq, sub_zero]
    simp [ideal, Polynomial.coeff_X_pow, hk, hk.symm]
  · have hs : treeSize t ≤ 3 := by
      change ¬ 2 ≤ treeSize t - 1 at hn
      omega
    rw [hLow t hs, Polynomial.coeff_zero]

/-- Proof consumer for the literal audited endpoint. Its leaf certificate
is an explicit argument, not smuggled into ExactScalarSeed. -/
theorem literal_fin11_of_leaf_certificates
    (M : MonomialBasis) (hM : standardPowers M)
    (e : (Fin 4 ⊕ Fin 8) ≃ Fin 12) (he : orderedBlocks e)
    (s t cStar : ℝ) (hseed : ExactScalarSeed M s t cStar)
    (cert : LeafCertificates M s t cStar) :
    LiteralStrictOrder8 M s t cStar e := by
  let g := geometry M s t cStar
  let cr := reverseClock s t
  let dr := reverseG s
  let cf := forwardClock M s t cStar
  let df := forwardG M s t cStar
  let a : ScalarLeaves g := cert.scalar
  let f : ForwardLeaves g cf df := cert.forward
  let r : ReverseLeaves g cr dr := cert.reverse
  have hPr : g.Projr = polyProject cr dr := rfl
  have hPf : g.Projf = polyProject cf df := rfl
  have hγ : 0 < g.γ := by
    change 0 < (zAt s)⁻¹
    apply inv_pos.mpr
    unfold zAt aAt
    have hs := hseed.sLower
    linarith
  have hxX : g.Ex Polynomial.X = xAt M s t cStar := evalSites_X M hM _
  have hyX : g.Ey Polynomial.X = yAt M s t cStar := evalSites_X M hM _
  have evalX : ∀ n, g.Ex (Polynomial.X ^ n) = (g.Ex Polynomial.X) ^ n := by
    intro n
    rw [hxX]
    exact evalSites_pow M hM _ n
  have primX : ∀ n : ℕ, g.I (Polynomial.X ^ n) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • Polynomial.X ^ (n + 1) := primitive_pow M hM
  have eyOne : g.Ey 1 = 1 := by
    change evalSites M (yAt M s t cStar) (1 : Polynomial ℝ) = (1 : V6 ℝ)
    have h := evalSites_pow M hM (yAt M s t cStar) 0
    simpa only [pow_zero] using h
  have i0 : g.I 1 = Polynomial.X := by
    simpa only [pow_zero, pow_one, zero_add, Nat.cast_one, inv_one, one_smul] using primX 0
  have i1 : g.I Polynomial.X = (2 : ℝ)⁻¹ • Polynomial.X ^ 2 := by
    have h := primX 1
    norm_num [pow_one] at h ⊢
    exact h
  obtain ⟨pd,pI⟩ := g.ideal_bindings evalX primX
  obtain ⟨hLow,hF⟩ := low_and_top g cf df hPf f
  have hProf := profile_bound g a
  have hLift : ∀ v : V8 ℝ, g.chart.projectOld v = g.Projr (v ∘ oldIx) := fun _ => rfl
  have hOld : ∀ W : List Letter, g.chart.revDefect g.ξ W =
      g.chart.profile W - g.Projr (wordMap g.R (1 - cr) W 1) :=
    reverse_defect_restrict g.chart g.ξ g.R cr g.Projr oldIx
      (rev_restrict g.R g.U) r.reflectedSites hLift
  have rFrame := ForwardChart.polyProject_frame cr dr r.distinct01 r.distinct02 r.distinct12 r.pivotNe
  have hShort : ∀ W : List Letter, W.length ≤ 2 →
      g.chart.profile W = g.Projr (wordMap g.R (1 - cr) W 1) := by
    rw [hPr]
    exact old_profile_eq_through_two g.chart g.R cr dr (polyProject cr dr)
      r.sum r.moment rFrame.1 rFrame.2.1 rFrame.2.2.1 rFrame.2.2.2 i0 i1
  have evalAtReverse (k : Fin 4) (hx : g.Ey Polynomial.X (reverseSite k) = cr k)
      (P : Polynomial ℝ) : g.Ey P (reverseSite k) = evalAt M (cr k) P := by
    rw [hyX] at hx
    change evalAt M (yAt M s t cStar (reverseSite k)) P = evalAt M (cr k) P
    rw [hx]
  have reverseAnchor (k : Fin 4) (ha : LocalThree g.R cr dr k)
      (hx : g.Ey Polynomial.X (reverseSite k) = cr k) :
      AnchorSteps g.R (1 - cr) g.Projr (evalAt M (cr k)) g.I ∧
      (∀ v, g.Ey (g.Projr v) (reverseSite k) = v k) ∧
      (∀ v, g.Ey (g.I (g.Projr v)) (reverseSite k) = (g.R *ᵥ v) k) := by
    have hX : g.Ex Polynomial.X (reverseSite k) = 1 - cr k := by
      rw [hxX]
      change 1 - yAt M s t cStar (reverseSite k) = 1 - cr k
      rw [← hyX, hx]
    have reflected (P : Polynomial ℝ) :
        evalAt M (cr k) ((1 - Polynomial.X) * P) = (1 - cr k) * evalAt M (cr k) P := by
      have h := congrArg (fun z : V6 ℝ => z (reverseSite k)) (a.clock P)
      change g.Ey ((1 - Polynomial.X) * P) (reverseSite k) =
        g.Ex Polynomial.X (reverseSite k) * g.Ey P (reverseSite k) at h
      simpa only [evalAtReverse k hx, hX] using h
    obtain ⟨step,evAt,act⟩ := bind_anchor M hM g.R cr dr k g.γ (cr k) rfl
      r.distinct01 r.distinct02 r.distinct12 r.pivotNe ha reflected
    refine ⟨?_,?_,?_⟩
    · rw [hPr]
      exact step
    · intro v
      rw [evalAtReverse k hx, hPr]
      exact evAt v
    · intro v
      rw [evalAtReverse k hx, hPr]
      have hh := act v
      rw [evAt v] at hh
      change evalAt M (cr k) (coefficientPrimitive M (polyProject cr dr v)) = (mat g.R v) k
      exact (sub_left_inj.mp hh).symm
  obtain ⟨step2,e2,ir2⟩ := reverseAnchor 2 r.anchor2 r.evalClock2
  obtain ⟨step3,e3,ir3⟩ := reverseAnchor 3 r.anchor3 r.evalClock3
  have revCard (P : Polynomial ℝ) (hb : PolyBound 3 P)
      (h2 : evalAt M (cr 2) P = 0) (h3 : evalAt M (cr 3) P = 0) :
      P = g.Ey P 0 • g.KR 0 + g.Ey P 4 • g.KR 1 :=
    r.cubicCardinal P hb ((evalAtReverse 2 r.evalClock2 P).trans h2)
      ((evalAtReverse 3 r.evalClock3 P).trans h3)
  have hR := reverse_top_of_anchors g.chart g.ξ g.R cr g.Projr
    (evalAt M (cr 2)) (evalAt M (cr 3)) (g.KR 0) (g.KR 1)
    hOld hShort step2 step3 hProf (fun v => by rw [hPr]; exact project_bound cr dr v) revCard
  have law := g.make_laws a.mass e2 e3 ir2 ir3 eyOne a.clock pd pI
    (reverse_short_of_restrict g.chart g.ξ g.R cr g.Projr hOld hShort)
    hLow (seed_bound g cf df hPf hLow) hProf a.green
  have h8 := g.emitted_order a.mass a.quadrature law hF hR 1 1 0
    one_ne_zero one_ne_zero (by rw [a.missingCell, mul_zero]) rfl
  obtain ⟨hTL,hTD⟩ := g.suffix_shape a.mass r.lower r.diagonal
  have hAnchor (v : V ℝ) :
      (g.G *ᵥ v) 2 - g.γ * v 2 =
        g.Ex (g.I (g.Projf v)) 1 - g.γ * g.Ex (g.Projf v) 1 := by
    let eval : Polynomial ℝ →ₗ[ℝ] ℝ := evalAt M (cf 2)
    have hx : xAt M s t cStar 1 = cf 2 := by rw [← hxX]; exact f.evalClock1
    have eF (P : Polynomial ℝ) : g.Ex P 1 = eval P := by
      change evalAt M (xAt M s t cStar 1) P = evalAt M (cf 2) P
      rw [hx]
    have e0 : eval 1 = 1 := by
      simpa only [eval,pow_zero] using eval_pow M hM (cf 2) 0
    have e1 : eval Polynomial.X = cf 2 := by
      simpa only [eval,pow_one] using eval_pow M hM (cf 2) 1
    have e2 : eval (Polynomial.X ^ 2) = (cf 2) ^ 2 := eval_pow M hM (cf 2) 2
    let primEval := eval.comp g.I
    have p0 : primEval 1 = cf 2 := by
      change eval (g.I 1) = _
      rw [i0,e1]
    have p1 : primEval Polynomial.X = (cf 2) ^ 2 / 2 := by
      change eval (g.I Polynomial.X) = _
      rw [i1,map_smul,e2]
      ring
    have p2 : primEval (Polynomial.X ^ 2) = (cf 2) ^ 3 / 3 := by
      change eval (g.I (Polynomial.X ^ 2)) = _
      rw [primX, map_smul]
      change ((3 : ℝ)⁻¹) * evalAt M (cf 2) (Polynomial.X ^ 3) = _
      rw [eval_pow M hM]
      ring
    let row := (coordinate (2 : Fin 4)).comp (mat g.G)
    have heval := ForwardChart.evaluate_toPoly eval (cf 2) e0 e1 e2
      (ForwardChart.project cf df v)
    have hprim := ForwardChart.primitive_evaluate_toPoly primEval (cf 2) p0 p1 p2
      (ForwardChart.project cf df v)
    have h := ForwardChart.corrected_anchor_all_vectors cf df v row g.γ
      f.distinct01 f.distinct02 f.distinct12 f.pivotNe f.anchor2.defectZero
      f.anchor2.row0 f.anchor2.row1 f.anchor2.row2 f.anchor2.rowDefect
    rw [← heval, ← hprim] at h
    simp only [eF, hPf]
    exact h
  obtain ⟨lower,diag,_strict,ord⟩ :=
    g.finish_fin11 e he.1 he.2 hγ.ne' f.lower f.diagonal hTL hTD hAnchor h8
  exact ⟨hγ,lower,diag,ord⟩

/-- The outstanding job has precisely this type. In particular it only
uses a symbolic seed and does not assert existence of one. -/
def LeafProducer : Prop :=
  ∀ (M : MonomialBasis), standardPowers M →
    ∀ (s t cStar : ℝ), ExactScalarSeed M s t cStar → LeafCertificates M s t cStar

theorem conditionalTarget_of_leafProducer (produce : LeafProducer) : ConditionalTarget := by
  intro M hm e he s t cStar hs
  exact literal_fin11_of_leaf_certificates M hm e he s t cStar hs (produce M hm s t cStar hs)

end RKResearch.Certified.PaidDefectBridge.SDIRK118.ConditionalFin11
