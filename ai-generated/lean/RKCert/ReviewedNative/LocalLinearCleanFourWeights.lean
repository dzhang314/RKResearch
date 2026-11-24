module

public import RKCert.ReviewedNative.LocalLinearCleanFourForward
public import RKCert.ReviewedNative.PositiveIntervalGrid19

@[expose] public section

/-! # Paid compensated weight and block transpose on the original feed

The output and reverse residuals are earned from the original rows.
This neutral window requires a true E8 indicator, order at least 17,
and the degree-two reverse test. The right interval has unit base
weight; no factor 1-X enters the transpose formula. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.ReviewedNative.PositiveRule19
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b τ h W k θ : Fin s → K}
variable {U : Submodule K (Fin s → K)} {S Q : K[X]}

abbrev ordinaryProfile (P : K[X]) : K[X] := P.comp (1-X)

theorem ordinaryProfile_degree (P : K[X]) :
    (ordinaryProfile P).natDegree ≤ P.natDegree := by
  have d : (1-X : K[X]).natDegree ≤ 1 := (natDegree_sub_le 1 X).trans (by simp)
  exact natDegree_comp_le.trans ((Nat.mul_le_mul (le_refl _) d).trans_eq (Nat.mul_one _))

theorem ordinaryProfile_twice (P : K[X]) : ordinaryProfile (ordinaryProfile P) = P := by
  change (P.comp (1-X)).comp (1-X) = P
  rw [comp_assoc, show (1-X : K[X]).comp (1-X) = X by
    simp only [sub_comp, one_comp, X_comp]
    ring, comp_X]

theorem ordinaryProfile_eval_node (P : K[X]) (i : Fin s) :
    (ordinaryProfile P).eval (nodes A i) = P.eval (reflectedClock A i) := by
  simp only [ordinaryProfile, eval_comp, reflectedClock, eval_sub, eval_one, eval_X,
    Pi.sub_apply, Pi.one_apply]

theorem ordinaryProfile_eval_reflected (P : K[X]) (i : Fin s) :
    (ordinaryProfile P).eval (reflectedClock A i) = P.eval (nodes A i) := by
  rw [←ordinaryProfile_eval_node (A:=A) (ordinaryProfile P) i, ordinaryProfile_twice]

/-- Only the actual compensated weight and paid degrees are required.
The horizon and dimension of the eventual tableau are irrelevant. -/
structure UnitFourCompensated (A : Matrix (Fin s) (Fin s) K)
    (b τ W : Fin s → K) (U : Submodule K (Fin s → K)) (S Q : K[X]) : Prop where
  core : U ≤ primitiveBack A b 1
  stable : U.map (diag (reflectedClock A)) ≤ U
  tau : ∃ r, τ ∈ primitiveBack A b r ∧ (S = 0 ∨ r+S.natDegree ≤ 4)
  qDegree : Q.natDegree ≤ 5
  form : ∃ u ∈ U, W = weightedEval (reflectedClock A) b Q -
    weightedEval (reflectedClock A) τ S - u

theorem UnitFourCompensated.of_local_trace {j r : ℕ}
    (F : LocalLinearBand A b j r U τ) (T : LocalLinearTraces A b U τ h r 5 S Q)
    (comp : ∃ u ∈ U, W = weightedEval (reflectedClock A) b Q -
      weightedEval (reflectedClock A) τ S - u) :
    UnitFourCompensated A b τ W U S Q := by
  have rb : r ≤ 2 := by rcases F.coreRank with e | e <;> omega
  have mono : Monotone (primitiveBack A b) := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have sc : S = 0 ∨ r+S.natDegree ≤ 4 := by
    rcases T.pDeg with e | d
    · exact Or.inl e
    · exact Or.inr (by omega)
  exact ⟨F.core.le.trans (mono (by omega)), F.invariant, ⟨r, F.headMem, sc⟩, T.qDeg, comp⟩

/-- The degree-eleven signed moment on the original ordinary nodes.
The three terms use independent reviewed payments. -/
theorem UnitFourCompensated.moment_sum (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p) (R : K[X]) (rd : R.natDegree ≤ 11) :
    (∑ i, W i * R.eval (nodes A i)) = (primitive (R*ordinaryProfile Q)).eval 1 := by
  obtain ⟨u, hu, raw⟩ := B.form
  let c := nodes A
  let P := ordinaryProfile Q
  let T := R*ordinaryProfile S
  have dp : (R*P).natDegree ≤ 16 :=
    natDegree_mul_le_of_le rd ((ordinaryProfile_degree Q).trans B.qDegree)
  have btest : (∑ i, b i * (R*P).eval (c i)) = (primitive (R*P)).eval 1 := by
    have q := probe_evalNodes ho (R*P) 0 (by omega)
    simpa only [probe, row_apply, dotProduct, pow_zero, mul_one, evalNodes_apply, one_mul, c] using q
  have utest : (∑ i, u i * R.eval (c i)) = 0 := by
    have q := mem_annih.mp (primitiveBack_annih ho 11 1 (by omega) (B.core hu)) _
      (evalNodes_mem_treeSpace A R rd)
    simpa only [row_apply, dotProduct, evalNodes_apply, c] using q
  have ttest : (∑ i, τ i * T.eval (c i)) = 0 := by
    obtain ⟨r, hp, sd⟩ := B.tau
    rcases sd with sz | credit
    · simp [T, ordinaryProfile, sz]
    · have td : T.natDegree ≤ 15-r := by
        change (R*ordinaryProfile S).natDegree ≤ 15-r
        refine (natDegree_mul_le (p:=R) (q:=ordinaryProfile S)).trans ?_
        have sdeg := ordinaryProfile_degree S
        omega
      have w := mem_annih.mp (primitiveBack_annih ho (15-r) r (by omega) hp) _
        (evalNodes_mem_treeSpace A T td)
      simpa only [row_apply, dotProduct, evalNodes_apply, c] using w
  have expand : (∑ i, W i * R.eval (c i)) = (∑ i, b i * (R*P).eval (c i)) -
      (∑ i, τ i * T.eval (c i)) - (∑ i, u i * R.eval (c i)) := by
    rw [←Finset.sum_sub_distrib, ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [congrFun raw i]
    simp only [Pi.sub_apply, weightedEval_apply, P, T, c, eval_mul, ordinaryProfile_eval_node]
    ring
  rw [expand, btest, ttest, utest, sub_zero, sub_zero]

section CharZero
variable [CharZero K]

/-- The degree-two compensated transpose residual is literally in L7.
No full reverse flag equality and no reverse order conversion is used. -/
theorem UnitFourCompensated.reverse_residual (B : UnitFourCompensated A b τ W U S Q)
    (H : K[X]) (hd : H.natDegree ≤ 2) :
    mat A.transpose (weightedEval (reflectedClock A) W H) -
      weightedEval (reflectedClock A) b (primitive (H*Q)) ∈ primitiveBack A b 7 := by
  let y := reflectedClock A
  let L := primitiveBack A b
  obtain ⟨u, hu, raw⟩ := B.form
  have mono : Monotone L := monotone_nat_of_le_succ (adjointFlag_le_succ _)
  have ub : weightedEval y u H ∈ L 6 :=
    mono (show 1 ≤ 6 by decide) (B.core (reflected_clock_weighted_core B.stable hu H))
  have tb : weightedEval y τ (H*S) ∈ L 6 := by
    obtain ⟨r, hp, sd⟩ := B.tau
    rcases sd with sz | credit
    · simp [sz, L]
    · have bd : (H*S).natDegree ≤ 6-r := natDegree_mul_le.trans (by omega)
      have mem := weighted_primitive_band hp (H*S) bd
      rwa [show r+(6-r)=6 by omega] at mem
  have bb : mat A.transpose (weightedEval y b (H*Q)) -
      weightedEval y b (primitive (H*Q)) ∈ L 7 :=
    reverse_primitive_next 6 (H*Q) (natDegree_mul_le.trans (by have qd := B.qDegree; omega))
  have shifted {v : Fin s → K} (hv : v ∈ L 6) : mat A.transpose v ∈ L 7 :=
    adjointFlag_transpose _ 6 (Submodule.mem_map_of_mem hv)
  have eq := scaled_contrast_decomposition (M:=H) raw
  change weightedEval y W H = weightedEval y b (H*Q) -
    weightedEval y τ (H*S) - weightedEval y u H at eq
  rw [eq, map_sub, map_sub]
  convert (L 7).sub_mem ((L 7).sub_mem bb (shifted tb)) (shifted ub) using 1
  abel

/-- On a whole actual feed block, the compensation contributes no mass.
The early core is tested against the same E8 indicator as the transpose. -/
theorem UnitFourCompensated.block_mass_fit (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    {x : K} (paid : indicator (nodes A) θ x ∈ treeSpace A 8) :
    blockMass (nodes A) θ W x = (ordinaryProfile Q).eval x * blockMass (nodes A) θ b x := by
  obtain ⟨u, hu, raw⟩ := B.form
  let c := nodes A
  let χ := indicator c θ x
  have uz : row u χ = 0 :=
    mem_annih.mp (primitiveBack_annih ho 8 1 (by omega) (B.core hu)) _ paid
  have e : row W χ = (ordinaryProfile Q).eval x * row b χ - row u χ := by
    simp only [row_apply, dotProduct]
    rw [Finset.mul_sum, ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases on : θ i ≠ 0 ∧ c i = x
    · have off := G.tauOff i on.1
      have value : Q.eval (reflectedClock A i) = (ordinaryProfile Q).eval x :=
        (ordinaryProfile_eval_node (A:=A) Q i).symm.trans
          (congrArg (ordinaryProfile Q).eval on.2)
      rw [congrFun raw i]
      simp only [Pi.sub_apply, weightedEval_apply]
      change ((Q.eval (reflectedClock A i) * b i - S.eval (reflectedClock A i) * τ i - u i) * χ i) = _
      have i1 : χ i = 1 := if_pos on
      simp only [i1, value, off, mul_zero, sub_zero, mul_one]
    · simp [χ, indicator, on]
  change row W χ = (ordinaryProfile Q).eval x * row b χ
  rw [e, uz, sub_zero]

/-- Actual transpose sum over blocks at the first-appearance chronology.
The right moment is I(x,1;R P), with unit weight. -/
theorem UnitFourCompensated.transpose_block_moment (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ) (R : K[X]) (rd : R.natDegree ≤ 2) :
    (∑ z ∈ weightedSites (nodes A) θ, blockMass (nodes A) θ W z *
      (R.eval z * coefficient A θ (ordinaryProfile Q) z x)) =
      blockMass (nodes A) θ b x * integral x 1 (R*ordinaryProfile Q) := by
  let c := nodes A
  let y := reflectedClock A
  let P := ordinaryProfile Q
  let H := ordinaryProfile R
  let χ := indicator c θ x
  have hd : H.natDegree ≤ 2 := (ordinaryProfile_degree R).trans rd
  have mem := B.reverse_residual H hd
  have paid := indicator_paid ho pay G inside stable hx
  have zero := mem_annih.mp (primitiveBack_annih ho 8 7 (by omega) mem) _ paid
  change row (mat A.transpose (weightedEval y W H) -
      weightedEval y b (primitive (H*Q))) χ = 0 at zero
  have balance : row (mat A.transpose (weightedEval y W H)) χ =
      row (weightedEval y b (primitive (H*Q))) χ :=
    sub_eq_zero.mp (by simpa only [row_apply, dotProduct, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib] using zero)
  rw [row_mat_transpose] at balance
  have sumL : row (weightedEval y W H) (mat A χ) =
      ∑ z ∈ weightedSites c θ, blockMass c θ W z * (R.eval z * coefficient A θ P z x) := by
    rw [←sum_by_feed_clock c θ W (fun i wi => (G.support i).mpr wi)
      (fun z => R.eval z * coefficient A θ P z x)]
    simp only [row_apply, dotProduct, weightedEval_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases wi : W i = 0
    · simp [wi]
    · have live := (G.support i).mpr wi
      have ce : mat A χ i = coefficient A θ P (c i) x := coefficient_eval ho pay G inside stable hx live
      have he : H.eval (y i) = R.eval (c i) := ordinaryProfile_eval_reflected (A:=A) R i
      rw [ce, he]
      ring
  have hp : H*Q = ordinaryProfile (R*P) := by
    change H*Q = (R*P).comp (1-X)
    rw [mul_comp]
    change H*Q = H*ordinaryProfile (ordinaryProfile Q)
    rw [ordinaryProfile_twice]
  have ev (i : Fin s) : (primitive (H*Q)).eval (y i) = integral (c i) 1 (R*P) := by
    rw [hp, ←formalPrimitive_eq_native, ←integral_zero_left]
    change integral 0 (1-c i) ((R*P).comp (1-X)) = integral (c i) 1 (R*P)
    exact integral_reflect _ _
  have sumR : row (weightedEval y b (primitive (H*Q))) χ =
      blockMass c θ b x * integral x 1 (R*P) := by
    simp only [blockMass, row_apply, dotProduct, weightedEval_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases on : θ i ≠ 0 ∧ c i = x
    · have i1 : χ i = 1 := by simp [χ, indicator, on]
      change _ * χ i = b i * χ i * _
      rw [ev i, on.2, i1]
      ring
    · have i0 : χ i = 0 := by simp [χ, indicator, on]
      change _ * χ i = b i * χ i * _
      simp [i0]
  exact sumL.symm.trans (balance.trans sumR)

/-- A paid reverse multiplier that kills later blocks earns its right
window at the original clock, once the whole output block mass is live. -/
theorem UnitFourCompensated.reverse_mask_zero (B : UnitFourCompensated A b τ W U S Q)
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (inside : hiddenKernel b τ U ≤ zeroSpace A 8)
    (stable : (hiddenKernel b τ U).map (diag (nodes A)) ≤ hiddenKernel b τ U)
    {x : K} (hx : x ∈ weightedSites (nodes A) θ)
    (mass : blockMass (nodes A) θ b x ≠ 0) (R : K[X]) (rd : R.natDegree ≤ 2)
    (filter : ∀ z, ∀ hz : z ∈ weightedSites (nodes A) θ,
      firstRow (nodes A) θ x hx < firstRow (nodes A) θ z hz → R.eval z = 0) :
    integral x 1 (R*ordinaryProfile Q) = 0 := by
  have eq := B.transpose_block_moment ho pay G inside stable hx R rd
  have z0 : (∑ z ∈ weightedSites (nodes A) θ, blockMass (nodes A) θ W z *
      (R.eval z * coefficient A θ (ordinaryProfile Q) z x)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    by_cases later : firstRow (nodes A) θ x hx < firstRow (nodes A) θ z hz
    · rw [filter z hz later, zero_mul, mul_zero]
    · rw [coefficient_eq_zero_before ha ho pay G inside stable hz hx (le_of_not_gt later),
        mul_zero, mul_zero]
  rw [z0] at eq
  exact (mul_eq_zero.mp eq.symm).resolve_left mass

/-- Forward-degree eleven pays the degree-four nodal hull times every
degree-seven test. This assertion is about the true feed support. -/
theorem UnitFourCompensated.hull_moment (B : UnitFourCompensated A b τ W U S Q)
    (ho : HasOrder p A b) (pay : 17 ≤ p)
    (G : UnitCleanFourFeed A b τ h W k θ U (ordinaryProfile Q))
    (R : K[X]) (rd : R.natDegree ≤ 7) :
    integral 0 1 ((nodalHull (weightedSites (nodes A) θ)*R)*ordinaryProfile Q) = 0 := by
  let D := weightedSites (nodes A) θ
  let N := nodalHull D
  have nd : N.natDegree = 4 := (natDegree_nodalHull D).trans G.sites
  have nr : (N*R).natDegree ≤ 11 := natDegree_mul_le_of_le nd.le rd
  have g := B.moment_sum ho pay (N*R) nr
  have z : (∑ i, W i * (N*R).eval (nodes A i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases wi : W i = 0
    · rw [wi, zero_mul]
    · have on : nodes A i ∈ D := mem_weightedSites.mpr ⟨i, (G.support i).mpr wi, rfl⟩
      simp only [N, eval_mul, nodalHull_eval_of_mem on, zero_mul, mul_zero]
  rw [z] at g
  rw [integral_zero_left, formalPrimitive_eq_native]
  exact g.symm

end CharZero

end
end RKResearch.Certified.Graded.Reverse.LocalLinear.CleanFour
