module

public import RKCert.ReviewedNative.LocalLinearRefinedCensus
public import RKCert.ReviewedNative.WeightedClockPaidAdvance

@[expose] public section

/-! # Whole-clock silent extra directions

A supported additional signed mode, orthogonal to the early core and
with zero mass in each original block, charges one more dimension if
it is outside the ordinary weighted clock orbit. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {y f e τ W v w : Fin s → K} {Q : K[X]} {U J : Submodule K (Fin s → K)}

theorem clockMass_of_clock_multiple (g : K → K) (a : K)
    (form : ∀ i, v i = g (y i) * w i) :
    clockMass y v a = g a * clockMass y w a := by
  simp only [clockMass, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases e : y i = a <;> simp [e, form i]

theorem clockMass_at_local_mode (a : K) (off : ∀ i, y i ≠ a → v i = 0) :
    clockMass y v a = ∑ i, v i := by
  simp only [clockMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : y i = a <;> simp [hit, off]

theorem clockMass_zero_of_local_total (a : K)
    (off : ∀ i, y i ≠ a → v i = 0) (total : (∑ i, v i) = 0) :
    ∀ x, clockMass y v x = 0 := by
  intro x
  by_cases eq : x = a
  · rw [eq, clockMass_at_local_mode a off, total]
  · apply clockMass_zero_of_not_site
    intro xsite
    obtain ⟨i,vi,ix⟩ := mem_weightedSites.mp xsite
    exact vi (off i (fun ia => eq (ix.symm.trans ia)))

private theorem tauSelector_sum (T : Finset K) :
    tauSelector y f e Q T =
      ∑ a ∈ T, (labelIndicator (tripleLabel y f e) (a,Q.eval a,0) : Fin s → K) := by
  ext i
  rw [Finset.sum_apply]
  by_cases on : tripleLabel y f e i ∈ tauLabels Q T
  · have iy : y i ∈ T := on.2.2
    have eq : tripleLabel y f e i = (y i,Q.eval (y i),0) :=
      Prod.ext rfl (Prod.ext on.2.1 on.1)
    rw [Finset.sum_eq_single_of_mem (y i) iy]
    · have on' : (y i, Q.eval (y i), 0) ∈ tauLabels Q T := eq ▸ on
      simp [labelIndicator, tauSelector, eq, on']
    · intro a _ ne
      have none : tripleLabel y f e i ≠ (a,Q.eval a,0) :=
        fun eq => ne (congrArg Prod.fst eq).symm
      simp [labelIndicator,none]
  · rw [show tauSelector y f e Q T i = 0 by simp [tauSelector,on]]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have none : tripleLabel y f e i ≠ (a,Q.eval a,0) := by
      intro eq
      exact on (eq.symm ▸ (show (a,Q.eval a,0) ∈ tauLabels Q T from ⟨rfl,rfl,ha⟩))
    simp [labelIndicator,none]

private theorem tauSelector_rank (C : JointBandCensus y f e τ W Q U J) :
    (weightedSites y (tauSelector y f e Q (weightedSites y τ))).card =
      (weightedSites y τ).card := by
  congr 1
  ext a
  constructor
  · intro h
    obtain ⟨i,vi,rfl⟩ := mem_weightedSites.mp h
    have on : tripleLabel y f e i ∈ tauLabels Q (weightedSites y τ) := by
      by_contra no
      exact vi (by simp [tauSelector,no])
    exact on.2.2
  · intro h
    obtain ⟨i,ti,eq⟩ := mem_weightedSites.mp h
    have on : tripleLabel y f e i ∈ tauLabels Q (weightedSites y τ) :=
      ⟨(C.tauRows i ti).1,(C.tauRows i ti).2,mem_weightedSites.mpr ⟨i,ti,rfl⟩⟩
    exact mem_weightedSites.mpr ⟨i,by simp [tauSelector,on],eq⟩

private theorem tauSelector_orbit_on (T : Finset K) :
    OnLabels (tripleLabel y f e) (tauLabels Q T)
      (completeOrbit y (tauSelector y f e Q T)) := by
  rintro _ ⟨P,rfl⟩ i off
  simp [weightedEval_apply,tauSelector,off]

private theorem silent_annih_selector {T : Finset K}
    (live : ∀ i, v i ≠ 0 → tripleLabel y f e i ∈ tauLabels Q T)
    (mass : ∀ a, clockMass y v a = 0) :
    v ∈ annih (completeOrbit y (tauSelector y f e Q T)) := by
  apply mem_annih.mpr
  rintro _ ⟨P,rfl⟩
  have rowFit : row v (weightedEval y (tauSelector y f e Q T) P) =
      ∑ i, v i * P.eval (y i) := by
    rw [row_apply,dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    by_cases zero : v i = 0
    · simp [zero]
    · have on := live i zero
      simp [weightedEval_apply,tauSelector,on]
  rw [rowFit,weighted_sum_by_clock y v P.eval]
  exact Finset.sum_eq_zero (fun a _ => by rw [mass a,zero_mul])

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- A genuinely new local mode silent on the old macro blocks lies
outside both the independent unweighted indicators and the old weighted
τ orbit. Only the literal block masses enter that independence. -/
theorem JointBandCensus.cancelled_rank_with_silent_extra
    (C : JointBandCensus y f e τ W Q U J)
    (mass : ∀ a, clockMass y τ a = 0)
    (extraIn : v ∈ annih U)
    (extraOn : ∀ i, v i ≠ 0 → tripleLabel y f e i ∈ tauLabels Q (weightedSites y τ))
    (extraMass : ∀ a, clockMass y v a = 0)
    (extraOut : v ∉ completeOrbit y τ) :
    finrank K U + finrank K J + 2*(weightedSites y τ).card + 1 +
      (weightedSites y W).card ≤ s := by
  let T := weightedSites y τ
  let O := completeOrbit y τ
  let X := Submodule.span K {v}
  let I := completeOrbit y (tauSelector y f e Q T)
  have Iorth : I ≤ annih U := by
    apply completeOrbit_annih C.clockStable
    rw [tauSelector_sum]
    exact (annih U).sum_mem (fun a _ => C.indicator _)
  have OI : O ≤ annih I := by
    rintro _ ⟨P,rfl⟩
    apply silent_annih_selector
    · intro i li
      by_cases ti : τ i = 0
      · exact (li (by simp [weightedEval_apply,ti])).elim
      exact ⟨(C.tauRows i ti).1,(C.tauRows i ti).2,mem_weightedSites.mpr ⟨i,ti,rfl⟩⟩
    · intro a
      rw [clockMass_of_clock_multiple P.eval a (fun i => weightedEval_apply _ _ _ _), mass a, mul_zero]
  have XI : X ≤ annih I := (Submodule.span_singleton_le_iff_mem _ _).mpr
    (silent_annih_selector extraOn extraMass)
  have XU : X ≤ annih U := (Submodule.span_singleton_le_iff_mem _ _).mpr extraIn
  have dis : (O ⊔ X) ⊓ I = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    rw [eq_zero_of_self_row_zero (mem_annih.mp (sup_le OI XI hz.1) _ hz.2)]
    exact (⊥ : Submodule K (Fin s → K)).zero_mem
  have idim : finrank K I = T.card :=
    (completeOrbit_rank _ _).trans (tauSelector_rank C)
  have odim : finrank K (O ⊔ X : Submodule K (Fin s → K)) = T.card + 1 :=
    (Submodule.finrank_sup_span_singleton extraOut).trans
      (congrArg (·+1) (completeOrbit_rank _ _))
  have d := Submodule.finrank_sup_add_finrank_inf_eq (O ⊔ X) I
  rw [dis,finrank_bot,add_zero,odim,idim] at d
  have Xon : OnLabels (tripleLabel y f e) (tauLabels Q T) X := by
    intro x hx i off
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    have vz : v i = 0 := by by_contra vi; exact off (extraOn i vi)
    simp [Pi.smul_apply,vz]
  have headOn : OnLabels (tripleLabel y f e) (tauLabels Q T) (O ⊔ X ⊔ I) :=
    onLabels_same_sup (onLabels_same_sup C.tau_on Xon) (tauSelector_orbit_on T)
  have headOrth : O ⊔ X ⊔ I ≤ annih U :=
    sup_le (sup_le (completeOrbit_annih C.clockStable C.tauOrth) XU) Iorth
  have separate : Disjoint coreLabels (tauLabels Q T) ∧
      Disjoint coreLabels (contrastLabels Q (weightedSites y W)) ∧
      Disjoint (tauLabels Q T) (contrastLabels Q (weightedSites y W)) := by
    refine ⟨Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_⟩
    · intro a aa bb
      exact one_ne_zero (aa.symm.trans bb.1)
    · intro a aa bb
      exact one_ne_zero (aa.symm.trans bb.1)
    · intro a aa bb
      exact bb.2.2.1 (aa.2.1.symm.trans bb.2.1)
  obtain ⟨st,sr,tr⟩ := separate
  have dim := finrank_supported_triple C.core_on headOn C.contrast_on st sr tr
  have upper := Submodule.finrank_mono (sup_le (sup_le C.coreOrth headOrth)
    (completeOrbit_annih C.clockStable C.contrastOrth))
  rw [dim,d,completeOrbit_rank] at upper
  have all := finrank_annih U
  rw [Fintype.card_fin] at all
  change finrank K U + finrank K J + 2*T.card + 1 + (weightedSites y W).card ≤ s
  omega

end
end RKResearch.Certified.Graded.Reverse.LocalLinear
