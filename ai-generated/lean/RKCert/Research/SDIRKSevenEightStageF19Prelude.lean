module
public import RKCert.Research.SDIRKSevenEightStageF19Arithmetic
public import RKCert.Research.SDIRKSevenEightStageGhostExclusion

@[expose] public section

/-! # Reviewed-tree ingress for the characteristic-19 profile gates

The mask and both moment laws are derived from the real reviewed order
predicate. The two-ended normalization and causal moment interface are
kept separate from these native results.
-/

namespace RKResearch.Certified.SDIRKSeven.F19
open RKResearch Graded Graded.SDIRKSeven
open scoped BigOperators Matrix

private theorem square_two_check : ∀ x : Fin 19,(x.val:K)*(x.val:K)≠2 := by
  decide +kernel

private theorem cubic_check :
    ∀ x : Fin 19,(x.val:K)^3-9*(x.val:K)^2+18*(x.val:K)-6≠0 := by
  decide +kernel

private theorem no_square_two : ¬ IsSquare (2:K) := by
  rintro ⟨u,e⟩
  let v : Fin 19 := ⟨u.val,u.val_lt⟩
  have hv : (v.val:K)=u := by
    change (u.val:K)=u
    exact ZMod.natCast_zmod_val u
  apply square_two_check v
  rw [hv]
  exact e.symm

private theorem no_cubic (u : K) : u^3-9*u^2+18*u-6≠0 := by
  let v : Fin 19 := ⟨u.val,u.val_lt⟩
  have hv : (v.val:K)=u := by
    change (u.val:K)=u
    exact ZMod.natCast_zmod_val u
  simpa only [hv] using cubic_check v

theorem actual_mask {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8→K} {γ : K}
    (ho : HasOrder 7 A b) (ha : A.IsLowerTriangular) (he : ∀i,A i i=γ) (hγ : γ≠0) :
    mask b := by
  by_cases h : ∀ i,b i≠0
  · exact Or.inl h
  · push Not at h
    obtain ⟨i,hi⟩ := h
    have positive : 0<(ghostSet b).card := Finset.card_pos.mpr ⟨i,mem_ghostSet.mpr hi⟩
    have hh := cubic_hidden_of_ghost_no_sqrt_two ho ha he hγ no_square_two positive
    obtain ⟨hb₀,hb₁⟩ := both_front_ghosts_of_cubic_hidden ho ha he hγ hh
    refine Or.inr ⟨hb₀,hb₁,?_⟩
    by_contra hb₂
    have pure (v : Fin 8→K) (hv : v∈zeroSpace A 3) :
        v 2=0 := mem_ghostSpace.mp (hh hv) 2 hb₂
    exact no_cubic _ (pure_third_clock_laguerre ho ha he hγ pure)

theorem actual_quad {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8→K}
    (ho : HasOrder 7 A b) (z : K) :
    quadrature z (Graded.nodes (SDIRKSix.scaleTable z A)) b := by
  intro j
  have valid : j.val+1≤7 := j.isLt
  have h := ho.hasQuadratureOrder j.val valid
  have hv : (∑ i, b i*Graded.nodes A i^j.val)=1/((j.val+1:ℕ):K) := by
    apply (eq_div_iff (ho.natCast_isUnit (by omega : 0<j.val+1) valid).ne_zero).mpr
    simpa only [dotProduct,Pi.pow_apply,mul_comm] using h
  simp only [SDIRKSix.nodes_scaleTable,Pi.smul_apply,smul_eq_mul,mul_pow,mul_left_comm (b _),
    ←Finset.mul_sum,hv]
  ring

theorem actual_first_seed_moments {A : Matrix (Fin 8) (Fin 8) K} {b : Fin 8→K}
    (ho : HasOrder 7 A b) (z : K) (j : Fin 5) :
    (∑ i, b i*(Graded.nodes (SDIRKSix.scaleTable z A) i)^j.val*
      SDIRKSix.seed (SDIRKSix.scaleTable z A) i)=0 := by
  have pay : j.val+2+1≤7 := by have := j.isLt; omega
  have e := LinearMap.mem_ker.mp (probe_zeroSpace ho pay (SDIRKSix.seed_zero A))
  have ev : (∑ i, b i*(Graded.nodes A i)^j.val*SDIRKSix.seed A i)=0 := by
    simpa only [probe,row_apply,dotProduct] using e
  calc
    _ = (z^j.val*z^2)*∑ i,b i*(Graded.nodes A i)^j.val*SDIRKSix.seed A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [SDIRKSix.nodes_scaleTable,SDIRKSix.seed_scaleTable,
        Pi.smul_apply,smul_eq_mul,mul_pow]
      ring
    _ = 0 := by rw [ev,mul_zero]

end RKResearch.Certified.SDIRKSeven.F19
