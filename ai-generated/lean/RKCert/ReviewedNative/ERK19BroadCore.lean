module

public import RKCert.ReviewedNative.ERK19TraceAlgebra

@[expose] public section

/-! # The actual jointly inactive coordinates are the stable core -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

def jointInactive (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K) :
    Submodule K (Fin 29→K) := (diag (firstSeed A b)).ker ⊓ (diag b).ker

theorem mem_jointInactive {v : Fin 29→K} :
    v∈jointInactive A b ↔
      (∀i, firstSeed A b i≠0 → v i=0) ∧ (∀i, b i≠0 → v i=0) := by
  change v∈(diag (firstSeed A b)).ker ⊓ (diag b).ker ↔ _
  rw [Submodule.mem_inf]
  have e (d : Fin 29→K) : v∈(diag d).ker ↔ ∀ i,d i≠0 → v i=0 := by
    constructor
    · intro h i di
      have a : d i*v i=0 := congrFun (LinearMap.mem_ker.mp h) i
      exact (mul_eq_zero.mp a).resolve_left di
    · intro h
      apply LinearMap.mem_ker.mpr
      ext i
      change d i*v i=0
      by_cases di : d i=0
      · rw [di,zero_mul]
      · rw [h i di,mul_zero]
  rw [e,e]

theorem jointInactive_stable : (jointInactive A b).map (diag (nodes A)) ≤ jointInactive A b := by
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨d,w⟩ := mem_jointInactive.mp hv
  apply mem_jointInactive.mpr
  exact ⟨fun i h=>by rw [diag_apply,d i h,mul_zero],
    fun i h=>by rw [diag_apply,w i h,mul_zero]⟩

theorem jointInactive_le_nine (ho : HasOrder 19 A b) (band : FullFirstBand A b) :
    jointInactive A b ≤ zeroSpace A 9 := by
  intro v hv
  obtain ⟨zd,zb⟩ := mem_jointInactive.mp hv
  have a : v∈annih (annih (treeSpace A 9)) := by
    apply mem_annih.mpr
    intro w hw
    obtain ⟨P,rfl⟩ := band.represent hw
    rw [row_apply,dotProduct]
    apply Finset.sum_eq_zero
    intro i _
    by_cases di : firstSeed A b i=0
    · rw [weightedEval_apply,di,mul_zero,mul_zero]
    · rw [zd i di,zero_mul]
  rw [annih_annih] at a
  apply eval_alias_from_full_probes ho (by decide) a
  intro k
  change (∑ i,(b i*(nodes A i)^k.val)*v i)=0
  apply Finset.sum_eq_zero
  intro i _
  by_cases bi : b i=0
  · rw [bi,zero_mul,zero_mul]
  · rw [zb i bi,mul_zero]

/-- The large-circle support makes the true joint zero-coordinate
submodule exactly the maximal clock-invariant part of the one-head band. -/
theorem broad_core_eq_jointInactive (ho : HasOrder 19 A b) (B : FullFirstBand A b)
    (wide : 19≤(weightedSites (nodes A) (firstSeed A b)).card)
    {r : ℕ} {U : Submodule K (Fin 29→K)} {w : Fin 29→K}
    (H : FlatClockHead A 8 1 r U w) : U=jointInactive A b := by
  have F9 : zeroSpace A 9=chain (diag (nodes A)) U w (r+1) := H.flags 1 (by decide)
  apply le_antisymm
  · intro x hx
    have xF := H.coreInside hx
    obtain ⟨P,dP,proj⟩ := original_first_degree_eight_trace ho B (zeroSpace_le_treeSpace A 8 xF)
    have pz : P=0 := by
      by_contra nz
      have shifted := H.coreInside (clock_pow_mem_invariant H.coreStable hx 9)
      have debt := trace_degree_from_paid_shift ho B wide nz dP proj (by decide) shifted
      omega
    rw [pz,map_zero] at proj
    have d (i : Fin 29) (live : firstSeed A b i≠0) : x i=0 := by
      have e : firstSeed A b i*x i=0 := (congrFun proj i).symm
      exact (mul_eq_zero.mp e).resolve_left live
    refine mem_jointInactive.mpr ⟨d,fun i bi=>?_⟩
    by_cases di : firstSeed A b i=0
    · exact clean_of_off_seed_live ho (by decide) B i di bi x xF
    · exact d i di
  · intro x hx
    obtain ⟨dx,bx⟩ := mem_jointInactive.mp hx
    let δ (i : Fin 29) := x i • coordinate (K:=K) i
    have δval (i j : Fin 29) : δ i j=if j=i then x i else 0 := by
      by_cases h : j=i
      · subst j
        simp [δ,coordinate]
      · simp [δ,coordinate,h]
    have δmem (i : Fin 29) : δ i∈jointInactive A b := by
      apply mem_jointInactive.mpr
      constructor
      · intro j d
        by_cases e : j=i
        · subst j; rw [δval,ite_eq_left rfl,dx i d]
        · rw [δval,ite_eq_right e]
      · intro j y
        by_cases e : j=i
        · subst j; rw [δval,ite_eq_left rfl,bx i y]
        · rw [δval,ite_eq_right e]
    have paid (i : Fin 29) : δ i∈U := by
      have column := jointInactive_le_nine ho B (δmem i)
      rw [F9] at column
      apply HeadFiber.localized_mem H.coreStable H.extraSites column (z:=nodes A i)
      intro j h
      rw [δval,ite_eq_right (fun e=>h (congrArg (nodes A) e))]
    have sum : (∑ i, δ i)=x := by
      ext j
      simp only [Finset.sum_apply,δval]
      simp
    rw [←sum]
    exact U.sum_mem (fun i _=>paid i)

end
end RKResearch.Certified.ERK19
