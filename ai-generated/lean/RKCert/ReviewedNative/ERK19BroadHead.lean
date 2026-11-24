module

public import RKCert.ReviewedNative.ERK19BroadCore

@[expose] public section

/-! # The very-wide branch has a paid physical quintic head

Its degree is forced by the grade-ten Jacobi alias and the same
physical one-head band, not by a new scalar pencil or a guessed mask. -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Polynomial Graded Graded.Reverse RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKCert.OneEscape
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

private theorem degree_length {Q : K[X]} {n : ℕ} (pos : 0<n)
    (d : Q.degree < (n : WithBot ℕ)) : Q.natDegree<n := by
  by_cases z : Q=0
  · simpa [z] using pos
  · exact (natDegree_lt_iff_degree_lt z).mpr d

private theorem trace_factor_of_chain {r : ℕ} {U : Submodule K (Fin 29→K)}
    {w v : Fin 29→K} {P : K[X]} (sub : U≤jointInactive A b)
    (trace : weightedEval (nodes A) (firstSeed A b) P=firstSeed A b*w)
    (hv : v∈chain (diag (nodes A)) U w r) :
    ∃ Q : K[X], Q.degree < (r : WithBot ℕ) ∧
      weightedEval (nodes A) (firstSeed A b) (P*Q)=firstSeed A b*v := by
  obtain ⟨u,hu,Q,dQ,eq⟩ := HeadFiber.exists_poly hv
  refine ⟨Q,dQ,?_⟩
  ext i
  have d0 : firstSeed A b i*u i=0 := by
    by_cases z : firstSeed A b i=0
    · rw [z,zero_mul]
    · rw [(mem_jointInactive.mp (sub hu)).1 i z,mul_zero]
  have t := congrFun trace i
  simp only [weightedEval_apply,Pi.mul_apply] at t
  simp only [weightedEval_apply,eval_mul,Pi.mul_apply]
  rw [congrFun eq i,Pi.add_apply,weightedEval_apply]
  calc
    _ = Q.eval (nodes A i)*(P.eval (nodes A i)*firstSeed A b i) := by ring
    _ = _ := by rw [t]; linear_combination -d0

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The ordinary tenth-grade rank rise is paid by the existing clock
shift, so all genuine off-seed live weights are clean there. -/
theorem nonzero_seed_grade_ten_clock_step (ha : ∀i j,i ≤ j → A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) :
    zeroSpace A 10=zeroSpace A 9 ⊔ (zeroSpace A 9).map (diag (nodes A)) := by
  apply zeroSpace_clock_step_of_unit
  · rw [(nonzero_seed_grade_ten ha ho nz).1,(width29_eight_nine ha ho).2]
  · intro inv
    have sep : PolySeparated A 9 := PolySeparated.of_coeff (coeff_separated ho (by decide))
    have h := clock_invariant_incoming ha (j:=8) sep inv
    rw [(width29_eight_nine ha ho).1,(width29_eight_nine ha ho).2] at h
    omega

theorem off_seed_live_ten_clean (ha : ∀i j,i ≤ j → A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) (band : FullFirstBand A b)
    (i : Fin 29) (d0 : firstSeed A b i=0) (bi : b i≠0) :
    ∀ f∈zeroSpace A 10,f i=0 := by
  intro f hf
  rw [nonzero_seed_grade_ten_clock_step ha ho nz] at hf
  obtain ⟨u,hu,_,⟨v,hv,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hf
  have z := clean_of_off_seed_live ho le_rfl band i d0 bi
  simp only [Pi.add_apply,diag_apply,z _ hu,z _ hv,mul_zero,add_zero]

structure WideQuinticHead (A : Matrix (Fin 29) (Fin 29) K) (b : Fin 29→K)
    (r : ℕ) (w : Fin 29→K) (P : K[X]) : Prop where
  fourPaid : 4≤r
  live : P≠0
  degree : P.natDegree+r=9
  trueTrace : weightedEval (nodes A) (firstSeed A b) P=firstSeed A b*w
  nine : zeroSpace A 9=chain (diag (nodes A)) (jointInactive A b) w (r+1)
  carrier : jointInactive A b≤zeroSpace A 8

set_option maxHeartbeats 1000000 in
theorem width29_very_wide_quintic_head (ha : ∀i j,i ≤ j → A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) (band : FullFirstBand A b)
    (wide : 19≤(weightedSites (nodes A) (firstSeed A b)).card) :
    ∃ r w P, WideQuinticHead A b r w P := by
  obtain ⟨f8,f9⟩ := width29_eight_nine ha ho
  have sep := coeff_separated ho (q:=9) (by decide)
  have cap : finrank K (zeroSpace A (8+1))≤finrank K (zeroSpace A 8)+1 := by
    change finrank K (zeroSpace A 9)≤finrank K (zeroSpace A 8)+1
    omega
  obtain ⟨r,U,w,H⟩ := flat_clock_head ha (j:=8) (d:=1) sep (by decide) (by decide) cap
  have JU := broad_core_eq_jointInactive ho band wide H
  have F8 : zeroSpace A 8=chain (diag (nodes A)) U w r := by
    simpa only [Nat.add_zero] using H.flags 0 (by decide)
  have F9 : zeroSpace A 9=chain (diag (nodes A)) U w (r+1) := H.flags 1 (by decide)
  have F10 : zeroSpace A 10=chain (diag (nodes A)) U w (r+2) := by
    rw [nonzero_seed_grade_ten_clock_step ha ho nz,F9,
      clock_chain_next H.coreStable (show 0<r+1 by omega)]
  have paid := (clock_chain_le_iff (T:=diag (nodes A)) (U:=U) (w:=w) r).mp F8.ge
  have w8 : w∈zeroSpace A 8 := by
    simpa only [pow_zero,Module.End.one_eq_id,LinearMap.id_apply] using paid.2 0 H.positive
  obtain ⟨P,dP,trace⟩ := original_first_degree_eight_trace ho band (zeroSpace_le_treeSpace A 8 w8)
  have pn : P≠0 := by
    intro z
    have d0 : firstSeed A b*w=0 := by simpa only [z,map_zero] using trace.symm
    have atSeed (i : Fin 29) (on : firstSeed A b i≠0) : w i=0 :=
      (mul_eq_zero.mp (congrFun d0 i : firstSeed A b i*w i=0)).resolve_left on
    have u : w∈jointInactive A b := by
      refine mem_jointInactive.mpr ⟨atSeed, fun i hi=>?_⟩
      by_cases ds : firstSeed A b i=0
      · exact clean_of_off_seed_live ho (by decide) band i ds hi w w8
      · exact atSeed i ds
    have p := clock_pow_mem_invariant H.coreStable (JU.symm ▸ u) (r+1)
    exact H.unpaid (zeroSpace_mono A (by decide : 8≤9) (H.coreInside p))
  have f := H.baseRank
  have r9 : r≤9 := by omega
  have drop := trace_degree_from_paid_shift ho band wide pn dP trace
    (k:=r-1) (by omega) (paid.2 (r-1) (by have :=H.positive;omega))
  have fact : (mesh9 K).natDegree ≤ P.natDegree+(r+1) := by
    have meshMem := nonzero_seed_first_alias ha ho nz
    rw [F10] at meshMem
    obtain ⟨Q,dQ,eQ⟩ := trace_factor_of_chain (show U≤jointInactive A b from JU.le) trace meshMem
    have dq : Q.natDegree≤r+1 := by have t := degree_length (by omega : 0<r+2) dQ; omega
    have whole : weightedEval (nodes A) (firstSeed A b) (mesh9 K)=
        firstSeed A b*evalNodes A (mesh9 K) := by ext i; simp [mul_comm]
    have bound : (P*Q).natDegree≤P.natDegree+(r+1) :=
      natDegree_mul_le.trans (by omega)
    have same := weighted_eq_at_enough_sites (j:=18) (by omega)
      (mesh9_degree.le.trans (by decide)) (bound.trans (by omega)) (whole.trans eQ.symm)
    rwa [same]
  rw [mesh9_degree] at fact
  have fit : P.natDegree+r=9 := by have :=H.positive; omega
  have sep8 : PolySeparated A 8 := (PolySeparated.of_coeff sep).mono (by decide)
  have capU := clock_invariant_outgoing ha sep8 H.coreInside H.coreStable
  change finrank K U+4 ≤ finrank K (zeroSpace A 9) at capU
  have four : 4≤r := by
    by_contra! small
    have r3 : r=3 := by omega
    have u6 : finrank K U=6 := by omega
    have u5 : zeroSpace A 5≤U := by
      intro x x5
      have x8 := zeroSpace_mono A (by decide : 5≤8) x5
      obtain ⟨Q,dQ,eq⟩ := original_first_degree_eight_trace ho band (zeroSpace_le_treeSpace A 8 x8)
      have smallQ : Q.natDegree≤5 := by
        by_cases qz : Q=0
        · simp [qz]
        · have h := trace_degree_from_paid_shift ho band wide qz dQ eq (k:=3) (by decide)
            (clock_pow_mem_new_grade x5 3)
          omega
      rw [F8] at x8
      obtain ⟨u,hu,R,rd,value⟩ := HeadFiber.exists_poly x8
      -- The explicit representative is the one whose coefficient vanishes.
      have exp : weightedEval (nodes A) (firstSeed A b) (P*R)=firstSeed A b*x := by
        ext i
        have z : firstSeed A b i*u i=0 := by
          by_cases ds : firstSeed A b i=0
          · rw [ds,zero_mul]
          · have good : u∈jointInactive A b := JU.le hu
            have dead : u i=0 := (mem_jointInactive.mp good).1 i ds
            rw [dead,mul_zero]
        have t := congrFun trace i
        simp only [weightedEval_apply,Pi.mul_apply] at t
        simp only [weightedEval_apply,eval_mul,Pi.mul_apply]
        rw [congrFun value i,Pi.add_apply,weightedEval_apply]
        calc
          _ = R.eval (nodes A i)*(P.eval (nodes A i)*firstSeed A b i) := by ring
          _ = _ := by rw [t]; linear_combination -z
      have rd' := degree_length H.positive rd
      have deg : (P*R).natDegree≤18 := natDegree_mul_le.trans (by omega)
      have eQR := weighted_eq_at_enough_sites (j:=18) (by omega) deg (by omega) (exp.trans eq.symm)
      have rz : R=0 := by
        by_contra z
        have d := natDegree_mul pn z
        rw [eQR] at d
        omega
      rw [value,rz,map_zero,add_zero]
      exact hu
    have grow6 := zeroSpace_rank_interval_of_separation ha sep (j:=6) (d:=2) (by decide) (by decide)
    have grow7 := zeroSpace_rank_interval_of_separation ha sep (j:=7) (d:=1) (by decide) (by decide)
    change finrank K (zeroSpace A 6)+2 ≤ finrank K (zeroSpace A 8) at grow6
    change finrank K (zeroSpace A 7)+1 ≤ finrank K (zeroSpace A 8) at grow7
    have low5 := grade_five_surplus_of_reviewed_order ha ho (by decide : 10≤19)
    have sep5 : PolySeparated A 5 := sep8.mono (by decide)
    have escape : ¬ (zeroSpace A 5).map (diag (nodes A))≤zeroSpace A 5 := by
      intro inv
      have c := clock_invariant_outgoing ha sep5 le_rfl inv
      change finrank K (zeroSpace A 5)+3 ≤ finrank K (zeroSpace A 6) at c
      omega
    let F := zeroSpace A 5 ⊔ (zeroSpace A 5).map (diag (nodes A))
    have inc : F≤U := by
      apply sup_le u5
      rintro _ ⟨x,hx,rfl⟩
      exact H.coreStable (Submodule.mem_map_of_mem (u5 hx))
    have proper : zeroSpace A 5 < F := by
      apply lt_of_le_of_ne le_sup_left
      intro e
      have bnd : (zeroSpace A 5).map (diag (nodes A))≤F := le_sup_right
      exact escape (bnd.trans e.ge)
    have count := Submodule.finrank_lt_finrank_of_lt proper
    have e : F=U := Submodule.eq_of_le_of_finrank_le inc (by omega)
    have sub : U≤zeroSpace A 6 := by
      rw [←e]
      apply sup_le (zeroSpace_mono A (by decide))
      rintro _ ⟨x,hx,rfl⟩
      exact diag_zeroSpace A 5 hx
    have cost := clock_invariant_outgoing ha (sep8.mono (show 6≤8 by decide)) sub H.coreStable
    change finrank K U+3 ≤ finrank K (zeroSpace A 7) at cost
    omega
  exact ⟨r,w,P,⟨four,pn,fit,trace,JU ▸ F9,JU ▸ H.coreInside⟩⟩

end
end RKResearch.Certified.ERK19
