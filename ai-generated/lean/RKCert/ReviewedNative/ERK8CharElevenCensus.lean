module
public import RKCert.ReviewedNative.ERK8PaidCensus
public import RKCert.ReviewedNative.ERK8CharElevenScalar

@[expose] public section

/-! # Full remaining paid tag counts at characteristic eleven
The exceptional characteristic only reopens five and seven off clocks.
The shape of these branches and their final closures use additional
scalar/physical arguments and are not asserted by this count. -/
namespace RKResearch.Certified.Graded.ERK8CharEleven

open RKResearch Module Polynomial OneOff Reverse ERKTaggedHorizon ERK8PaidField RKCert.Endpoint
open scoped Matrix Classical

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

private theorem anchored_zero (ho : HasOrder 8 A b) (L : K[X])
    (hd : L.natDegree ≤ 4) (hz : L.eval 0 = 0)
    (pay : ∀ j : Fin 4, probe A b j.val (evalNodes A L) = 0) : L = 0 := by
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero L).trans hz)
  by_cases h0 : Q = 0
  · simp [hQ, h0]
  have hqd : Q.natDegree ≤ 3 := by
    rw [hQ, natDegree_mul X_ne_zero h0, natDegree_X] at hd
    omega
  have hq := anchored_poly_zero_of_probes ho 3 (by decide) Q hqd (fun j => by
    rw [←hQ]
    exact pay j)
  simp [hQ, hq]

/-- Literal paid-width-ten theorem, valid in particular in
characteristic 11. Cases 5 and 7 may be eliminated by a separate
numerical guard, but no such guard is assumed in this statement. -/
theorem order8_count_one_four_five_seven (ha : ∀ i j, i≤j → A i j=0)
    (ho : HasOrder 8 A b) :
    (offKnots A).card=1 ∨
    ((offKnots A).card=4 ∧ (cleanKnots A).card=5) ∨
    ((offKnots A).card=5 ∧ (cleanKnots A).card=5) ∨
    ((offKnots A).card=7 ∧ (cleanKnots A).card=3) := by
  have H := order8_paid_even_horizon ha ho
  obtain ⟨r3,r4,cap⟩ := order8_paid_ranks ha ho H
  have sep : PolySeparated A 4 := PolySeparated.of_coeff
    (explicit_coeff_separated (s:=9) ha ho (q:=4) (by decide))
  have pos := off_pos_paid ha ho sep
  obtain ⟨no2,no3⟩ := not_two_or_three_paid ha ho sep r3 r4
  by_cases one : (offKnots A).card=1
  · exact Or.inl one
  have four : 4≤(offKnots A).card := by omega
  obtain ⟨P,dP,nz,_,_,fit⟩ := two_curve_head r3 r4 (by omega)
  have total := clean_off_count A
  by_cases small : (offKnots A).card≤6
  · have cancel := offMass_zero_of_head ho fit (by omega)
    have cl := order8_paid_five_clean ha ho cap four cancel
    have cases : (offKnots A).card=4 ∨ (offKnots A).card=5 := by omega
    exact Or.inr (cases.elim (fun h=>Or.inl ⟨h,cl⟩) (fun h=>Or.inr (Or.inl ⟨h,cl⟩)))
  · let T := cleanKnots A
    let L := nodalHull T
    have dL : L.natDegree=T.card := natDegree_nodalHull _
    have nL : L≠0 := (monic_nodalHull _).ne_zero
    have zT : (0:K)∈T := zero_mem_cleanKnots (s:=9) ha
    have cl : T.card=3 := by
      by_contra! ne
      have d : (P*L).natDegree≤4 := by
        rw [natDegree_mul nz nL,dL]
        change T.card+(offKnots A).card≤10 at total
        omega
      have z : (P*L).eval 0=0 := by rw [eval_mul,nodalHull_eval_of_mem zT,mul_zero]
      have probe0 (j : Fin 4) : probe A b j.val (evalNodes A (P*L))=0 := by
        exact on_hull_times_head_probes ho fit j.val (by
          change j.val+T.card+3≤8
          change T.card+(offKnots A).card≤10 at total
          have := j.isLt
          omega)
      exact mul_ne_zero nz nL (anchored_zero ho _ d z probe0)
    change T.card+(offKnots A).card≤10 at total
    exact Or.inr (Or.inr (Or.inr ⟨by omega,cl⟩))

end RKResearch.Certified.Graded.ERK8CharEleven

#print axioms RKResearch.Certified.Graded.ERK8CharEleven.order8_count_one_four_five_seven
