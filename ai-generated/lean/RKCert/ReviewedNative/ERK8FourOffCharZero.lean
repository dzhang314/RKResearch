module

public import RKCert.ReviewedNative.ERK8FourOffPhysicalNewton
public import RKCert.ReviewedNative.ERK8CharElevenFourNoncenterScalar

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Literal four-off exclusion over every characteristic-zero field
The four-node terminal and actual Newton calculations are reused
without a characteristic-11 hypothesis. The checked characteristic-zero
scalar chart receives its literal chronological input here. -/
namespace RKResearch.Certified.Graded.FourOffNewton

open Polynomial RKResearch OneOff ERKTaggedHorizon ERK8PaidField FourOffPhysical
open RKCert.Endpoint
open RKResearch.Certified.Graded.MultiOff.FourOff8CleanShape
open RKResearch.Certified.Graded.MultiOff.FourOff8Scalar
open scoped Classical Matrix

variable {K : Type*} [Field K]

/-- One cofactor term: on nonconstant monomials the factor of the
node itself cancels the same factor of the original nodal cofactor. -/
private theorem cancel_clean_clock {u v w d : K} (un : u≠0) (dn : d≠0)
    (uv : u≠v) (uw : u≠w) {r : ℕ} (rpos : 1≤r) :
    (u^r/d)/(u*(u-v)*(u-w))=(d*(u-v)*(u-w))⁻¹*u^(r-1) := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  simp only [Nat.succ_sub_one,pow_succ']
  field_simp [un,dn,sub_ne_zero.mpr uv,sub_ne_zero.mpr uw]

theorem nodalMeasure_eq_reviewed_moment
    {P : K[X]} {h x z theta kap : K}
    (D : CleanClocks h x z) (hd : P.natDegree≤2)
    (N : NormalizedShape P h x z theta kap) {r : ℕ} (rpos : 1≤r) :
    nodalMeasure P (cleanSites h x z) (X^r)=moment (shape h x z theta kap) h x z r := by
  obtain ⟨c0,ch,cx,cz⟩ := four_clean_cofactors D
  unfold moment cleanWeight
  rw [nodalMeasure_four P _ D,c0,ch,cx,cz]
  simp only [eval_pow,eval_X,zero_pow (by omega : r≠0),zero_div,zero_add]
  rw [N.coeffs.eval hd h,N.coeffs.eval hd x,N.coeffs.eval hd z]
  rw [cancel_clean_clock (lobatto_clock_ne_zero D.root_h) N.nonzero.ph_ne D.h_ne_x D.h_ne_z rpos,
    cancel_clean_clock (lobatto_clock_ne_zero D.root_x) N.nonzero.px_ne D.h_ne_x.symm D.x_ne_z rpos,
    cancel_clean_clock (lobatto_clock_ne_zero D.root_z) N.nonzero.pz_ne D.h_ne_z.symm D.x_ne_z.symm rpos]

variable [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Four-off cannot occur in the actual width-ten order-eight tableau.
Only field operations and characteristic zero are used; no ordering
or distinguished square root is assumed. -/
theorem no_four_off_charZero
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b) :
    (offKnots A).card≠4 := by
  intro off
  obtain ⟨P,R,dup,k,_theta,_scale,M,L,T,_raw⟩ := actual_raw_head_of_order8_four_off ha ho off
  let h := nodes A k
  let x := nodes A 6
  let z := nodes A 7
  let S := cleanSites h x z
  have H : CleanClocks h x z := L.roots
  obtain ⟨theta,kap,N⟩ := clean_shape_from_actual_prefix ha ho M.rankData.bandFour off L
    M.rankData.headDegree M.rankData.headNonzero M.rankData.fit T
  change NormalizedShape P h x z theta kap at N
  have p2 := N.head_degree M.rankData.headDegree
  have C : S.card=4 := cleanSites_card H
  have cp : ∀ u∈S,P.eval u≠0 := by
    intro u hu
    simp only [S,cleanSites,Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl|rfl|rfl|rfl
    · rw [N.coeffs.eval M.rankData.headDegree]
      simpa [Quad.eval] using N.nonzero.p0_ne
    · rw [N.coeffs.eval M.rankData.headDegree]
      exact N.nonzero.ph_ne
    · rw [N.coeffs.eval M.rankData.headDegree]
      exact N.nonzero.px_ne
    · rw [N.coeffs.eval M.rankData.headDegree]
      exact N.nonzero.pz_ne
  have sq : nodalHull S=quartic h x z := cleanSites_hull H
  have T' : CleanTerminalProfile A (nodalHull S) R := sq.symm ▸ T
  obtain ⟨sig,sn,he⟩ := actual_terminal_hull_transfer M C cp p2 T'
  obtain ⟨δ,tap,gain,t5,rows⟩ := paid_newton_clean_transfer ha ho M C cp p2 sn he
  let e := nodes A (fourthEarlyOff k)
  let Cmom := moment (shape h x z theta kap) h x z
  have eq (r : ℕ) (rpos : 1≤r) : nodalMeasure P S (X^r)=Cmom r :=
    nodalMeasure_eq_reviewed_moment H M.rankData.headDegree N rpos
  have r1 : nodalMeasure P S X=Cmom 1 := by simpa only [pow_one] using eq 1 (by decide)
  have r2 := eq 2 (by decide)
  have r3 := eq 3 (by decide)
  have r4 := eq 4 (by decide)
  obtain ⟨O2,E2⟩ := rows 1 (by decide) (by decide)
  obtain ⟨O3,E3⟩ := rows 2 (by decide) (by decide)
  obtain ⟨O4,E4⟩ := rows 3 (by decide) (by decide)
  simp only [Nat.reduceAdd,Nat.cast_ofNat,r1,r2,r3,r4,pow_one] at O2 E2 O3 E3 O4 E4
  rcases M.firstAtFourOrFive with k4|k5
  · exact firstCleanAt4_contradiction H N.scale_ne N.ratio
      (show EarlyRows Cmom δ e h tap from ⟨O2,O3,O4⟩)
      (show FirstCleanRows Cmom e h gain from ⟨E2 k4,E3 k4,E4 k4⟩)
  · rw [t5 k5] at O2 O3 O4
    exact firstCleanAt5_contradiction H N.scale_ne N.ratio
      (show EarlyRows Cmom δ e h 0 from ⟨O2,O3,O4⟩)

end RKResearch.Certified.Graded.FourOffNewton

#print axioms RKResearch.Certified.Graded.FourOffNewton.no_four_off_charZero
