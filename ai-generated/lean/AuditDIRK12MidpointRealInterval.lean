import RKCert.ReviewedNative.DIRK12MidpointRealStarBridge

open RKResearch FiniteRootedTree Polynomial
open RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval
open scoped Matrix Polynomial FiniteRootedTree

set_option autoImplicit false

example :
    ∃ x f d v : ℝ, Encloses xBox x ∧ Encloses fBox f ∧ realX x = 0 ∧ realF x f = 0 ∧
      d ≠ v ∧ d+v = S (moments x f) ∧ d*v = P (moments x f) := by
  obtain ⟨x,f,hx,hf,hQ,hF⟩ := exists_real_parameters
  obtain ⟨d,v,hd,hs,hp⟩ := exists_real_orientations hx hf
  exact ⟨x,f,d,v,hx,hf,hQ,hF,hd,hs,hp⟩

example {ι : Type} [Fintype ι] {x f d v : ℝ} (A : Matrix ι ι ℝ) (b : ι → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f)
    (hSum : d+v = S (moments x f)) (hProd : d*v = P (moments x f))
    (roots : ∀ i, b i * (supportHull x f d v).eval (1-Certified.Graded.nodes A i) = 0)
    (paid : ∀ Q : ℝ[X], Q.natDegree<12 → Certified.DIRK12MidpointStar.quadr A b Q = integral Q) :
    (starLo:ℝ) < (((bushyTree 13).factorial:Nat):ℝ) * (b ⬝ᵥ Φ (bushyTree 13) A)-1 ∧
      (((bushyTree 13).factorial:Nat):ℝ) * (b ⬝ᵥ Φ (bushyTree 13) A)-1 < (starHi:ℝ) :=
  actual_star_bounded A b hx hf hSum hProd roots paid

#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_real_parameters
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.exists_real_orientations
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.midpoint_star_bounds
#print axioms RKResearch.Certified.DIRK12MidpointRealInterval.actual_star_bounded
