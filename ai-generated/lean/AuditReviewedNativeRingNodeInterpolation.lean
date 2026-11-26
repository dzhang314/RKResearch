module

import RKCert.ReviewedNative.RingNodeInterpolation

open RKResearch.Certified.RingNodeInterpolation
open scoped Matrix

section
variable {R : Type*} [CommRing R] {n : ℕ}

-- The literal integer-node matrix has unit determinant over the paid ring.
example (paid : IsUnit (n.factorial : R)) :
    IsUnit (Matrix.vandermonde (fun i : Fin n => (i.val : R))).det :=
  isUnit_det_integerVandermonde paid

-- Reconstruction and integer-node evaluation are inverse in both directions.
example (paid : IsUnit (n.factorial : R)) (a : Fin n → R) :
    reconstruct (Matrix.vandermonde (fun i : Fin n => (i.val : R)) *ᵥ a) = a :=
  reconstruct_samples paid a

example (paid : IsUnit (n.factorial : R)) (v : Fin n → R) :
    Matrix.vandermonde (fun i : Fin n => (i.val : R)) *ᵥ reconstruct v = v :=
  samples_reconstruct paid v

-- The inputs are the literal j-th monomial samples on the integer grid.
example {ι : Type*} (paid : IsUnit (n.factorial : R)) (x : ι → R) (j : Fin n) :
    resample n x *ᵥ (fun k : Fin n => (k.val : R) ^ j.val) = fun i => x i ^ j.val :=
  resample_monomial paid x j

example {ι : Type*} (paid : IsUnit (n.factorial : R)) (x : ι → R) (j : Fin n) (i : ι) :
    ((j.val + 1 : ℕ) : R) *
      (primitiveReadMap paid x *ᵥ (fun k : Fin n => (k.val : R) ^ j.val)) i =
      x i ^ (j.val + 1) :=
  mul_primitiveReadMap_monomial paid x j i

-- The row evaluating the primitive at the actual endpoint 1 has cleared readout one.
example (paid : IsUnit (n.factorial : R)) (j : Fin n) :
    ((j.val + 1 : ℕ) : R) *
      (primitiveReadout paid 1 ⬝ᵥ (fun k : Fin n => (k.val : R) ^ j.val)) = 1 :=
  mul_quadratureWeights_monomial paid j

end

#print axioms RKResearch.Certified.RingNodeInterpolation.isUnit_det_integerVandermonde
#print axioms RKResearch.Certified.RingNodeInterpolation.reconstruct_samples
#print axioms RKResearch.Certified.RingNodeInterpolation.samples_reconstruct
#print axioms RKResearch.Certified.RingNodeInterpolation.resample_monomial
#print axioms RKResearch.Certified.RingNodeInterpolation.mul_primitiveReadMap_monomial
#print axioms RKResearch.Certified.RingNodeInterpolation.mul_quadratureWeights_monomial
