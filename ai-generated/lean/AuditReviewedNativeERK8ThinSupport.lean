module

import RKCert.ReviewedNative.ERKTaggedHorizonSupport

open RKResearch
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.ERKTaggedHorizon
open Polynomial

-- The two tags use the actual physical defect even if their abscissas coincide.
example {K : Type*} [Field K] {s : ℕ} (A : Matrix (Fin s) (Fin s) K) {x : K} :
    x ∈ cleanKnots A ↔ ∃ i, g A i = 0 ∧ nodes A i = x :=
  mem_cleanKnots

example {K : Type*} [Field K] [CharZero K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} (ho : HasOrder 8 A b) (P : K[X]) (d : P.natDegree ≤ 3)
    (h : ∀ k : Fin 3, probe A b k.val (evalNodes A ((X^2-X)*P)) = 0) :
    P = C (P.coeff 3) * LobattoEight.lobattoCubic :=
  beta_cubic_from_actual_probes ho (by decide) P d h

example {K : Type*} [Field K] [CharZero K] {P : K[X]}
    (d : P.natDegree ≤ 2) {u : K} (hu : u ≠ 0)
    (fac : LobattoEight.lobattoCubic = (X-C u)*P)
    (h : (primitive (X*P)).eval u = 0) : False :=
  LobattoEight.lobatto_first_on_scalar_gate d hu fac h

#print axioms RKResearch.Certified.Graded.LobattoEight.lobatto_first_on_scalar_gate
#print axioms RKResearch.Certified.Graded.ERKTaggedHorizon.anchored_poly_zero_of_probes
#print axioms RKResearch.Certified.Graded.ERKTaggedHorizon.beta_cubic_from_actual_probes
