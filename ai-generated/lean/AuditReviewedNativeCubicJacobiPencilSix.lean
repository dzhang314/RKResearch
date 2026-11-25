import RKCert.ReviewedNative.CubicJacobiPencilSix

open Polynomial
open RKCert.ReviewedNative.JacobiSix RKCert.ReviewedNative.PositiveRule19

example (K : Type*) [Field K] [CharZero K] :
    (J6 K).Monic ∧ (J6 K).natDegree = 6 ∧ OrthogonalSix (J6 K) ∧
    (J7 K).Monic ∧ (J7 K).natDegree = 7 ∧ OrthogonalSix (J7 K) :=
  ⟨J6_monic K, J6_natDegree K, J6_orthogonal, J7_monic K, J7_natDegree K, J7_orthogonal⟩

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q : K[X]} (mq : Q.Monic) (deg : Q.natDegree = 7)
    (moments : ∀ R : K[X], R.natDegree ≤ 5 → integral 0 1 (X * (1-X) * Q * R) = 0) :
    ∃ a : K, Q = J7 K + C a * J6 K :=
  monic_seven_pencil mq deg moments

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q : K[X]} (mq : Q.Monic) (deg : Q.natDegree = 7)
    (moments : ∀ R : K[X], R.natDegree ≤ 5 → integral 0 1 (X * (1-X) * Q * R) = 0)
    (at14 : 0 < Q.eval (14/15)) (at15 : 0 < Q.eval (15/16)) : False :=
  not_monic_seven_positive_at_cut_points mq deg moments at14 at15

#print axioms RKCert.ReviewedNative.JacobiSix.J6_orthogonal
#print axioms RKCert.ReviewedNative.JacobiSix.J7_orthogonal
#print axioms RKCert.ReviewedNative.JacobiSix.monic_seven_pencil
#print axioms RKCert.ReviewedNative.JacobiSix.not_monic_seven_positive_at_cut_points
