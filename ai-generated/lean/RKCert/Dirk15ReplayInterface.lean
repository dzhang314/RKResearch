module

public import RKCert.Dirk15ArithmeticNorms

@[expose] public section

/-! # Explicit degree-preserving prime replay obligations for order 15

Reducing these integer polynomials modulo 1009 is only useful with the
structural caps attained; separate modular coprimality then transfers
the Sylvester obstruction to all characteristic-zero fields. -/
namespace RKCert.FixedPolynomial
open Polynomial 
open scoped Classical
noncomputable section

set_option maxRecDepth 4096 in
instance order15Prime : Fact (Nat.Prime 1009) := ⟨by norm_num⟩

abbrev order15Reduce : ℤ→+*ZMod 1009 :=
  Int.castRingHom (ZMod 1009)

structure Order15GoodPrimePair (P Q : ℤ[X]) (d e : ℕ) : Prop where
  leftDegree : (P.map order15Reduce).natDegree=d
  rightDegree : (Q.map order15Reduce).natDegree=e
  notBothConstant : d≠0 ∨ e≠0
  coprime : IsCoprime (P.map order15Reduce) (Q.map order15Reduce)

theorem Order15GoodPrimePair.no_common {P Q : ℤ[X]} {d e : ℕ}
    (cert : Order15GoodPrimePair P Q d e)
    (pCap : P.natDegree≤d) (qCap : Q.natDegree≤e)
    {K : Type*} [Field K] [CharZero K] (u : K)
    (p0 : P.eval₂ (Int.castRingHom K) u=0)
    (q0 : Q.eval₂ (Int.castRingHom K) u=0) : False := by
  have w := no_common_eval_of_good_prime P Q d e pCap qCap cert.leftDegree cert.rightDegree
    cert.notBothConstant cert.coprime u
  simp only [eval_map,p0,q0,ne_eq,not_true_eq_false,or_self] at w

/-- Exactly the five families of finite checks. The hypotheses below range
over the fixed small indices only, not a candidate array or its free parameter. -/
structure Order15FiniteReplay : Prop where
  forwardMoments : ∀ (n k e : ℕ), (n=5 ∨ n=6) → 0<k → e≤1 → k+e≤4 →
    Order15GoodPrimePair (nodeMomentNorm n k (1+e) 0) (nodeMomentNorm n k (2+e) 0)
      (momentCap n k 0) (momentCap n k 0)
  reflectedMoments : ∀ (n k : ℕ), (n=5 ∨ n=6) → 0<k → k≤3 →
    Order15GoodPrimePair (nodeMomentNorm n k 1 1) (nodeMomentNorm n k 2 1)
      (momentCap n k 1) (momentCap n k 1)
  fixedMoments : ∀ (n k : ℕ), (n=5 ∨ n=6) → 0<k → k≤4 →
    Order15GoodPrimePair (anchorMomentNorm n k 1) (anchorMomentNorm n k 2)
      (n.choose (k-1)) (n.choose (k-1))
  gramBothRoots : ∀ (n k e : ℕ), (n=5 ∨ n=6) → 0<k → e≤1 → k+e≤3 →
    Order15GoodPrimePair (parameterGramNorm n k (1+e) 0) (minusParameter (parameterGramNorm n k 1 e))
      (2*momentCap n k 0) (2*momentCap n k e)
  gramFixedReverse : ∀ (n k : ℕ), (n=5 ∨ n=6) → 0<k → k≤3 →
    Order15GoodPrimePair (parameterGramNorm n k 1 0) (minusParameter (anchorGramNorm n k))
      (2*momentCap n k 0) (2*n.choose (k-1))

end
end RKCert.FixedPolynomial
