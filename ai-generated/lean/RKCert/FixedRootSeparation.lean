module

public import RKCert.FixedPolynomialSpecialize
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-! # Distinct fixed roots stay distinct at a simple good prime
A divided-difference equation is preserved alongside the root equations.
It prevents the kernel from silently treating distinct physical clocks
as distinct residue elements without proof. -/
namespace RKCert.FixedPolynomial
open MvPolynomial

universe u
variable {ι : Type*} {R : Type*} [CommRing R]

noncomputable def rootEquation (D : Polynomial ℤ) (i : ι) : MvPolynomial ι ℤ :=
  D.eval₂ MvPolynomial.C (X i)

theorem eval_rootEquation (D : Polynomial ℤ) (a : ι → R) (i : ι) :
    (rootEquation D i).eval₂ (Int.castRingHom R) a=D.eval₂ (Int.castRingHom R) (a i) := by
  let E := MvPolynomial.eval₂Hom (Int.castRingHom R) a
  have e : E.comp MvPolynomial.C=Int.castRingHom R := by ext z; simp [E]
  change E (Polynomial.eval₂ MvPolynomial.C (X i) D)=_
  rw [Polynomial.hom_eval₂,e]
  simp [E]

noncomputable def dividedEquation (D : Polynomial ℤ) (i j : ι) : MvPolynomial ι ℤ :=
  ∑ n ∈ Finset.range (D.natDegree+1), C (D.coeff n)*
    (∑ k∈ Finset.range n,X i^k*X j^(n-1-k))

theorem eval_dividedEquation (D : Polynomial ℤ) (a : ι → R) (i j : ι) :
    (dividedEquation D i j).eval₂ (Int.castRingHom R) a =
      ∑ n∈Finset.range (D.natDegree+1), (D.coeff n:R)*
        (∑ k∈Finset.range n, (a i)^k*(a j)^(n-1-k)) := by
  change MvPolynomial.eval₂Hom (Int.castRingHom R) a (dividedEquation D i j)=_
  rw [dividedEquation,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul,MvPolynomial.eval₂Hom_C,map_sum]
  simp

theorem eval_dividedEquation_mul (D : Polynomial ℤ) (a : ι → R) (i j : ι) :
    (dividedEquation D i j).eval₂ (Int.castRingHom R) a*(a i-a j)=
      D.eval₂ (Int.castRingHom R) (a i)-D.eval₂ (Int.castRingHom R) (a j) := by
  rw [eval_dividedEquation,Finset.sum_mul,Polynomial.eval₂_eq_sum_range,Polynomial.eval₂_eq_sum_range,
    ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_assoc,geom_sum₂_mul,mul_sub]
  rfl

theorem eval_dividedEquation_diag (D : Polynomial ℤ) (a : ι → R) (i j : ι)
    (he : a i=a j) :
    (dividedEquation D i j).eval₂ (Int.castRingHom R) a =
      D.derivative.eval₂ (Int.castRingHom R) (a i) := by
  have D' : D.derivative =
      ∑ n∈Finset.range (D.natDegree+1), Polynomial.monomial (n-1) ((n:ℤ)*D.coeff n) := by
    conv_lhs => rw [D.as_sum_range]
    rw [Polynomial.derivative_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Polynomial.derivative_monomial,mul_comm]
  rw [eval_dividedEquation,D',Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  have hs : (∑ k∈Finset.range n,a i^k*a j^(n-1-k))=(n:R)*a i^(n-1) := by
    rw [←he,show (∑ k∈Finset.range n,a i^k*a i^(n-1-k))=
      ∑ _k∈Finset.range n,a i^(n-1) from ?_]
    · simp [nsmul_eq_mul]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [←pow_add]
      congr 1
      have h := Finset.mem_range.mp hk
      omega
  rw [hs,Polynomial.eval₂_monomial,map_mul]
  change (D.coeff n:R) * ((n:R) * a i^(n-1)) =
    (((n:ℤ):R) * (D.coeff n:R)) * a i^(n-1)
  rw [Int.cast_natCast]
  ring

theorem Specialization.root_preserved {p : ℕ} {K : Type u} [Field K] {a : ι → K}
    (S : Specialization p a) (D : Polynomial ℤ) (i : ι)
    (h : D.eval₂ (Int.castRingHom K) (a i)=0) :
    D.eval₂ (Int.castRingHom S.carrier) (S.image i)=0 := by
  have he := S.preserves (rootEquation D i) (by rwa [eval_rootEquation])
  rwa [eval_rootEquation] at he

/-- In an integral-root specialization, distinct roots of D are preserved
as distinct whenever the modular polynomial and its derivative are coprime.
The proof needs no primitive element or algorithm for splitting. -/
theorem Specialization.distinct_roots_of_good_prime {p : ℕ} [Fact p.Prime]
    {K : Type u} [Field K] {a : ι → K}
    (S : Specialization p a) (D : Polynomial ℤ) {i j : ι}
    (hi : D.eval₂ (Int.castRingHom K) (a i)=0)
    (hj : D.eval₂ (Int.castRingHom K) (a j)=0) (hne : a i≠a j)
    (hgood : IsCoprime (D.map (Int.castRingHom (ZMod p)))
      (D.derivative.map (Int.castRingHom (ZMod p)))) : S.image i≠S.image j := by
  intro hEq
  have e := eval_dividedEquation_mul D a i j
  rw [hi,hj,sub_self] at e
  have e0 := (mul_eq_zero.mp e).resolve_right (sub_ne_zero.mpr hne)
  have der := S.preserves (dividedEquation D i j) e0
  rw [eval_dividedEquation_diag _ _ _ _ hEq] at der
  have r := S.root_preserved D i hi
  let T := Polynomial.eval₂RingHom S.embed (S.image i)
  have hT : S.embed.comp (Int.castRingHom (ZMod p))=Int.castRingHom S.carrier := by
    ext n
    simp
  have r' : T (D.map (Int.castRingHom (ZMod p)))=0 := by
    change (D.map (Int.castRingHom (ZMod p))).eval₂ S.embed (S.image i)=0
    rwa [Polynomial.eval₂_map,hT]
  have d' : T (D.derivative.map (Int.castRingHom (ZMod p)))=0 := by
    change (D.derivative.map (Int.castRingHom (ZMod p))).eval₂ S.embed (S.image i)=0
    rwa [Polynomial.eval₂_map,hT]
  obtain ⟨U,V,eq⟩ := hgood
  have e' := congrArg T eq
  rw [map_add,map_mul,map_mul,map_one,r',d',mul_zero,mul_zero,add_zero] at e'
  exact zero_ne_one e'

end RKCert.FixedPolynomial
