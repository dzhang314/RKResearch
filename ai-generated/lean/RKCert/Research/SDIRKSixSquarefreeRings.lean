module
public import RKCert.Research.SDIRKSixFieldClassification
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

public section

/-! # Matching ring endpoints on the squarefree support locus

No reducedness assumption is imposed. The support integer must vanish
literally, as opposed to merely being nilpotent, for this CRT construction.
The exceptional factor 3533 needs a square root only in its own component.
-/

namespace RKResearch
open FiniteRootedTree
open scoped Matrix

namespace HasStrictSDIRKOrderSix

theorem prod {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (hR : HasStrictSDIRKOrderSix R n) (hS : HasStrictSDIRKOrderSix S n) :
    HasStrictSDIRKOrderSix (R × S) n := by
  obtain ⟨A,b,γ,ht,hγ,hu,ho⟩ := hR
  obtain ⟨T,w,δ,ht',hδ,hu',ho'⟩ := hS
  let M : Matrix (Fin n) (Fin n) (R × S) := Matrix.of fun i j => (A i j,T i j)
  let W : Fin n → R × S := fun i => (b i,w i)
  refine ⟨M,W,(γ,δ),?_,?_,?_,?_⟩
  · intro i j hij
    exact Prod.ext (ht hij) (ht' hij)
  · intro i
    exact Prod.ext (hγ i) (hδ i)
  · obtain ⟨u,hu⟩ := hu
    obtain ⟨v,hv⟩ := hu'
    rw [←hu, ←hv]
    apply IsUnit.of_mul_eq_one ((↑u⁻¹ : R), (↑v⁻¹ : S))
    exact Prod.ext (by simp) (by simp)
  · intro t ht
    apply Prod.ext
    · let f : (R × S) →+* R := RingHom.fst R S
      change f ((t.factorial : R × S) * (W ⬝ᵥ Φ t M)) = f 1
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ, map_one]
      exact ho t ht
    · let f : (R × S) →+* S := RingHom.snd R S
      change f ((t.factorial : R × S) * (W ⬝ᵥ Φ t M)) = f 1
      simp only [map_mul, map_natCast, RingHom.map_dotProduct, RKResearch.map_Φ, map_one]
      exact ho' t ht

private theorem crt {m n : ℕ} {s : ℕ} (hn : m.Coprime n)
    (hm : HasStrictSDIRKOrderSix (ZMod m) s) (h : HasStrictSDIRKOrderSix (ZMod n) s) :
    HasStrictSDIRKOrderSix (ZMod (m*n)) s :=
  (hm.prod h).map (ZMod.chineseRemainder hn).symm.toRingHom

/-- The base change of the quadratic witness needs the root relation,
not a field structure on the target. The statement also applies to
a trivial component, useful when taking CRT products. -/
theorem of_3533_square_root {R : Type*} [CommRing R]
    (hc : (3533 : R) = 0) (h : ∃ x : R, x^2 = 2077) : HasStrictSDIRKOrderSix R 6 := by
  obtain ⟨x,hx⟩ := h
  let f : ZMod 3533 →+* R := ZMod.castHom (ringChar.dvd (by simpa only [Nat.cast_ofNat] using hc)) R
  let : Algebra (ZMod 3533) R := f.toAlgebra
  let t : R := (x+824)*1767
  have ht : 2*t = x+824 := by
    dsimp only [t]
    linear_combination (norm := ring) (x+824)*hc
  have h4 : IsUnit (4 : R) :=
    IsUnit.of_mul_eq_one (2650 : R) (by linear_combination (norm := ring) 3*hc)
  have hh : t*t = (3009 : ZMod 3533) • (1 : R) + (824 : ZMod 3533) • t := by
    simp only [Algebra.smul_def, map_ofNat, mul_one]
    apply h4.mul_left_cancel
    linear_combination (norm := ring) (2*t+x-824)*ht + hx - 195*hc
  exact quadratic3533.map (QuadraticAlgebra.lift ⟨t,hh⟩).toRingHom

end HasStrictSDIRKOrderSix

/-- The squarefree product on which no quadratic generator is needed. -/
@[expose] def sixStagePlainSupport : ℕ := 187 * 163 * 263 * 457 * 126963077

private theorem split_support : sixStageSupport = sixStagePlainSupport * 3533 := by
  decide +kernel

/-- A single CRT tableau for all rings annihilated by the plain support. -/
theorem hasStrictSDIRKOrderSix_of_plain_support {R : Type*} [CommRing R]
    (h : (sixStagePlainSupport : R) = 0) : HasStrictSDIRKOrderSix R 6 := by
  open HasStrictSDIRKOrderSix in
  have hbase : HasStrictSDIRKOrderSix (ZMod sixStagePlainSupport) 6 :=
    crt (by decide) (crt (by decide) (crt (by decide) (crt (by decide) mod187 mod163) mod263) mod457) mod126963077
  exact hbase.map_zmod h

private theorem coprime_support_3533 {R : Type*} [CommRing R] :
    IsCoprime (sixStagePlainSupport : R) (3533 : R) := by
  refine ⟨1180, -155352042858586623, ?_⟩
  norm_num [sixStagePlainSupport, Nat.cast_mul]

/-- If the full squarefree support vanishes, it is enough for the
characteristic-3533 CRT component to contain the required square root.
The other components can be arbitrary commutative rings. -/
theorem hasStrictSDIRKOrderSix_of_squarefree_support {R : Type*} [CommRing R]
    (h : (sixStageSupport : R) = 0)
    (hx : ∃ x : R ⧸ Ideal.span ({(3533 : R)} : Set R), x^2 = 2077) :
    HasStrictSDIRKOrderSix R 6 := by
  let I : Ideal R := Ideal.span {(sixStagePlainSupport : R)}
  let J : Ideal R := Ideal.span {(3533 : R)}
  have hc : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr coprime_support_3533
  have hI : (sixStagePlainSupport : R ⧸ I) = 0 := by
    rw [←map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hJ : (3533 : R ⧸ J) = 0 := by
    rw [←Nat.cast_ofNat, ←map_natCast (Ideal.Quotient.mk J), Nat.cast_ofNat]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hIJ : I*J = ⊥ := by
    dsimp only [I,J]
    rw [Ideal.span_singleton_mul_span_singleton]
    have hz : (sixStagePlainSupport : R) * 3533 = 0 := by
      simpa only [split_support, Nat.cast_mul, Nat.cast_ofNat] using h
    rw [hz, Ideal.span_singleton_zero]
  let e : (R ⧸ I) × (R ⧸ J) ≃+* R := ((Ideal.quotientMulEquivQuotientProd I J hc).symm.trans
    (Ideal.quotEquivOfEq hIJ)).trans (RingEquiv.quotientBot R)
  exact ((hasStrictSDIRKOrderSix_of_plain_support hI).prod
    (HasStrictSDIRKOrderSix.of_3533_square_root hJ hx)).map e.toRingHom

/-- Matching minimum at six without the extension-sensitive factor. -/
theorem strictSDIRKOrderSix_minimum_plain_support {R : Type*} [CommRing R] [Nontrivial R]
    (h : (sixStagePlainSupport : R) = 0) :
    IsLeast {n : ℕ | HasStrictSDIRKOrderSix R n} 6 :=
  ⟨hasStrictSDIRKOrderSix_of_plain_support h, fun _ hn => HasStrictSDIRKOrderSix.six_le hn⟩

/-- Matching minimum at six in the squarefree support construction. -/
theorem strictSDIRKOrderSix_minimum_squarefree_support {R : Type*} [CommRing R] [Nontrivial R]
    (h : (sixStageSupport : R) = 0)
    (hx : ∃ x : R ⧸ Ideal.span ({(3533 : R)} : Set R), x^2 = 2077) :
    IsLeast {n : ℕ | HasStrictSDIRKOrderSix R n} 6 :=
  ⟨hasStrictSDIRKOrderSix_of_squarefree_support h hx, fun _ hn => HasStrictSDIRKOrderSix.six_le hn⟩

/-- Matching minimum at seven whenever the exceptional support survives
in a field image (equivalently its value in the ring is nonnilpotent). -/
theorem strictSDIRKOrderSix_minimum_off_support {R : Type*} [CommRing R] [Nontrivial R]
    (h : IsUnit (720 : R)) (hD : ¬ IsNilpotent (sixStageSupport : R)) :
    IsLeast {n : ℕ | HasStrictSDIRKOrderSix R n} 7 := by
  refine ⟨HasStrictSDIRKOrderSix.seven h, ?_⟩
  rintro n ⟨A,b,γ,ht,hγ,hunit,ho⟩
  exact ho.common_diagonal_order_six_stages_off_exceptional_support ht hγ (Or.inr hD)

end RKResearch
