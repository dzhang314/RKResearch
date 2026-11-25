module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.AdjoinRoot
public import RKCert.ReviewedNative.PolynomialProjectionSplit

public section

/-! # Cancel centrally in a monic chart before specializing

Put `M = R[z][u]/(G)`, with `G` monic in `u`. If the ideal `(v)` of
`M` contains a monic polynomial in `z`, the ideal is saturated for
every base-regular coefficient. The target ring need not preserve that
coefficient. All certificates below are ring identities or divisibilities
in the unspecialized presentation.
-/

namespace RKCert.ReviewedNative

open Polynomial

variable {R : Type*} [CommRing R] {G : Polynomial (Polynomial R)}

/-- Saturation of the principal ideal of `v` in the monic chart.
`w*v = of G g` is the projected monic certificate. -/
theorem dvd_of_smul_dvd_of_monic_projection
    (hG : G.Monic) {g : R[X]} (hg : g.Monic)
    {v w : AdjoinRoot G} (hproj : w * v = AdjoinRoot.of G g)
    {a : R} (ha : IsSMulRegular R a) {x : AdjoinRoot G}
    (hx : v ∣ a • x) : v ∣ x := by
  let e := (AdjoinRoot.powerBasisAux' hG).equivFun
  let V := LinearMap.mul R (AdjoinRoot G) v
  let W := LinearMap.mul R (AdjoinRoot G) w
  have hwv (y : AdjoinRoot G) : W (V y) = g • y := by
    change w * (v * y) = g • y
    calc
      w * (v * y) = (w * v) * y := (mul_assoc _ _ _).symm
      _ = (algebraMap R[X] (AdjoinRoot G) g) * y :=
        congrArg (fun z => z * y) hproj
      _ = g • y := (Algebra.smul_def g y).symm
  obtain ⟨L, hL⟩ := exists_linear_leftInverse_of_monic_scalar_comp e hg V W hwv
  obtain ⟨y, hy⟩ := hx
  have hrange : a • x ∈ V.range := LinearMap.mem_range.mpr ⟨y, hy.symm⟩
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp
    (mem_range_of_smul_mem_range V (isSMulRegular_of_polynomial_coordinates e ha)
      (smul_range_reflected_of_linear_leftInverse V L hL a) hrange)
  exact ⟨z, hz.symm⟩

/-- Simple arithmetic of the two archived combinations:
`t*q ∈ (v)` and `a*h = q*c mod v` imply `a*(t*h) ∈ (v)`. -/
private theorem dvd_smul_product_of_certificates
    {B : Type*} [CommRing B] [Algebra R B] {a : R} {v t q h c : B}
    (htq : v ∣ t * q) (hcert : v ∣ a • h - q * c) :
    v ∣ a • (t * h) := by
  obtain ⟨u, hu⟩ := htq
  obtain ⟨k, hk⟩ := hcert
  refine ⟨t * k + u * c, ?_⟩
  calc
    a • (t * h) = t * (a • h) := (mul_smul_comm a t h).symm
    _ = t * (v * k + q * c) := congrArg (t * ·) (sub_eq_iff_eq_add.mp hk)
    _ = t * (v * k) + (t * q) * c := by rw [mul_add, mul_assoc t q c]
    _ = v * (t * k + u * c) := by rw [hu, mul_add]; ac_rfl

/-- Any specialization killing `v` also kills the guarded value `t*h`,
even if it kills `a`. In a field, a nonzero specialized guard gives
`f h = 0`. Neither that field nor a characteristic need be chosen
when doing the scalar cancellation. -/
theorem map_guard_mul_eq_zero_of_monic_projection
    (hG : G.Monic) {t q : R[X]} (hg : (t * q).Monic)
    {v w h c : AdjoinRoot G}
    (hproj : w * v = AdjoinRoot.of G (t * q))
    {a : R} (ha : IsSMulRegular R a)
    (hcert : v ∣ a • h - AdjoinRoot.of G q * c)
    {T : Type*} [CommRing T] (f : AdjoinRoot G →+* T) (hv : f v = 0) :
    f (AdjoinRoot.of G t) * f h = 0 := by
  have htq : v ∣ AdjoinRoot.of G t * AdjoinRoot.of G q := by
    refine ⟨w, ?_⟩
    rw [← map_mul, ← hproj, mul_comm w v]
  obtain ⟨u, hu⟩ := dvd_of_smul_dvd_of_monic_projection hG hg hproj ha
    (dvd_smul_product_of_certificates htq hcert)
  simpa only [map_mul, hv, zero_mul] using congrArg f hu

/-- Literal two-variable polynomial form, to take the two original
generator combinations directly. They are congruences modulo `G`.
In particular the target never has to carry an inverse for `a`. -/
theorem eval₂_guard_mul_eq_zero_of_monic_chart
    (hG : G.Monic) {t q : R[X]} (hg : (t * q).Monic)
    {v w h c k : Polynomial (Polynomial R)}
    (hproj : G ∣ w * v - C (t * q))
    {a : R} (ha : IsSMulRegular R a)
    (hcert : G ∣ (a • h - C q * c) - v * k)
    {T : Type*} [CommRing T] (φ : R[X] →+* T) (y : T)
    (hGy : G.eval₂ φ y = 0) (hvy : v.eval₂ φ y = 0) :
    φ t * h.eval₂ φ y = 0 := by
  let m := AdjoinRoot.mk G
  have hp : m w * m v = AdjoinRoot.of G (t * q) := by
    change m w * m v = m (C (t * q))
    rw [← map_mul]
    exact AdjoinRoot.mk_eq_mk.mpr hproj
  have hc : m v ∣ a • m h - AdjoinRoot.of G q * m c := by
    refine ⟨m k, ?_⟩
    have he : m (a • h - C q * c) = m (v * k) := AdjoinRoot.mk_eq_mk.mpr hcert
    change a • AdjoinRoot.mk G h - AdjoinRoot.mk G (C q) * AdjoinRoot.mk G c =
      AdjoinRoot.mk G v * AdjoinRoot.mk G k
    simpa only [m, map_sub, map_mul, ← AdjoinRoot.smul_mk] using he
  have hv : AdjoinRoot.lift φ y hGy (m v) = 0 := by
    simpa only [m, AdjoinRoot.lift_mk] using hvy
  simpa only [m, AdjoinRoot.lift_mk, AdjoinRoot.lift_of] using
    map_guard_mul_eq_zero_of_monic_projection hG hg hp ha hc
      (AdjoinRoot.lift φ y hGy) hv

end RKCert.ReviewedNative
