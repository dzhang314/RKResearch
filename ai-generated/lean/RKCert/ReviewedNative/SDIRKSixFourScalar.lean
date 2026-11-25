module

public import RKCert.ReviewedNative.SDIRKSixIntegralReceipts
public import RKCert.ReviewedNative.MonicChartSpecialization
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

@[expose] public section

/-! # The four-multiplier strict SDIRK6 scalar obstruction

Only the original combinations in SDIRKSixIntegralReceipts are used.
The large branch multiplier is canceled over ℤ[1/30], not in a target
field. The proof recovers ideal membership by applying those same
receipts to quotient maps. -/
namespace RKCert.ReviewedNative.SDIRKSixReceipts

open Polynomial

/-- Sufficient exception product; not claimed to be exact. -/
def fourExceptionProduct : ℕ :=
  3846112 * 198898968576 * 122267206287360000 * 6214370355160790146744320000

theorem isUnit_of_dvd_paid_power {R : Type*} [CommRing R] (h30 : IsUnit (30 : R))
    {n : ℕ} (hn : n ∣ 30 ^ 13) : IsUnit (n : R) := by
  apply isUnit_of_dvd_unit _ (h30.pow 13)
  obtain ⟨m,hm⟩ := hn
  refine ⟨(m:R), ?_⟩
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using
    congrArg (fun j : ℕ => (j:R)) hm

private theorem cancel_paid {R : Type*} [CommRing R] (h30 : IsUnit (30 : R))
    {n : ℕ} (hn : n ∣ 30 ^ 13) {x : R} (hx : (n : R) * x = 0) : x = 0 :=
  (isUnit_of_dvd_paid_power h30 hn).mul_left_cancel (by simpa only [mul_zero] using hx)

private abbrev Base := Localization.Away (30 : ℤ)
private abbrev PolyBase := Polynomial Base

private theorem base_paid : IsUnit (30 : Base) := by
  simpa only [map_ofNat] using
    (IsLocalization.Away.algebraMap_isUnit (S := Base) (30 : ℤ))

private theorem base_regular : IsSMulRegular Base (5446080 : Base) := by
  have h30 : (30 : ℤ) ≠ 0 := by decide
  letI : IsDomain Base := Localization.Away.isDomain h30
  have inj := IsLocalization.injective Base (powers_le_nonZeroDivisors_of_noZeroDivisors h30)
  have hm : (algebraMap ℤ Base) (5446080 : ℤ) ≠ (algebraMap ℤ Base) 0 :=
    fun h => (show (5446080 : ℤ) ≠ 0 from by decide) (inj h)
  have h : (5446080 : Base) ≠ 0 := by simpa only [map_ofNat, map_zero] using hm
  exact fun _ _ he => mul_left_cancel₀ h he

private noncomputable def cubic {P : Type*} [CommRing P] (a b c d : P) : P[X] :=
  C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

private theorem cubic_one_monic {P : Type*} [CommRing P] (b c d : P) :
    (cubic 1 b c d).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3
  · unfold cubic
    compute_degree!
  · norm_num [cubic, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]

/-- The cubic leading coefficients use the small archived zero-chart
Bézout identity. -/
private theorem leading_bezout {P : Type*} [CommRing P] (h30 : IsUnit (30 : P)) (z : P) :
    ∃ s t : P, s * (2 * zeroCubic z 0 0) + t * zeroLaguerre z 0 0 = 1 := by
  let p := -53*z^4 + 1344*z^3 - 9660*z^2 + 18720*z - 8280
  let q := -53*z^2 + 390*z - 1368
  have h : p * zeroCubic z 0 0 + q * zeroLaguerre z 0 0 = 8640 := by
    dsimp [p, q, zeroCubic, zeroLaguerre]
    ring
  obtain ⟨j, hj⟩ := (isUnit_of_dvd_paid_power h30 (n := 17280) (by decide)).exists_left_inv
  refine ⟨j * p, (j * 2) * q, ?_⟩
  calc
    _ = j * (2 * (p * zeroCubic z 0 0 + q * zeroLaguerre z 0 0)) := by ring
    _ = 1 := by rw [h]; norm_num at hj ⊢; exact hj

/-- Cancel the twelve-branch scalar before specializing. This also
works when the target image of 5446080 vanishes. -/
theorem hTwelve_guard_mul_eq_zero {K : Type*} [CommRing K] (h30 : IsUnit (30 : K))
    {z u ρ : K} (hf : front z u ρ = 0) (hb : bridge1 z u ρ = 0) :
    (z^2 * factorThree z u ρ) * hTwelve z u ρ = 0 := by
  classical
  letI pRing : CommRing PolyBase := by
    change CommRing (AddMonoidAlgebra Base ℕ)
    exact AddMonoidAlgebra.commRing
  letI ppRing : CommRing (Polynomial PolyBase) := by
    change CommRing (AddMonoidAlgebra PolyBase ℕ)
    exact AddMonoidAlgebra.commRing
  let x₀ : PolyBase := X
  let Z : PolyBase[X] := C x₀
  let U : PolyBase[X] := X
  let F : PolyBase[X] := front Z U 0
  let B : PolyBase[X] := bridge1 Z U 0
  let a : PolyBase := 2 * zeroCubic x₀ 0 0
  let d : PolyBase := zeroLaguerre x₀ 0 0
  let f₂ : PolyBase := -10*x₀^3 + 84*x₀^2 - 240*x₀ + 120
  let f₁ : PolyBase := 15*x₀^3 - 84*x₀^2 + 120*x₀
  let f₀ : PolyBase := -6*x₀^3 + 24*x₀^2
  let b₂ : PolyBase := 4*x₀^5 - 102*x₀^4 + 840*x₀^3 - 2640*x₀^2 + 2880*x₀ - 720
  let b₁ : PolyBase := -5*x₀^5 + 102*x₀^4 - 630*x₀^3 + 1320*x₀^2 - 720*x₀
  let b₀ : PolyBase := 2*x₀^5 - 36*x₀^4 + 180*x₀^3 - 240*x₀^2
  have hFC : F = cubic a f₂ f₁ f₀ := by
    dsimp only [F, front, cubic, a, zeroCubic, f₂, f₁, f₀, Z, U]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    ring
  have hBC : B = cubic d b₂ b₁ b₀ := by
    dsimp only [B, bridge1, cubic, d, zeroLaguerre, b₂, b₁, b₀, Z, U]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    ring
  have h30P : IsUnit (30 : PolyBase) := by
    simpa only [map_ofNat] using base_paid.map (C : Base →+* PolyBase)
  obtain ⟨α, β, hab⟩ := leading_bezout h30P x₀
  change α * a + β * d = 1 at hab
  let G : PolyBase[X] := C α * F + C β * B
  let V : PolyBase[X] := -C d * F + C a * B
  have hGc : G = cubic (α*a+β*d) (α*f₂+β*b₂) (α*f₁+β*b₁) (α*f₀+β*b₀) := by
    change C α * F + C β * B = _
    rw [hFC, hBC]
    simp only [cubic, map_add, map_mul]
    ring
  have hG : G.Monic := by
    rw [hGc, hab]
    exact cubic_one_monic _ _ _
  have hcomb : C α * C a + C β * C d = (1 : PolyBase[X]) := by
    rw [← map_mul, ← map_mul, ← map_add, hab, map_one]
  have hFi : F = C a * G - C β * V := by
    calc
      F = (C α * C a + C β * C d) * F := by rw [hcomb, one_mul]
      _ = _ := by dsimp only [G, V]; ring
  have hBi : B = C d * G + C α * V := by
    calc
      B = (C α * C a + C β * C d) * B := by rw [hcomb, one_mul]
      _ = _ := by dsimp only [G, V]; ring

  let M := AdjoinRoot G
  letI : CommRing M := inferInstanceAs (CommRing (AdjoinRoot G))
  let m := AdjoinRoot.mk G
  let x : M := AdjoinRoot.of G x₀
  let y : M := m U
  let v : M := m V
  let t : PolyBase := x₀^2 * factorThree x₀ 0 0
  let q : PolyBase := factorTwelve x₀ 0 0
  let H : M := hTwelve x y 0
  have hg : (t*q).Monic := by
    change ((x₀^2 * factorThree x₀ 0 0) * factorTwelve x₀ 0 0).Monic
    refine ((monic_X.pow 2).mul ?_).mul ?_
    · dsimp only [x₀, factorThree]
      monicity!
    · dsimp only [x₀, factorTwelve]
      monicity!
  have mZ : m Z = x := rfl
  have mU : m U = y := rfl
  have mF : m F = front x y 0 := by
    change m (front Z U 0) = _
    simp only [front, map_pow, map_mul, map_add, map_sub, map_ofNat, mZ, mU]
  have mB : m B = bridge1 x y 0 := by
    change m (bridge1 Z U 0) = _
    simp only [bridge1, map_pow, map_mul, map_add, map_sub, map_neg, map_ofNat, mZ, mU]
  have mG : m G = 0 := AdjoinRoot.mk_self
  have killFB (J : Ideal M) (hvJ : v ∈ J) :
      front (Ideal.Quotient.mk J x) (Ideal.Quotient.mk J y) 0 = 0 ∧
      bridge1 (Ideal.Quotient.mk J x) (Ideal.Quotient.mk J y) 0 = 0 := by
    let j := Ideal.Quotient.mk J
    have hjV : j (m V) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hvJ
    have hjF : j (m F) = 0 := by
      rw [hFi]
      simp only [map_sub, map_mul, mG, map_zero, mul_zero, hjV, sub_zero]
    have hjB : j (m B) = 0 := by
      rw [hBi]
      simp only [map_add, map_mul, mG, map_zero, mul_zero, hjV, add_zero]
    constructor
    · simpa only [j, mF, front, map_pow, map_mul, map_add, map_sub, map_ofNat] using hjF
    · simpa only [j, mB, bridge1, map_pow, map_mul, map_add, map_sub, map_neg, map_ofNat] using hjB
  let I := Ideal.span ({v} : Set M)
  let i := Ideal.Quotient.mk I
  obtain ⟨hiF, hiB⟩ := killFB I (Ideal.mem_span_singleton_self v)
  have hi30 : IsUnit (30 : M ⧸ I) := by
    simpa only [map_ofNat] using base_paid.map (i.comp (algebraMap Base M))
  have hgI : i (AdjoinRoot.of G (t*q)) = 0 := by
    have hp := cancel_paid hi30 (n := 360) (by decide)
      (project_mul (i x) (i y) 0 hiB hiF)
    simpa only [t, q, x, factorThree, factorTwelve, map_pow, map_mul, map_add, map_sub, map_ofNat] using hp
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hgI)
  have hproj : w * v = AdjoinRoot.of G (t*q) := (mul_comm _ _).trans hw.symm

  let Iq := Ideal.span ({AdjoinRoot.of G q} : Set M)
  let J := I ⊔ Iq
  let j := Ideal.Quotient.mk J
  obtain ⟨hjF, hjB⟩ := killFB J (Ideal.mem_sup_left (Ideal.mem_span_singleton_self v))
  have hjq : j (AdjoinRoot.of G q) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (AdjoinRoot.of G q)))
  have hqj : factorTwelve (j x) (j y) 0 = 0 := by
    simpa only [q, factorTwelve, x, map_pow, map_mul, map_add, map_sub, map_ofNat] using hjq
  have hjH : j ((5446080 : Base) • H) = 0 := by
    have hh := deriveHTwelve_mul (j x) (j y) 0 hjB hjF hqj
    have eq : (5446080 : Base) • H = (5446080 : M) * H := by
      change ((5446080 : ℕ) : Base) • H = ((5446080 : ℕ) : M) * H
      exact (Nat.cast_smul_eq_nsmul Base 5446080 H).trans (nsmul_eq_mul 5446080 H)
    rw [eq]
    simpa only [H, hTwelve, map_pow, map_mul, map_add, map_sub, map_ofNat] using hh
  have hJ := Ideal.Quotient.eq_zero_iff_mem.mp hjH
  obtain ⟨l, hl, r, hr, hlr⟩ := Submodule.mem_sup.mp hJ
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp hl
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
  have hcert : v ∣ (5446080 : Base) • H - AdjoinRoot.of G q * c := by
    refine ⟨k, ?_⟩
    rw [← hlr, hk, hc, add_sub_cancel_right]

  -- The target specialization only needs the already-paid 30.
  let baseMap : Base →+* K := IsLocalization.Away.lift (g := Int.castRingHom K) (30 : ℤ)
    (by simpa only [map_ofNat] using h30)
  let φ : PolyBase →+* K := Polynomial.eval₂RingHom baseMap z
  let ε : PolyBase[X] →+* K := Polynomial.eval₂RingHom φ u
  have hx₀ : φ x₀ = z := Polynomial.eval₂_X _ _
  have hZ : ε Z = z := by
    change (C x₀).eval₂ φ u = z
    rw [Polynomial.eval₂_C, hx₀]
  have hU : ε U = u := Polynomial.eval₂_X _ _
  have hεF : ε F = 0 := by
    change ε (front Z U 0) = 0
    simpa only [front, map_pow, map_mul, map_add, map_sub, map_ofNat, hZ, hU] using hf
  have hεB : ε B = 0 := by
    change ε (bridge1 Z U 0) = 0
    simpa only [bridge1, map_pow, map_mul, map_add, map_sub, map_neg, map_ofNat, hZ, hU] using hb
  have hεG : G.eval₂ φ u = 0 := by
    change ε G = 0
    simp only [G, map_mul, map_add, hεF, hεB, mul_zero, add_zero]
  let χ := AdjoinRoot.lift φ u hεG
  have χv : χ v = 0 := by
    change AdjoinRoot.lift φ u hεG (AdjoinRoot.mk G V) = 0
    rw [AdjoinRoot.lift_mk]
    change ε V = 0
    simp only [V, map_mul, map_add, map_neg, hεF, hεB, mul_zero, add_zero]
  have χx : χ x = z := (AdjoinRoot.lift_of hεG).trans hx₀
  have χy : χ y = u := by
    change AdjoinRoot.lift φ u hεG (AdjoinRoot.mk G U) = u
    rw [AdjoinRoot.lift_mk]
    exact Polynomial.eval₂_X _ _
  have χt : χ (AdjoinRoot.of G t) = z^2 * factorThree z u ρ := by
    change AdjoinRoot.lift φ u hεG (AdjoinRoot.of G t) = _
    rw [AdjoinRoot.lift_of]
    simp only [t, factorThree, map_pow, map_mul, map_add, map_sub, map_ofNat, hx₀]
  have χH : χ H = hTwelve z u ρ := by
    change χ (hTwelve x y 0) = _
    simp only [hTwelve, map_pow, map_mul, map_add, map_sub, map_ofNat, χx, χy]
  simpa only [χt, χH] using
    map_guard_mul_eq_zero_of_monic_projection hG hg hproj base_regular hcert χ χv

theorem zero_chart_excluded_paid {K : Type*} [Field K] (h30 : IsUnit (30 : K))
    {z u v : K} (h₀ : zeroCubic z u v = 0) (h₁ : zeroLaguerre z u v = 0) : False := by
  exact one_ne_zero (cancel_paid h30 (n := 8640) (by decide) (noZero_mul z u v h₀ h₁))

/-- Literal nonzero-tap chart obstruction. The cubic branch takes
precedence at a common root. -/
theorem nonzero_chart_excluded_away_four {K : Type*} [Field K] (h30 : IsUnit (30 : K))
    (hD : (fourExceptionProduct : K) ≠ 0) {z u v : K} (hz : z ≠ 0)
    (hf : front z u v = 0) (hb : bridge1 z u v = 0) (ht : bridge2 z u v = 0)
    (hk : kappa z u v = 0 ∨ terminal z u v = 0) : False := by
  have hprod : (3846112 : K) * 198898968576 * 122267206287360000 *
      6214370355160790146744320000 ≠ 0 := by
    simpa only [fourExceptionProduct, Nat.cast_mul, Nat.cast_ofNat] using hD
  have d₁ : (3846112 : K) ≠ 0 := fun h => hprod (by simp only [h, zero_mul])
  have d₂ : (198898968576 : K) ≠ 0 := fun h => hprod (by simp only [h, mul_zero, zero_mul])
  have d₃ : (122267206287360000 : K) ≠ 0 := fun h => hprod (by simp only [h, mul_zero, zero_mul])
  have d₄ : (6214370355160790146744320000 : K) ≠ 0 := fun h => hprod (by simp only [h, mul_zero])
  by_cases h₃ : factorThree z u v = 0
  · have hH := cancel_paid h30 (n := 576) (by decide) (deriveHThree_mul z u v hb hf h₃)
    have hV := cancel_paid h30 (n := 960) (by decide) (deriveVThree_mul z u v ht hH h₃)
    rcases hk with hk | hterm
    · exact d₁ (by simpa only [mul_one] using noThreeKappa_mul z u v hk hV hH h₃)
    · exact d₂ (by simpa only [mul_one] using noThreeTerminal_mul z u v hterm hV hH h₃)
  · have hguard := mul_ne_zero (pow_ne_zero 2 hz) h₃
    have hproject := cancel_paid h30 (n := 360) (by decide) (project_mul z u v hb hf)
    have h₁₂ := (mul_eq_zero.mp hproject).resolve_left hguard
    have hH := (mul_eq_zero.mp (hTwelve_guard_mul_eq_zero h30 hf hb)).resolve_left hguard
    have hV := cancel_paid h30 (n := 5529600) (by decide) (deriveVTwelve_mul z u v ht hH h₁₂)
    rcases hk with hk | hterm
    · exact d₃ (by simpa only [mul_one] using noTwelveKappa_mul z u v hk hV hH h₁₂)
    · exact d₄ (by simpa only [mul_one] using noTwelveTerminal_mul z u v hterm hV hH h₁₂)

end RKCert.ReviewedNative.SDIRKSixReceipts
