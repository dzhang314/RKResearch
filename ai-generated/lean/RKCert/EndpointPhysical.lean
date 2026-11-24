module

public import RKCert.PolynomialEndpointMoments

@[expose] public section
/-! Normalization of actual chronological clocks for shared generic endpoint moments.
The base scalar lemmas live in RKCert.PolynomialEndpointMoments and are not duplicated. -/
namespace RKCert.EndpointPhysical
open RKCert.Endpoint
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- Coefficients of P(ux) when c are the coefficients of P. -/
def rescale (c : Fin n → K) (u : K) : Fin n → K := fun i => c i * u^i.val

/-- Physical, rather than unit-normalized, first and second endpoint tests. -/
def tests (c : Fin n → K) (u v : K) (d : ℕ) : Prop :=
  (∀ k : Fin d, moment c u (k.val+1) = 0) ∧
  (moment c v 2 - u*moment c v 1 = 0) ∧
  (moment c v 3 - u*moment c v 2 = 0)

theorem moment_rescale (c : Fin n → K) (u r : K) (k : ℕ) :
    moment c (u*r) k = u^(k+1)*moment (rescale c u) r k := by
  simp only [moment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rescale,mul_pow,pow_add,div_eq_mul_inv]
  ring

/-- Convert two genuine physical pivots to the shared normalized moment API. -/
theorem normalize {c : Fin n → K} {u v : K} {d : ℕ} (hu : u ≠ 0) (h : tests c u v d) :
    twoTests (rescale c u) (v/u) d := by
  let m := moment (rescale c u)
  have vu : u*(v/u) = v := by field_simp
  have hvr (j : ℕ) : moment c v j = u^(j+1)*m (v/u) j := by
    simpa only [vu] using moment_rescale c u (v/u) j
  have f (k : Fin d) : m 1 (k.val+1) = 0 := by
    have w := moment_rescale c u 1 (k.val+1)
    rw [mul_one,h.1 k] at w
    exact (mul_eq_zero.mp w.symm).resolve_left (pow_ne_zero _ hu)
  have z (j : ℕ) (w : moment c v (j+1)-u*moment c v j = 0) :
      m (v/u) (j+1)-m (v/u) j = 0 := by
    rw [hvr,hvr,pow_succ u (j+1)] at w
    have ww : (u^(j+1)*u)*(m (v/u) (j+1)-m (v/u) j) = 0 := by linear_combination w
    exact (mul_eq_zero.mp ww).resolve_left (mul_ne_zero (pow_ne_zero _ hu) hu)
  exact ⟨f,z 1 h.2.1,z 2 h.2.2⟩

omit [CharZero K] in
theorem rescale_eq_zero_iff (c : Fin n → K) {u : K} (hu : u ≠ 0) :
    rescale c u = 0 ↔ c = 0 := by
  constructor
  · intro h
    ext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_right (pow_ne_zero _ hu)
  · rintro rfl
    ext i; simp [rescale]

/-- Characteristic-zero absolute quartic rule used at the DIRK order-18/19 frontier. -/
theorem match4 (c : Fin 5 → K) (u v : K) (hu : u ≠ 0) (hv : v ≠ 0) (hvu : v ≠ u)
    (h : tests c u v 4) : c = 0 :=
  (rescale_eq_zero_iff c hu).mp <| Endpoint.match4 _ _ (div_ne_zero hv hu)
    (fun e => hvu ((div_eq_one_iff_eq hu).mp e)) (normalize hu h)

end RKCert.EndpointPhysical

