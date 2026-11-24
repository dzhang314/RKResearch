module
public import RKCert.ReviewedNative.FiniteCauchy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Two-endpoint rigidity in every degree m ≥ 4

The proof uses only finite sums in the given field. Its summation-by-parts
identity is the coefficient form of the Jacobi equation for the weight x.
There is no appeal to positivity or to a count of real zeros.
-/
namespace RKCert.ReviewedNative.TwoKnot
variable {K : Type*} [Field K] [CharZero K]
noncomputable section

/-- Formal moment of the coefficient array, with primitive based at zero. -/
def moment {n : ℕ} (c : Fin n → K) (u : K) (k : ℕ) : K :=
  ∑ i : Fin n, c i * u ^ (i.val + k + 1) / (i.val+k+1 : ℕ)

/-- This square shifted Hilbert system uses the same cached finite Cauchy
kernel as the native tree probes, with no legacy tree import. -/
private theorem shifted_hilbert_kernel {n : ℕ} (d : ℕ) (hd : 0 < d) (v : Fin n → K)
    (h : ∀ i : Fin n, ∑ j : Fin n, v j / ((i.val+j.val+d : ℕ) : K) = 0) : v = 0 := by
  let x : Fin n → K := fun i => (i.val : K)
  let y : Fin n → K := fun j => ((j.val + d : ℕ) : K)
  have hx : Function.Injective x := by
    intro i j e
    exact Fin.ext (Nat.cast_injective (R := K) e)
  have hy : Function.Injective y := by
    intro i j e
    have t : i.val+d = j.val+d := Nat.cast_injective (R := K) e
    exact Fin.ext (by omega)
  have val (i j : Fin n) : x i+y j = ((i.val+j.val+d : ℕ) : K) := by
    dsimp [x,y]
    push_cast
    ring
  apply funext
  apply RKResearch.Certified.Graded.cauchy_kernel x y v hx hy
  · intro i j
    rw [val]
    exact Nat.cast_ne_zero.mpr (by omega)
  · simpa only [val] using h

private def μ (c : Fin n → K) (a : K) (k : ℕ) : K := moment c a k

private def ev0 (c : Fin n → K) (a : K) := ∑ i, c i*a^i.val
private def ev1 (c : Fin n → K) (a : K) := ∑ i, c i*(i.val : K)*a^i.val
private def mm (m : ℕ) : K := (m:K)*((m:K)+2)

private def jac {m : ℕ} (c : Fin (m+1) → K) (j : Fin m) :=
  c j.castSucc*(mm m - (j.val:K)*((j.val:K)+2)) +
    c j.succ*((j.val:K)+1)*((j.val:K)+2)

omit [CharZero K] in
private lemma sturm_scalar (i k M a : K) (h1 : i+k+1 ≠ 0) (h2 : i+k+2 ≠ 0) :
    a*(M-i*(i+2))/(i+k+2) + i*(i+1)/(i+k+1) =
    a*(M-k*(k+2))/(i+k+2) + k*(k+1)/(i+k+1) + (1-a)*(i-k) := by
  field_simp; ring

private lemma sturm_id {m : ℕ} (c : Fin (m+1) → K) (a : K) (k : ℕ) :
    μ (jac c) a (k+1) = (mm m - (k:K)*((k:K)+2))*μ c a (k+1)
       + (k:K)*((k:K)+1)*μ c a k + a^(k+1)*(1-a)*(ev1 c a-(k:K)*ev0 c a) := by
  let g (i : Fin (m+1)) := c i*(mm m-(i.val:K)*((i.val:K)+2)) *
                              a^(i.val+k+2) / ((i.val+k+2 : ℕ):K)
  let h (i : Fin (m+1)) := c i*(i.val:K)*((i.val:K)+1) *
                              a^(i.val+k+1) / ((i.val+k+1 : ℕ):K)
  have gl : ∑ j : Fin m, g j.castSucc = ∑ i : Fin (m+1), g i := by
    rw [Fin.sum_univ_castSucc g]; simp [g,mm]
  have hl : ∑ j : Fin m, h j.succ = ∑ i : Fin (m+1), h i := by
    rw [Fin.sum_univ_succ h]; simp [h]
  calc
    μ (jac c) a (k+1) = ∑ j : Fin m, (g j.castSucc + h j.succ) := by
      unfold μ moment
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [jac,g,h,Fin.val_castSucc,Fin.val_succ]
      have ex1 : j.val + (k+1) + 1 = j.val + k + 2 := by omega
      have ex2 : (j.val+1)+k+1 = j.val + k + 2 := by omega
      rw [ex1,ex2]; push_cast; ring
    _ = ∑ i : Fin (m+1), (g i + h i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, gl, hl]
    _ = _ := by
      simp only [μ, moment, ev0, ev1, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib, mul_sub]
      apply Finset.sum_congr rfl
      intro i _
      let I : K := i.val
      let J : K := k
      have h1 : I+J+1 ≠ 0 := by
        change (i.val:K)+(k:K)+1 ≠ 0; norm_cast
      have h2 : I+J+2 ≠ 0 := by
        change (i.val:K)+(k:K)+2 ≠ 0; norm_cast
      have id := sturm_scalar I J (mm m) a h1 h2
      dsimp only [I,J] at id
      dsimp only [g,h]
      simp only [pow_add, pow_one, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
      linear_combination (c i * a^i.val * a^k * a) * id

/-- The full first-endpoint tests force the finite-coefficient Jacobi equation. -/
private lemma jac_zero {m : ℕ} (c : Fin (m+1) → K)
    (h : ∀ k : Fin m, μ c 1 (k.val+1) = 0) : jac c = 0 := by
  apply shifted_hilbert_kernel 2 (by decide)
  intro k
  have e := sturm_id c 1 k.val
  have haux : (k.val:K)*((k.val:K)+1)*μ c 1 k.val = 0 := by
    cases hk : k.val with
    | zero => simp
    | succ j =>
      have hj : j < m := by have hh := k.isLt; omega
      rw [h ⟨j,hj⟩]; ring
  rw [h k, haux] at e
  simpa [μ, moment, add_assoc, add_comm, add_left_comm] using e

omit [CharZero K] in
/-- A sufficiently long sequence of equal primitive moments at a nonzero,
nonunit endpoint forces their common value to vanish. -/
private lemma four_boundary_rows (M a b D E : K) (ha : a ≠ 1)
    (h0 : M*b + a*(1-a)*D = 0)
    (h1 : (M-1)*b + a^2*(1-a)*(D-E) = 0)
    (h2 : (M-2)*b + a^3*(1-a)*(D-2*E) = 0)
    (h3 : (M-3)*b + a^4*(1-a)*(D-3*E) = 0) : b = 0 := by
  by_contra hb
  have e2 : b*(a-1)*(M*a-M+2) = 0 := by
    linear_combination a^2*h0 - 2*a*h1 + h2
  have e3 : b*(a-1)*(2*M*a^2 - M*a - 3*(-a) - M + 3) = 0 := by
    linear_combination 2*a^3*h0 - 3*a^2*h1 + h3
  have nn : b*(a-1) ≠ 0 := mul_ne_zero hb (sub_ne_zero.mpr ha)
  have f := (mul_eq_zero.mp e2).resolve_left nn
  have g := (mul_eq_zero.mp e3).resolve_left nn
  exact ha (by linear_combination (2*a+1)*f - g)

private lemma μ_factor {n : ℕ} (c : Fin n → K) (a : K) (k : ℕ) :
    μ c a (k+1) = a^(k+2) * ∑ j, c j*a^j.val / ((j.val+k+2:ℕ):K) := by
  unfold μ moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have e : j.val+(k+1)+1 = j.val+(k+2) := by omega
  rw [e, pow_add]
  have ee : j.val + (k+2) = j.val+k+2 := by omega
  rw [ee]; ring

/-- A degree-at-most-m polynomial satisfying m right-endpoint x-weighted moment
tests and three second-endpoint x(x-1)-weighted moment tests vanishes. This
strengthens the m−1 second-endpoint tests in the flat-band source. -/
theorem twoEndpointJacobi {m : ℕ} (hm : 4 ≤ m) (c : Fin (m+1) → K)
    (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (first : ∀ k : Fin m, moment c 1 (k.val+1) = 0)
    (second : ∀ k : Fin 3, moment c a (k.val+2) = moment c a (k.val+1)) :
    c = 0 := by
  have hz := jac_zero c first
  have stepIdentity (k : ℕ) : (mm m-(k:K)*((k:K)+2))*μ c a (k+1) +
      (k:K)*((k:K)+1)*μ c a k + a^(k+1)*(1-a)*(ev1 c a-(k:K)*ev0 c a) = 0 := by
    rw [← sturm_id, hz]
    simp [μ,moment]
  let b := μ c a 1
  have e1 : μ c a 2 = b := second 0
  have e2 : μ c a 3 = b := (second 1).trans e1
  have e3 : μ c a 4 = b := (second 2).trans e2
  have z : b = 0 := by
    apply four_boundary_rows (mm m) a b (ev1 c a) (ev0 c a) ha1
    · simpa [b] using stepIdentity 0
    · have e := stepIdentity 1
      norm_num only [Nat.cast_one, Nat.reduceAdd, one_mul, Nat.reducePow, Nat.cast_ofNat] at e
      rw [e1] at e; change _ * b + _ * b + _ = 0 at e
      linear_combination e
    · have e := stepIdentity 2
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at e
      rw [e2,e1] at e; linear_combination e
    · have e := stepIdentity 3
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at e
      rw [e3,e2] at e; linear_combination e
  have hD : ev1 c a = 0 := by
    have e := stepIdentity 0
    change μ c a 1 = 0 at z
    simpa [z, ha, sub_ne_zero.mpr ha1.symm] using e
  have hE : ev0 c a = 0 := by
    have e := stepIdentity 1
    have e1z : μ c a 1 = 0 := z
    have e2z := e1.trans z
    simpa [e1z,e2z,hD,ha, sub_ne_zero.mpr ha1.symm] using e
  have allμ (k : ℕ) (hk : k < m) : μ c a (k+1) = 0 := by
    induction k with
    | zero => exact z
    | succ k ih =>
      have prev := ih (by omega)
      have e := stepIdentity (k+1)
      rw [prev,hD,hE] at e
      have hcoef : (mm m : K) - (↑(k+1):K)*((↑(k+1):K)+2) ≠ 0 := by
        have hn : m*(m+2) ≠ (k+1)*(k+1+2) := by nlinarith
        dsimp [mm]
        apply sub_ne_zero.mpr
        exact_mod_cast hn
      simp only [mul_zero, sub_zero, add_zero] at e
      exact (mul_eq_zero.mp e).resolve_left hcoef
  have unitSum (k : Fin m) :
      ∑ j : Fin (m+1), c j / ((j.val+k.val+2:ℕ):K) = 0 := by
    have e := first k; change μ c 1 (k.val+1) = 0 at e
    simpa [μ_factor] using e
  have scaledSum (k : Fin m) :
      ∑ j : Fin (m+1), c j*a^j.val / ((j.val+k.val+2:ℕ):K) = 0 := by
    have e := allμ k.val k.isLt
    rw [μ_factor] at e
    exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ ha)
  let v : Fin m → K := fun j => c j.succ*(a^(j.val+1)-1)
  have vz : v = 0 := by
    apply shifted_hilbert_kernel 3 (by decide)
    intro k
    have zsum : ∑ j : Fin (m+1), (c j*(a^j.val-1) / ((j.val+k.val+2:ℕ):K)) = 0 := by
      simp_rw [mul_sub, mul_one, sub_div]
      rw [Finset.sum_sub_distrib, scaledSum, unitSum, sub_self]
    rw [Fin.sum_univ_succ] at zsum
    simp only [Fin.val_zero, pow_zero, sub_self, mul_zero, zero_div, zero_add] at zsum
    convert zsum using 1
    apply Finset.sum_congr rfl
    intro j _
    change c j.succ * (a^(j.val+1)-1) / _ = _
    congr 2
    simp only [Fin.val_succ]
    omega
  let i0 : Fin m := ⟨0, by omega⟩
  have c1 : c i0.succ = 0 := by
    have e := congrFun vz i0
    change c i0.succ*(a^(0+1)-1) = 0 at e
    simpa [sub_ne_zero.mpr ha1] using e
  have c0 : c 0 = 0 := by
    have e := congrFun hz i0
    change jac c i0 = 0 at e
    unfold jac at e
    rw [c1] at e
    have hi0 : i0.val = 0 := rfl
    have hiC : i0.castSucc = 0 := Fin.ext (by simp [i0])
    have mpos : (m:K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have mpos2 : (m:K)+2 ≠ 0 := by norm_cast
    simpa [hi0,hiC,mm,mpos,mpos2] using e
  have tail : (fun j : Fin m => c j.succ) = 0 := by
    apply shifted_hilbert_kernel 3 (by decide)
    intro k
    have e := unitSum k
    rw [Fin.sum_univ_succ] at e
    simp only [c0,zero_div,zero_add] at e
    convert e using 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    simp only [Fin.val_succ]
    omega
  exact funext (Fin.cases c0 (fun j => congrFun tail j))


section Physical
variable {n : ℕ}

/-- Coefficients of P(ux) when c are the coefficients of P. -/
private def rescale (c : Fin n → K) (u : K) : Fin n → K := fun i => c i * u^i.val

private theorem moment_rescale (c : Fin n → K) (u r : K) (k : ℕ) :
    moment c (u*r) k = u^(k+1)*moment (rescale c u) r k := by
  simp only [moment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [rescale,mul_pow,pow_add,div_eq_mul_inv]
  ring

omit [CharZero K] in
private theorem rescale_eq_zero_iff (c : Fin n → K) {u : K} (hu : u ≠ 0) :
    rescale c u = 0 ↔ c = 0 := by
  constructor
  · intro h
    ext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_right (pow_ne_zero _ hu)
  · rintro rfl
    ext i; simp [rescale]

/-- The generic algebraic Jacobi gate at arbitrary physical knots, without
silently replacing the two endpoints by a positive ordered interval. -/
theorem physical_jacobi_gate {m : ℕ} (hm : 4≤m) (e : Fin (m+1) → K)
    (u v : K) (hu : u≠0) (hv : v≠0) (hvu : v≠u)
    (h1 : ∀ k : Fin m,moment e u (k.val+1)=0)
    (h2 : ∀ k : Fin 3,moment e v (k.val+2)=u*moment e v (k.val+1)) : e=0 := by
  let f := rescale e u
  apply (rescale_eq_zero_iff e hu).mp
  apply twoEndpointJacobi hm _ (v/u) (div_ne_zero hv hu) (fun h => hvu ((div_eq_one_iff_eq hu).mp h))
  · intro k
    have h := moment_rescale e u 1 (k.val+1)
    rw [mul_one,h1 k] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hu)
  · intro k
    have vu : u*(v/u)=v := by field_simp
    have scale (t : ℕ) : moment e v t=u^(t+1)*moment f (v/u) t := by
      simpa only [vu] using moment_rescale e u (v/u) t
    have h := h2 k
    rw [scale,scale,pow_succ u (k.val+2)] at h
    have hz : (u^(k.val+2)*u)*(moment f (v/u) (k.val+2)-moment f (v/u) (k.val+1))=0 := by
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero (pow_ne_zero _ hu) hu))

end Physical
end
end RKCert.ReviewedNative.TwoKnot

