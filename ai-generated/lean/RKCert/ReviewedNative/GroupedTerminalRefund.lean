import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace RKResearch.Certified.GroupedTerminalRefund

open Module

section ClockFrame

variable {K : Type*} [Field K]

noncomputable def coefficients {d : ℕ} (a : Fin d → K) : Polynomial K :=
  ∑ i : Fin d, Polynomial.monomial i.val (a i)

private theorem coefficients_at {d : ℕ} (a : Fin d → K) (i : Fin d) :
    (coefficients a).coeff i.val = a i := by
  classical
  change Polynomial.lcoeff K i.val (coefficients a) = _
  rw [coefficients, map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Polynomial.coeff_monomial, Ne.symm (fun h => hj (Fin.ext h))]
  · simp

private theorem coefficients_deg {d : ℕ} (hd : 0 < d) (a : Fin d → K) :
    (coefficients a).natDegree < d := by
  classical
  have hle : (coefficients a).natDegree ≤ d-1 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _ fun i _ =>
      (Polynomial.natDegree_monomial_le _).trans (by have := i.isLt; omega)
  omega

private theorem coefficients_eval {d : ℕ} (c : Fin d → K) (t : K) :
    (coefficients c).eval t = ∑ i : Fin d, c i * t ^ i.val := by
  change Polynomial.evalRingHom t (coefficients c) = _
  rw [coefficients, map_sum]
  simp

/-- Degree-at-most-`d` forward tests vanishing at the protected clock. -/
noncomputable def clockFrame {n d : ℕ} (x : Fin n → K) (v : K) :
    (Fin d → K) →ₗ[K] (Fin n → K) where
  toFun c i := (x i - v) * (coefficients c).eval (x i)
  map_add' a b := by
    ext i
    change (x i - v) * (coefficients (a+b)).eval (x i) =
      (x i - v) * (coefficients a).eval (x i) + (x i - v) * (coefficients b).eval (x i)
    simp only [coefficients_eval, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' a b := by
    ext i
    change (x i - v) * (coefficients (a • b)).eval (x i) =
      a * ((x i - v) * (coefficients b).eval (x i))
    rw [coefficients_eval, coefficients_eval]
    have h : (∑ j : Fin d, (a • b) j * x i ^ j.val) =
        a * ∑ j : Fin d, b j * x i ^ j.val := by
      rw [Finset.mul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [h, mul_left_comm]

/-- Seven-dimensional (or `d`-dimensional) non-port clock frame. -/
theorem clockFrame_injective {n d : ℕ} (hd : 0 < d) (hs : d ≤ n)
    (x : Fin n → K) (v : K) (hx : Function.Injective x)
    (hv : ∀ i, x i ≠ v) : Function.Injective (clockFrame (d := d) x v) := by
  classical
  intro a b hab
  let p := coefficients (a - b)
  have hz : clockFrame x v (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  have hr (i : Fin n) : p.eval (x i) = 0 := by
    have hi := congrFun hz i
    change (x i - v) * p.eval (x i) = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (sub_ne_zero.mpr (hv i))
  have hp : p = 0 := by
    by_contra hpn
    have hm : (Finset.univ.image x).val ⊆ p.roots := by
      intro y hy
      have hy' : y ∈ Finset.univ.image x := hy
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hy'
      rw [← hi]
      exact (Polynomial.mem_roots hpn).mpr (hr i)
    have h1 := Polynomial.card_le_degree_of_subset_roots hm
    have h2 := coefficients_deg hd (a-b)
    change p.natDegree < d at h2
    rw [Finset.card_image_of_injective _ hx, Finset.card_univ, Fintype.card_fin] at h1
    omega
  funext i
  have hc := congrArg (fun q : Polynomial K => q.coeff i.val) hp
  simpa only [p, coefficients_at, Polynomial.coeff_zero,
    Pi.sub_apply, sub_eq_zero] using hc

end ClockFrame

section Refund

variable {K X H Z Y V : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup H] [Module K H]
  [AddCommGroup Z] [Module K Z] [AddCommGroup Y] [Module K Y]
  [AddCommGroup V] [Module K V] [FiniteDimensional K X] [FiniteDimensional K Z]

/-- The terminal linear combinations killing every allowed mixed discrepancy. -/
def refunded (F : H →ₗ[K] X) (T : Module.Dual K X →ₗ[K] Z) :
    Submodule K (Module.Dual K Z) :=
  (F.dualMap.ker.map T).dualAnnihilator

/-- The mixed tests force at least `terminal dimension - nodal codimension`
    independent next-grade reverse measurements. No use of weight signs. -/
theorem refund_rank [FiniteDimensional K H] {F : H →ₗ[K] X}
    (hF : Function.Injective F) (T : Module.Dual K X →ₗ[K] Z) :
    finrank K Z ≤
      finrank K (refunded F T) + (finrank K X - finrank K H) := by
  have hsur := LinearMap.dualMap_surjective_of_injective hF
  have h1 := LinearMap.finrank_range_add_finrank_ker F.dualMap
  rw [LinearMap.range_eq_top.mpr hsur, _root_.finrank_top,
    Subspace.dual_finrank_eq, Subspace.dual_finrank_eq] at h1
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq (F.dualMap.ker.map T)
  have h3 := Submodule.finrank_map_le (f := T) (F.dualMap.ker)
  change finrank K Z ≤ finrank K (F.dualMap.ker.map T).dualAnnihilator +
    (finrank K X - finrank K H)
  omega

omit [FiniteDimensional K X] [FiniteDimensional K Z] in
/-- The actual primitive step pays the refunded combinations; the clock
    step is already exact before taking combinations. The meanings of
    `A`, `C`, and `M` are the actual reverse primitive, clock, and means. -/
theorem refunded_word_steps (F : H →ₗ[K] X) (T : Module.Dual K X →ₗ[K] Z)
    (A C : V →ₗ[K] V) (M : V →ₗ[K] Z) (a : Y →ₗ[K] V)
    (idealA idealC : Y →ₗ[K] Z) (err : Y →ₗ[K] Module.Dual K X)
    (hpair : ∀ w, F.dualMap (err w) = 0)
    (hA : ∀ w, M (A (a w)) - idealA w = T (err w))
    (hC : ∀ w, M (C (a w)) = idealC w)
    (l : refunded F T) (w : Y) :
    l.1 (M (A (a w))) = l.1 (idealA w) ∧
      l.1 (M (C (a w))) = l.1 (idealC w) := by
  have hz : l.1 (T (err w)) = 0 :=
    (Submodule.mem_dualAnnihilator l.1).mp l.2 _
      ⟨err w, hpair w, rfl⟩
  rw [← hA w, map_sub, sub_eq_zero] at hz
  exact ⟨hz, congrArg l.1 (hC w)⟩

end Refund

section Packet

variable {K V U W H : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H]

/-- One step of the paid commutator packet. A decoded lead survives,
    and the later packet is carried by an injective physical commutator. -/
theorem packet_step {P : V →ₗ[K] V} (hP : Function.Injective P)
    {e : U →ₗ[K] V} {f : W →ₗ[K] V} (hf : Function.Injective f)
    {D : V →ₗ[K] H} (he : Function.Injective (D.comp e))
    (hz : D.comp (P.comp f) = 0) :
    Function.Injective (e.coprod (P.comp f)) := by
  intro a b h
  have qab : e a.1 + P (f a.2) = e b.1 + P (f b.2) := h
  have za : D (P (f a.2)) = 0 := LinearMap.congr_fun hz a.2
  have zb : D (P (f b.2)) = 0 := LinearMap.congr_fun hz b.2
  have q1 : a.1 = b.1 := he <| by
    simpa only [map_add, za, zb, add_zero, LinearMap.comp_apply] using congrArg D qab
  have q2 : a.2 = b.2 := hf (hP (add_left_cancel (q1 ▸ qab)))
  exact Prod.ext q1 q2

variable {U0 U1 U2 U3 H0 H1 H2 : Type*}
  [AddCommGroup U0] [Module K U0] [FiniteDimensional K U0]
  [AddCommGroup U1] [Module K U1] [FiniteDimensional K U1]
  [AddCommGroup U2] [Module K U2] [FiniteDimensional K U2]
  [AddCommGroup U3] [Module K U3] [FiniteDimensional K U3]
  [AddCommGroup H0] [Module K H0] [AddCommGroup H1] [Module K H1]
  [AddCommGroup H2] [Module K H2] [FiniteDimensional K V]

/-- The four blocks at polynomial sizes `8,6,4,2`. The size-eight
    block contains just the genuinely measured highest-grade targets. -/
theorem four_block_floor {P : V →ₗ[K] V} (hP : Function.Injective P)
    {e0 : U0 →ₗ[K] V} {e1 : U1 →ₗ[K] V} {e2 : U2 →ₗ[K] V}
    {e3 : U3 →ₗ[K] V} (h3 : Function.Injective e3)
    {D0 : V →ₗ[K] H0} {D1 : V →ₗ[K] H1} {D2 : V →ₗ[K] H2}
    (h0 : Function.Injective (D0.comp e0)) (h1 : Function.Injective (D1.comp e1))
    (h2 : Function.Injective (D2.comp e2))
    (z01 : ∀ a, D0 (P (e1 a)) = 0)
    (z02 : ∀ a, D0 (P (P (e2 a))) = 0)
    (z03 : ∀ a, D0 (P (P (P (e3 a)))) = 0)
    (z12 : ∀ a, D1 (P (e2 a)) = 0)
    (z13 : ∀ a, D1 (P (P (e3 a))) = 0)
    (z23 : ∀ a, D2 (P (e3 a)) = 0) :
    finrank K U0 + finrank K U1 + finrank K U2 + finrank K U3 ≤ finrank K V := by
  let f2 := e2.coprod (P.comp e3)
  have hf2 : Function.Injective f2 := packet_step hP h3 h2 <| by
    exact LinearMap.ext z23
  let f1 := e1.coprod (P.comp f2)
  have hf1 : Function.Injective f1 := packet_step hP hf2 h1 <| by
    apply LinearMap.ext
    rintro ⟨a,b⟩
    change D1 (P (e2 a + P (e3 b))) = 0
    simp only [map_add, z12, z13, add_zero]
  have hf0 : Function.Injective (e0.coprod (P.comp f1)) :=
    packet_step hP hf1 h0 <| by
      apply LinearMap.ext
      rintro ⟨a,b,c⟩
      change D0 (P (e1 a + P (e2 b + P (e3 c)))) = 0
      simp only [map_add, z01, z02, z03, add_zero]
  have hb := LinearMap.finrank_le_finrank_of_injective hf0
  simp only [Module.finrank_prod] at hb
  omega

end Packet

/-- One literal shared port, `n - t` new representatives, and the actual
    reverse readout packet. `g=7` and `lo=12` give the order-15 chart. -/
theorem grouped_count (n t old d lo g front : ℕ)
    (ht : t ≤ n) (hn : g < n)
    (hrefund : t ≤ d + (n - 1 - g)) (hpacket : lo + d ≤ old) :
    front + lo + g ≤ front + old + (n - t) - 1 := by
  omega

theorem no_thirty_three (n t old d : ℕ) (ht : t ≤ n) (hn : 8 ≤ n)
    (hrefund : t ≤ d + (n - 8)) (hpacket : 12 + d ≤ old) :
    34 ≤ 15 + old + (n - t) - 1 := by
  omega

theorem no_twenty_five (n t old d : ℕ) (ht : t ≤ n) (hn : 7 ≤ n)
    (hrefund : t ≤ d + (n - 7)) (hpacket : 9 + d ≤ old) :
    26 ≤ 11 + old + (n - t) - 1 := by
  omega

/-- If the top residual has already saturated all its independent
    evaluations, take those evaluations outright, not an overcomplete
    list of terminal functionals. The protected port is disjoint. -/
theorem saturated_terminal_count (n t old front lo g : ℕ)
    (ht : t < n) (hpacket : lo + g ≤ old) :
    front + lo + g ≤ front + old + (n - t) - 1 := by
  omega

end RKResearch.Certified.GroupedTerminalRefund
