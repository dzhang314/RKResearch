module

public import RKCert.ReviewedNative.FiniteOrderCheck
public import RKCert.ReviewedNative.ChangeCoefficients

@[expose] public section

/-! # Denominator-cleared, sparse native order checking

Literal finite tableau evaluation can be replaced by any *proved* matrix
action and weighted output. Since a reviewed stage column is homogeneous
of degree one less than its tree order, ordinary order conditions can then
be replayed on the exact integer numerators rather than repeatedly reducing
fractions. Both extensions keep the reviewed `Φ` and `HasOrder` unchanged. -/

namespace RKResearch.Certified

open FiniteRootedTree
open scoped Matrix FiniteRootedTree

section Replay

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Native elementary vectors, using a supplied stage action. -/
def replayStage (act : (ι → R) → (ι → R)) : FiniteRootedTree → (ι → R)
  | .leaf => 1
  | .butcherProduct t u => replayStage act t * act (replayStage act u)

theorem replayStage_eq {A : Matrix ι ι R} {act : (ι → R) → (ι → R)}
    (hact : ∀ v, act v = A *ᵥ v) (t : FiniteRootedTree) :
    replayStage act t = Φ t A := by
  induction t with
  | leaf => rfl
  | butcherProduct t u ht hu => simp only [replayStage, Φ, ht, hu, hact]

/-- The paid numerator equation at each tree of at most order `p`.
The exponent is determined by the reviewed constructor's order. -/
def checkScaledOrder [DecidableEq R] (act : (ι → R) → (ι → R)) (out : (ι → R) → R)
    (stageScale weightScale : R) (p : ℕ) : Bool :=
  (List.range p).all fun n => (treesOfOrderSucc n).all fun t =>
    decide ((t.factorial : R) * out (replayStage act t) =
      weightScale * stageScale^((t.order : ℕ)-1))

theorem checkScaledOrder_spec [DecidableEq R] {A : Matrix ι ι R} {b : ι → R}
    {act : (ι → R) → (ι → R)} {out : (ι → R) → R}
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (d e : R) (p : ℕ) :
    checkScaledOrder act out d e p = true ↔
      ∀ t : FiniteRootedTree, (t.order : ℕ) ≤ p →
        (t.factorial : R) * (b ⬝ᵥ Φ t A) = e * d^((t.order:ℕ)-1) := by
  simp only [checkScaledOrder, List.all_eq_true, List.mem_range, mem_treesOfOrderSucc,
    decide_eq_true_eq, hout, replayStage_eq hact]
  constructor
  · intro h t ht
    have hpos := t.order.pos
    exact h ((t.order : ℕ)-1) (by omega) t (by omega)
  · intro h n hn t ht
    exact h t (by omega)

/-- Each primitive attachment introduces exactly one matrix scaling factor. -/
theorem Φ_matrix_smul (A : Matrix ι ι R) (z : R) (t : FiniteRootedTree) :
    Φ t (z • A) = z^((t.order:ℕ)-1) • Φ t A := by
  induction t with
  | leaf => simp [Φ, order]
  | butcherProduct t u ht hu =>
    have step : ((t ◂ u).order:ℕ)-1 =
        ((t.order:ℕ)-1) + (1+((u.order:ℕ)-1)) := by
      have ht := t.order.pos
      have hu := u.order.pos
      simp only [order, PNat.add_coe]
      omega
    simp only [step, Φ, ht, hu, Matrix.smul_mulVec, Matrix.mulVec_smul, pow_add, pow_one]
    funext i
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ac_rfl

end Replay

private theorem cancel_scaled {R : Type*} [CommMonoid R] {a d e v : R}
    (hd : IsUnit d) (he : IsUnit e) (h : a * (d * (e * v)) = e*d) : a*v=1 := by
  apply (he.mul hd).mul_left_cancel
  rw [mul_one]
  exact (by ac_rfl : e*d*(a*v) = a*(d*(e*v))).trans h

section Transport

variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S]
variable {A : Matrix ι ι R} {b : ι → R} {U : Matrix ι ι S} {w : ι → S}

/-- Transport exact numerator equations to ordinary reviewed order. It is
enough that the two normalization factors map to units; the coefficient map
need not be injective. No separate characteristic condition is introduced. -/
theorem hasOrder_of_scaled_moments (f : R →+* S) {d e : R} {p : ℕ}
    (hA : A.map f = f d • U) (hb : f ∘ b = f e • w)
    (hd : IsUnit (f d)) (he : IsUnit (f e))
    (h : ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ p →
      (t.factorial : R) * (b ⬝ᵥ Φ t A) = e*d^((t.order:ℕ)-1)) :
    HasOrder p U w := by
  intro t ht
  have hn := congrArg f (h t ht)
  simp only [map_mul, map_pow, map_natCast, RingHom.map_dotProduct, map_Φ_coefficients,
    hA, hb, Φ_matrix_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at hn
  exact cancel_scaled (hd.pow _) he hn

/-- The checked sparse evaluator plus scalar units certifies a native order witness. -/
theorem hasOrder_of_scaled_check [DecidableEq R] (f : R →+* S) {d e : R} {p : ℕ}
    {act : (ι → R) → (ι → R)} {out : (ι → R) → R}
    (hact : ∀ v, act v = A *ᵥ v) (hout : ∀ v, out v = b ⬝ᵥ v)
    (hA : A.map f = f d • U) (hb : f ∘ b = f e • w)
    (hd : IsUnit (f d)) (he : IsUnit (f e))
    (h : checkScaledOrder act out d e p = true) : HasOrder p U w :=
  hasOrder_of_scaled_moments f hA hb hd he ((checkScaledOrder_spec hact hout d e p).mp h)

end Transport

end RKResearch.Certified
