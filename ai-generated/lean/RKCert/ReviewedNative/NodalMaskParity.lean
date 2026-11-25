module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-! # The shared paid polynomial-mask argument

Multiplying a clock packet by a nonzero polynomial is an injective
coefficient change into a wider paid packet.  A degree d mask takes d units
of grade and d units of clock testing budget.  This abstract argument works
for both stage columns and weighted output covectors.
-/

namespace RKResearch.Certified.Graded
open Module Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Evaluation of every polynomial through degree q under a specified
linear clock evaluator. -/
def polyClockBand (L : K[X] →ₗ[K] V) (q : ℕ) : Submodule K V :=
  (degreeLT K (q+1)).map L

theorem polyClockBand_mono (L : K[X] →ₗ[K] V) {q r : ℕ} (h : q ≤ r) :
    polyClockBand L q ≤ polyClockBand L r :=
  Submodule.map_mono (degreeLT_mono (by omega))

/-- A masked block is the space of evaluations of the polynomials P Q
with deg Q ≤ q, not a change to the underlying tableau or order. -/
def maskedPolyClockBand (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) : Submodule K V :=
  polyClockBand (L.comp (LinearMap.mulLeft K P)) q

private theorem degreeLT_mul_mask (P Q : K[X]) {q : ℕ}
    (hQ : Q ∈ degreeLT K (q+1)) : P*Q ∈ degreeLT K (q+P.natDegree+1) := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE] at hQ ⊢
  have hv := natDegree_le_of_degree_le hQ
  apply degree_le_of_natDegree_le
  exact natDegree_mul_le.trans (by omega)

theorem maskedPolyClockBand_le (L : K[X] →ₗ[K] V) (P : K[X]) (q : ℕ) :
    maskedPolyClockBand L P q ≤ polyClockBand L (q+P.natDegree) := by
  rintro _ ⟨Q,hQ,rfl⟩
  exact ⟨P*Q,degreeLT_mul_mask P Q hQ,rfl⟩

theorem finrank_maskedPolyClockBand (L : K[X] →ₗ[K] V) (P : K[X]) (hP : P ≠ 0)
    (q : ℕ) (hinj : Function.Injective (L.comp (degreeLT K (q+P.natDegree+1)).subtype)) :
    finrank K (maskedPolyClockBand L P q) = q+1 := by
  let W := degreeLT K (q+1)
  let g : W →ₗ[K] V := (L.comp (LinearMap.mulLeft K P)).comp W.subtype
  have hg : Function.Injective g := by
    intro u v huv
    let u' : degreeLT K (q+P.natDegree+1) :=
      ⟨P*(u : K[X]),degreeLT_mul_mask P u u.property⟩
    let v' : degreeLT K (q+P.natDegree+1) :=
      ⟨P*(v : K[X]),degreeLT_mul_mask P v v.property⟩
    have h : u' = v' := hinj huv
    exact Subtype.ext (mul_left_cancel₀ hP (congrArg Subtype.val h))
  have hband : g.range = maskedPolyClockBand L P q := by
    dsimp only [g,W,maskedPolyClockBand,polyClockBand]
    rw [LinearMap.range_comp,Submodule.range_subtype]
  rw [← hband,LinearMap.finrank_range_of_inj hg]
  exact (degreeLTEquiv K (q+1)).finrank_eq.trans (Module.finrank_fin_fun K)

/-- A common interface for a primal or dual clock system supplied by paid
reviewed order.  Separation is for the *entire* augmented clock band. -/
structure PaidPolyClockSystem (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (E : ℕ → Submodule K V) (p : ℕ) : Prop where
  step_injective : Function.Injective T
  band_injective : ∀ q, 2*q+1 ≤ p → Function.Injective (L.comp (degreeLT K (q+1)).subtype)
  band_le : ∀ j q, q ≤ j → q+j+1 ≤ p → polyClockBand L q ≤ E j
  step_le : ∀ j, j+3 ≤ p → (E j).map T ≤ E (j+2)
  separated : ∀ j q, q ≤ j+2 → q+j+3 ≤ p → polyClockBand L q ⊓ (E j).map T = ⊥

private abbrev clockBudget (m r : ℕ) := min r (m-1-r)

/-- The actual masked parity packet: successive blocks act on the
polynomial multiples by powers of T, starting with T^0. -/
def maskedParityPacket (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V) (P : K[X]) (m : ℕ) :
    ℕ → Submodule K V
  | 0 => maskedPolyClockBand L P 0
  | 1 => maskedPolyClockBand L P (min 1 (m-2))
  | r+2 => maskedPolyClockBand L P (min (r+2) (m-1-(r+2))) ⊔
      (maskedParityPacket L T P m r).map T

private theorem effective_block {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) {m r : ℕ} (hscale : p = m+2*P.natDegree) (hr : r+1 ≤ m) :
    finrank K (maskedPolyClockBand L P (clockBudget m r)) = clockBudget m r+1 ∧
    maskedPolyClockBand L P (clockBudget m r) ≤ E (r+P.natDegree) := by
  have h₁ : clockBudget m r ≤ r := Nat.min_le_left _ _
  have h₂ : clockBudget m r ≤ m-1-r := Nat.min_le_right _ _
  refine ⟨finrank_maskedPolyClockBand L P hP _
    (sys.band_injective _ (by omega)),?_⟩
  exact (maskedPolyClockBand_le L P _).trans (sys.band_le _ _ (by omega) (by omega))

variable [FiniteDimensional K V]

/-- The shifted packet has exactly the effective parity rank and lies in
the actual unmasked paid flag at the shifted grade.  The proof splits off
its full-rank polynomial block disjointly at each step. -/
theorem maskedParityPacket_rank_and_le {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) {m : ℕ} (hscale : p = m+2*P.natDegree) :
    ∀ r, r+1 ≤ m → finrank K (maskedParityPacket L T P m r) = parityCensus m r ∧
      maskedParityPacket L T P m r ≤ E (r+P.natDegree)
  | 0, hr => by
      have h := effective_block sys P hP hscale (r := 0) hr
      have eq : clockBudget m 0 = 0 := Nat.zero_min _
      rw [eq] at h
      exact h
  | 1, hr => by
      have h := effective_block sys P hP hscale (r := 1) hr
      have eq : clockBudget m 1 = min 1 (m-2) := by
        change min 1 (m-1-1) = min 1 (m-2)
        rw [show m-1-1 = m-2 by omega]
      rw [eq] at h
      exact h
  | r+2, hr => by
      let w := clockBudget m (r+2)
      let U := maskedPolyClockBand L P w
      let W := maskedParityPacket L T P m r
      let d := P.natDegree
      obtain ⟨hU,hUs⟩ := effective_block sys P hP hscale hr
      obtain ⟨hW,hWs⟩ := maskedParityPacket_rank_and_le sys P hP hscale r (by omega)
      have hw₁ : w ≤ r+2 := Nat.min_le_left _ _
      have hw₂ : w ≤ m-1-(r+2) := Nat.min_le_right _ _
      have hpay : w+d+(r+d)+3 ≤ p := by
        change p = m+2*d at hscale
        omega
      have hUW : U ⊓ W.map T = ⊥ := by
        have hb : U ≤ polyClockBand L (w+d) := maskedPolyClockBand_le L P w
        have hsep := sys.separated (r+d) (w+d) (by omega) hpay
        exact le_antisymm ((inf_le_inf hb (Submodule.map_mono hWs)).trans hsep.le) bot_le
      let e : V ≃ₗ[K] V := LinearEquiv.ofBijective T
        ⟨sys.step_injective,LinearMap.surjective_of_injective sys.step_injective⟩
      have hm : finrank K (W.map T) = finrank K W := e.finrank_map_eq W
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq U (W.map T)
      change finrank K U = w+1 at hU
      change finrank K W = parityCensus m r at hW
      rw [hUW,finrank_bot,add_zero,hm,hU,hW] at hdim
      have hf : W.map T ≤ E (r+2+d) := by
        have hp : r+d+3 ≤ p := by omega
        rw [show r+2+d = r+d+2 by omega]
        exact (Submodule.map_mono hWs).trans (sys.step_le (r+d) hp)
      change finrank K (↥(U ⊔ W.map T : Submodule K V)) = w+1+parityCensus m r ∧ (U ⊔ W.map T) ≤ E (r+2+d)
      exact ⟨hdim,sup_le hUs hf⟩

/-- Both causal cutoff directions use this single invariant target
argument. The seed condition refers to all polynomial multiples; the
target need not be a coordinate subspace. -/
theorem maskedParityPacket_le_invariant (L : K[X] →ₗ[K] V) (T : V →ₗ[K] V)
    (P : K[X]) (m : ℕ) (U : Submodule K V)
    (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U) :
    ∀ r, maskedParityPacket L T P m r ≤ U
  | 0 => by rintro _ ⟨Q,_,rfl⟩; exact hseed Q
  | 1 => by rintro _ ⟨Q,_,rfl⟩; exact hseed Q
  | r+2 => sup_le (by rintro _ ⟨Q,_,rfl⟩; exact hseed Q)
      ((Submodule.map_mono (maskedParityPacket_le_invariant L T P m U hU hseed r)).trans hU)

/-- A paid masked rank is a lower bound for any invariant target that
contains the seed block. -/
theorem maskedParityPacket_cut_rank {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) {m : ℕ} (hscale : p = m+2*P.natDegree)
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    {r : ℕ} (hr : r+1 ≤ m) : parityCensus m r ≤ finrank K U := by
  have h := Submodule.finrank_mono (maskedParityPacket_le_invariant L T P m U hU hseed r)
  rwa [(maskedParityPacket_rank_and_le sys P hP hscale r hr).1] at h

/-- At equality the actual masked packet fills the target, rather than
only bounding its cardinal dimension. -/
theorem maskedParityPacket_eq_of_cut_rank {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) {m : ℕ} (hscale : p = m+2*P.natDegree)
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U)
    {r : ℕ} (hr : r+1 ≤ m) (htight : finrank K U = parityCensus m r) :
    maskedParityPacket L T P m r = U :=
  Submodule.eq_of_le_of_finrank_eq (maskedParityPacket_le_invariant L T P m U hU hseed r)
    ((maskedParityPacket_rank_and_le sys P hP hscale r hr).1.trans htight.symm)

/-- Optimize either parity in the effective order p−2 deg P. -/
theorem maskedParityPacket_cut_floor {L : K[X] →ₗ[K] V} {T : V →ₗ[K] V}
    {E : ℕ → Submodule K V} {p : ℕ} (sys : PaidPolyClockSystem L T E p)
    (P : K[X]) (hP : P ≠ 0) (hpos : 2*P.natDegree < p)
    (U : Submodule K V) (hU : U.map T ≤ U) (hseed : ∀ Q : K[X], L (P*Q) ∈ U) :
    nonsingularStageFloor (p-2*P.natDegree) ≤ finrank K U := by
  let m := p-2*P.natDegree
  have hm : 0 < m := by dsimp [m]; omega
  have hz : p = m+2*P.natDegree := by dsimp [m]; omega
  exact max_le
    (maskedParityPacket_cut_rank sys P hP hz U hU hseed (r := m-1) (by omega))
    (maskedParityPacket_cut_rank sys P hP hz U hU hseed (r := m-2) (by omega))

end
end RKResearch.Certified.Graded
