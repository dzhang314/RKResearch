module

public import RKCert.ReviewedNative.PolynomialCertificatePortIntegral
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageRule
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.List.FinRange

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

structure LocalPort where
  factors : List (Fin 8)
  stop : Fin 8
  e : ℕ
  reflected : Bool
  deriving DecidableEq, Repr

structure PortWord where
  roots : List (Fin 8)
  u : Fin 8
  a : Fin 8
  h : Fin 8
  z : Fin 8
  deriving DecidableEq, Repr

/-- Input permutation lists, in this order, the positions of r1,r2,r3,r4,
u,a,h,z in the strictly sorted physical site tuple. -/
def decodeWord (σ : List (Fin 8)) : PortWord :=
  ⟨σ.take 4, σ[4]?.getD 0, σ[5]?.getD 0, σ[6]?.getD 0, σ[7]?.getD 0⟩

def PortWord.before (w : PortWord) (k : Fin 8) : ℕ :=
  (w.roots.filter (fun i => decide (i < k))).length

/-- Necessary inequalities from the genuine separate and difference port
windows. The geometric input must establish these; they are not conclusions
of a formal quadrature identity on arbitrary labels. -/
def PortWord.permitted (w : PortWord) : Bool :=
  decide (w.roots.Pairwise (· < ·) ∧ 2 ≤ w.before w.u ∧ w.before w.z ≤ 2 ∧
    (if w.a < w.u then 1 ≤ w.before w.a ∧ w.before w.a < w.before w.u
      else w.before w.u < w.before w.a) ∧
    (if w.z < w.h then w.before w.z < w.before w.h ∧ w.before w.h ≤ 3
      else w.before w.h < w.before w.z))

def PortWord.six (w : PortWord) : List LocalPort :=
  [⟨w.roots, w.u, 1, false⟩, ⟨w.roots, w.z, 1, true⟩,
   ⟨w.roots, w.u, 2, false⟩, ⟨w.roots, w.z, 2, true⟩,
   ⟨w.roots ++ [w.u], w.a, 1, false⟩, ⟨w.roots ++ [w.z], w.h, 1, true⟩]

structure SignedPort where
  port : LocalPort
  positive : Bool
  deriving DecidableEq, Repr

def gridInterval (r : CageRow) (reflected : Bool) (i : Fin 8) : ℤ × ℤ :=
  let z := r.endpoint i.val
  if reflected then (32768 - (z.2 : ℤ), 32768 - (z.1 : ℤ)) else ((z.1 : ℤ), (z.2 : ℤ))

def SignedPort.ok (r : CageRow) (test : SignedPort) : Bool :=
  let bounds := gridInterval r test.port.reflected
  let stop := bounds test.port.stop
  boxPortOK test.positive test.port.e stop.1 stop.2 (test.port.factors.map bounds)

def planOK (words : List PortWord) (r : CageRow) (plan : List SignedPort) : Bool :=
  plan.all (SignedPort.ok r) &&
    words.all (fun w => plan.any (fun p => decide (p.port ∈ w.six)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def portSite (reflected : Bool) (β : Fin 8 → K) (i : Fin 8) : K :=
  if reflected then 1 - β i else β i

noncomputable def LocalPort.value (p : LocalPort) (β : Fin 8 → K) : K :=
  formalPort p.e (portSite p.reflected β p.stop) (p.factors.map (portSite p.reflected β))

abbrev InCages (r : CageRow) (β : Fin 8 → K) : Prop :=
  ∀ i : Fin 8, β i ∈ Set.Icc (((r.endpoint i.val).1 : K) / 32768)
    (((r.endpoint i.val).2 : K) / 32768)

private theorem gridInterval_mem (r : CageRow) (reflected : Bool) {β : Fin 8 → K}
    (hb : InCages r β) (i : Fin 8) :
    (32768 : K) * portSite reflected β i ∈ Set.Icc ((gridInterval r reflected i).1 : K)
      ((gridInterval r reflected i).2 : K) := by
  have pos : (0 : K) < 32768 := by norm_num
  have lo := (div_le_iff₀ pos).mp (hb i).1
  have hi := (le_div_iff₀ pos).mp (hb i).2
  cases reflected <;> constructor <;>
    simp [gridInterval, portSite] <;> linarith only [lo, hi]

private theorem gridInterval_factors (r : CageRow) (reflected : Bool) {β : Fin 8 → K}
    (hb : InCages r β) (ids : List (Fin 8)) :
    List.Forall₂ (fun a z => z ∈ Set.Icc (a.1 : K) (a.2 : K))
      (ids.map (gridInterval r reflected)) (ids.map (fun i => 32768 * portSite reflected β i)) := by
  induction ids with
  | nil => exact .nil
  | cons i ids ih => exact .cons (gridInterval_mem r reflected hb i) ih

/-- The exact accepted integer cell sign rules out the corresponding
literal normalized paid integral of the true sites. -/
theorem SignedPort.value_ne_zero {r : CageRow} (p : SignedPort) (ok : p.ok r = true)
    {β : Fin 8 → K} (hb : InCages r β) : p.port.value β ≠ 0 := by
  let d := portSite p.port.reflected β p.port.stop
  let rs := p.port.factors.map (portSite p.port.reflected β)
  have hh := boxPortOK_sound ok (gridInterval_mem r p.port.reflected hb p.port.stop)
    (gridInterval_factors r p.port.reflected hb p.port.factors)
  have shift : 0 < signedValue p.positive
      (formalPort p.port.e (32768 * d) (rs.map (fun z => (32768 : K) * z))) := by
    dsimp only [d, rs]
    rw [List.map_map]
    exact hh
  rw [formalPort_eq_rec, portRec_scale_factors] at shift
  intro bad
  have hz : portRec (unitMoment (K := K)) d rs p.port.e = 0 := by
    simpa only [LocalPort.value, formalPort_eq_rec, d, rs] using bad
  rw [hz, mul_zero] at shift
  cases hp : p.positive <;> simp [signedValue, hp] at shift

theorem plan_forces_nonzero {words : List PortWord} {r : CageRow} {plan : List SignedPort}
    (ok : planOK words r plan = true) {w : PortWord} (hw : w ∈ words)
    {β : Fin 8 → K} (hb : InCages r β) : ∃ p ∈ w.six, p.value β ≠ 0 := by
  obtain ⟨checks, coversWords⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨test, ht, hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp coversWords w hw)
  exact ⟨test.port, of_decide_eq_true hp, test.value_ne_zero (List.all_eq_true.mp checks test ht) hb⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
