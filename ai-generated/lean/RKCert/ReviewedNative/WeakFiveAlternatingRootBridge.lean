module

public import RKCert.ReviewedNative.OrderedSingleGapRoot
public import RKCert.ReviewedNative.OrderedAlternationDegree

import Mathlib.Tactic.Choose
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Actual roots from paid finite alternation witnesses

An explicitly supplied common ordered extension fills only the displayed
opposite-sign gaps. No ordered-field intermediate value theorem is assumed.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

open Polynomial
open RKCert.ReviewedNative.FiniteOrderedSigns
open RKCert.ReviewedNative.FiniteRootSeparator
open RKCert.ReviewedNative.OrderedRootGapSaturation
open scoped Polynomial

universe u v

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {L : Type v} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

/-- Keep the initial `m+1` representatives of a paid nonzero sample chain. -/
theorem finite_alternation_tuple {p : K[X]} {S : Set K} {m : ℕ} (hm : 0 < m)
    (h : HasAlternationsOn p S m) :
    ∃ x : Fin (m+1) → K, StrictMono x ∧ (∀ i, x i ∈ S) ∧
      ∀ i : Fin m, p.eval (x i.castSucc) * p.eval (x i.succ) < 0 := by
  obtain ⟨ys, inc, inside, alt, low⟩ := h.alternating_samples
  have avail : m+1 ≤ ys.length := by omega
  let x : Fin (m+1) → K := fun i => ys[i.val]'(i.isLt.trans_le avail)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i j ij
    exact (List.pairwise_iff_getElem.mp inc) i.val j.val (i.isLt.trans_le avail)
      (j.isLt.trans_le avail) ij
  · intro i
    exact inside _ (List.getElem_mem (i.isLt.trans_le avail))
  · intro i
    have zz := (List.isChain_iff_getElem.mp alt.jumps) i.val
      ((Nat.succ_lt_succ i.isLt).trans_le avail)
    simpa only [x, Fin.val_castSucc, Fin.val_succ] using zz

theorem alternations_map_unit (e : K →+* L) (ord : StrictMono e)
    {p : K[X]} {m : ℕ} (h : HasAlternationsOn p (Set.Ioo (0 : K) 1) m) :
    HasAlternationsOn (p.map e) (Set.Ioo (0 : L) 1) m := by
  obtain ⟨xs, inc, inner, alt, low⟩ := h.alternating_samples
  apply HasAlternationsOn.of_alternating_samples (xs := xs.map e)
    ((List.pairwise_map).2 (inc.imp fun h => ord h)) ?_ ?_
    (by simpa only [List.length_map] using low)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact ⟨by simpa only [map_zero] using ord (inner _ hy).1,
      by simpa only [map_one] using ord (inner _ hy).2⟩
  · constructor
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      intro eq
      rw [Polynomial.eval_map_apply] at eq
      exact alt.nonzero _ hy (e.injective (eq.trans (map_zero e).symm))
    · rw [List.isChain_map]
      apply alt.jumps.imp
      intro a b opposite
      simpa only [Polynomial.eval_map_apply, ← map_mul, ← map_zero e] using ord opposite

/-- Four paid departures give four actual distinct interior roots in one
field. The theorem is uniform in the number of strict gaps (at least one). -/
theorem roots_of_paid_unit_alternations {p : K[X]} {m : ℕ} (hm : 0 < m)
    (h : HasAlternationsOn p (Set.Ioo (0 : K) 1) m) :
    ∃ E : OrderedExtension K, ∃ r : Fin m → E.carrier,
      StrictMono r ∧ (∀ i, r i ∈ Set.Ioo 0 1) ∧
        ∀ i, (p.map E.embed).IsRoot (r i) := by
  classical
  obtain ⟨x, ix, inner, alt⟩ := finite_alternation_tuple hm h
  obtain ⟨E, source⟩ := RKCert.ReviewedNative.OrderedSingleGapRoot.exists_unitRootSource p
  have one (i : Fin m) := source (inner i.castSucc) (inner i.succ) (ix Fin.castSucc_lt_succ)
    (show Opposite (p.eval (x i.castSucc)) (p.eval (x i.succ)) from
      by simpa only [Opposite, mul_neg_iff, or_comm] using alt i)
  choose r lo hi rt using one
  refine ⟨E, r, ?_, ?_, rt⟩
  · intro i j ij
    have between : i.succ ≤ j.castSucc := by
      change i.val+1 ≤ j.val
      exact Nat.succ_le_of_lt ij
    exact (hi i).trans ((E.mono.monotone (ix.monotone between)).trans_lt (lo j))
  · intro i
    have a : 0 < E.embed (x i.castSucc) := by simpa only [map_zero] using E.mono (inner i.castSucc).1
    have b : E.embed (x i.succ) < 1 := by simpa only [map_one] using E.mono (inner i.succ).2
    exact ⟨a.trans (lo i), (hi i).trans b⟩

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
