module

public import Symbolic13
import all Symbolic13
public import RKCert.ReviewedNative.FastCausalFold
public import RKCert.ReviewedNative.ProtectedTail

@[expose] public section

/-! Certified successive seed from the frozen order-thirteen quotient. -/

namespace RKResearch.Certified.FixedOneSeed13

open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge
open Symbolic13Data
open scoped Matrix FiniteRootedTree BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

abbrev oldA := FixedOneOrder13.A0
abbrev blockMatrix := FixedOneOrder13.Ablock
abbrev keep := FixedOneOrder13.keep
abbrev redirect := FixedOneOrder13.redirect
abbrev flat := FixedOneOrder13.flatten

def A : Matrix (Fin 35) (Fin 35) ℚ :=
  fastFoldMatrix (fresh := 9) FixedOneOrder13.donors FixedOneOrder13.A38
def b : Fin 35 → ℚ :=
  fastFoldWeights (fresh := 9) FixedOneOrder13.donors FixedOneOrder13.b38

theorem mat_eq : A = FixedOneOrder13.A :=
  fastFoldMatrix_eq (fresh := 9) FixedOneOrder13.donors FixedOneOrder13.A38
theorem weights_eq : b = FixedOneOrder13.b :=
  fastFoldWeights_eq (fresh := 9) FixedOneOrder13.donors FixedOneOrder13.b38

theorem order : HasOrder 13 A b := by
  rw [mat_eq, weights_eq]
  exact FixedOneOrder13.order

theorem noNext : ¬ HasOrder 14 A b := by
  rw [mat_eq, weights_eq]
  exact FixedOneOrder13.noNext

private theorem respects : Respects FixedOneOrder13.A38 redirect keep := by
  have h := respects_literal FixedOneOrder13.S38 (1 : ℚ) redirect keep
    (redirect_keepHead (fresh := 9) FixedOneOrder13.donors) FixedOneOrder13.virtual_copies
  rw [← FixedOneOrder13.virtual_decomp] at h
  exact h

/-- Actual physical clock data, kept rows only. -/
def c : Fin 35 → ℚ := (Sum.elim FixedOneOrder13.c0 site) ∘ flat.symm ∘ keep

theorem clocks_eq : clocks A = c := by
  rw [mat_eq]
  have hv : clocks FixedOneOrder13.A38 =
      clocks FixedOneOrder13.A ∘ redirect := mulVec_pullback respects 1
  have hv0 : clocks FixedOneOrder13.A38 = clocks blockMatrix ∘ flat.symm :=
    action_shifted flat blockMatrix 1
  have hh : clocks blockMatrix = Sum.elim FixedOneOrder13.c0 site := by
    funext i
    cases i with
    | inl i =>
      have h := congrFun (head_action oldA blockU blockB 1) i
      change clocks blockMatrix (Sum.inl i) = clocks oldA i at h
      rw [Seed11Donors.clockVec] at h
      exact h
    | inr i =>
      have h := congrFun (tail_clocks_from_feed (by decide : 1 ≤ 6) FixedOneOrder13.feed_paid) i
      exact h
  rw [hh] at hv0
  rw [hv0] at hv
  funext i
  have h := congrFun hv (keep i)
  simp only [Function.comp_apply, redirect_keepHead] at h
  exact h.symm

/-- The three freshly protected head receivers of order thirteen. -/
def protectedIndex (i : Fin 3) : Fin 12 := ⟨3+i.val, by have := i.isLt; omega⟩
def bankIndex (i : Fin 3) : Fin 35 := redirect (flat (Sum.inr (protectedIndex i)))
def bankTime (i : Fin 3) : ℚ := site (protectedIndex i)

private theorem exactBool {m n : ℕ} (f : Fin m → Fin n → Bool)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => f i j)) = true) :
    ∀ i j, f i j = true := by
  intro i j
  exact List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i))
    j (List.mem_finRange j)

theorem bankIndex_val (i : Fin 3) : (bankIndex i).val = 26+i.val :=
  of_decide_eq_true (List.all_eq_true.mp (show (List.finRange 3).all
    (fun j => decide ((bankIndex j).val = 26+j.val)) = true by decide +kernel) i (List.mem_finRange i))

theorem bank_clock (i : Fin 3) : clocks A (bankIndex i) = bankTime i := by
  rw [clocks_eq]
  apply of_decide_eq_true
  exact List.all_eq_true.mp (show (List.finRange 3).all
    (fun j => decide (c (bankIndex j) = bankTime j)) = true by decide +kernel) i (List.mem_finRange i)

private theorem zero_pred (i j : Fin 3) :
    FixedOneOrder13.feedMap (protectedIndex i) (Sum.inr j) = 0 :=
  of_decide_eq_true (exactBool (fun (i j : Fin 3) => decide
    (FixedOneOrder13.feedMap (protectedIndex i) (Sum.inr j) = 0)) (by decide +kernel) i j)

private theorem protected_integrates (i : Fin 3) (k : Fin 7) :
    ((FixedOneOrder13.feedMap * FixedOneOrder13.bankResponse) +
         blockB * FixedOneOrder13.powerBasis) (protectedIndex i) k =
      FixedOneOrder13.primitiveBasis (protectedIndex i) k :=
  of_decide_eq_true (exactBool (fun (i : Fin 3) (k : Fin 7) => decide
    (((FixedOneOrder13.feedMap * FixedOneOrder13.bankResponse) +
         blockB * FixedOneOrder13.powerBasis) (protectedIndex i) k =
      FixedOneOrder13.primitiveBasis (protectedIndex i) k)) (by decide +kernel) i k)

private theorem protected_paid (i : Fin 3) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 7) :
    (blockU *ᵥ normalized oldA t + blockB *ᵥ (site^((t.order : ℕ)-1))) (protectedIndex i) =
      site (protectedIndex i) ^ (t.order : ℕ)/(t.order : ℚ) := by
  have ho := t.order.pos
  let k : Fin 7 := ⟨(t.order : ℕ)-1, by omega⟩
  have hObs := observed_eq_column StrictSDIRKGram26Order11.order
    Seed11Donors.pure18 Seed11Donors.pure19 t ht
  rw [← FixedOneOrder13.oldObs_eq, Seed11Donors.clock18, Seed11Donors.clock19] at hObs
  let O : Matrix (Fin 7) (Fin 26) ℚ := FixedOneOrder13.oldObs
  let P : Matrix (Fin 3) (Fin 26) ℚ :=
    fun j => oldA (FixedOneOrder13.donors j) - Pi.single (FixedOneOrder13.donors j) 1
  let M := mixed ℚ 6 (-9) (-11)
  let Rr : Matrix (Fin 3) (Fin 7) ℚ := fun i j =>
    FixedOneOrder13.donorTime i^(j.val+1) / ((j.val+1 : ℕ) : ℚ) - FixedOneOrder13.donorTime i^j.val
  have he := protected_bank_action (i := protectedIndex i) (j := k)
    FixedOneOrder13.feedMap O P M Rr (zero_pred i) hObs
  change ((FixedOneOrder13.feedMap * FixedOneOrder13.bank) *ᵥ normalized oldA t) (protectedIndex i) =
    (FixedOneOrder13.feedMap * FixedOneOrder13.bankResponse) (protectedIndex i) k at he
  rw [FixedOneOrder13.feed_decomp, Pi.add_apply, he]
  change ((FixedOneOrder13.feedMap * FixedOneOrder13.bankResponse) +
         blockB * FixedOneOrder13.powerBasis) (protectedIndex i) k =
      site (protectedIndex i)^ (t.order : ℕ)/(t.order : ℚ)
  rw [protected_integrates]
  have hk : k.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  simp only [FixedOneOrder13.primitiveBasis, hk]

theorem pure_bank (i : Fin 3) : PureAt A (bankIndex i) 8 := by
  have h := protected_pure (by decide : 1 ≤ 6) FixedOneOrder13.feed_paid
    (protectedIndex i) (protected_paid i)
  have hv : PureAt FixedOneOrder13.A38 (flat (Sum.inr (protectedIndex i))) 8 := by
    apply (pure_shifted_iff blockMatrix flat _ _).mpr
    rw [Equiv.symm_apply_apply]
    exact h
  rw [mat_eq]
  exact (pure_folded_iff respects _ _).mp hv

#print axioms pure_bank
#print axioms clocks_eq
end RKResearch.Certified.FixedOneSeed13
