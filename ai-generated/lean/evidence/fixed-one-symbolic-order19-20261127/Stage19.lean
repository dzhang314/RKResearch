module

public import Stage17
import all Stage17
public import Stage19Data
public import RKCert.ReviewedNative.CausalCopyLocal
public import RKCert.ReviewedNative.ProtectedTail

@[expose] public section

/-! Generated native symbolic order certificate with its next bank. -/

namespace RKResearch.Certified.FixedOneOrder19

open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge
open Stage19Data
open scoped Matrix FiniteRootedTree BigOperators

set_option maxHeartbeats 16000000
set_option maxRecDepth 24000
set_option Elab.async false

abbrev q : ℕ := 9
abbrev target : ℕ := 2*q+1
abbrev oldN : ℕ := 58
abbrev copies : ℕ := 4
abbrev newN : ℕ := 2*q
abbrev fresh : ℕ := newN-copies
abbrev protectedN : ℕ := q-copies
abbrev virtualN : ℕ := oldN+copies+fresh
abbrev physicalN : ℕ := oldN+fresh

private theorem check1 {m : ℕ} (f : Fin m → Bool)
    (h : (List.finRange m).all f = true) : ∀ i, f i = true :=
  fun i => List.all_eq_true.mp h i (List.mem_finRange i)

private theorem check2 {m n : ℕ} (f : Fin m → Fin n → Bool)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (f i)) = true) :
    ∀ i j, f i j = true := by
  intro i j
  exact check1 (f i) (check1 (fun k => (List.finRange n).all (f k)) h i) j

private theorem checkMat {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℚ)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => decide (X i j = Y i j))) = true) :
    X = Y := Matrix.ext (fun i j => of_decide_eq_true (check2 (fun i j => decide (X i j = Y i j)) h i j))

abbrev A0 := FixedOneOrder17.A
abbrev b0 := FixedOneOrder17.b
abbrev c0 := FixedOneOrder17.c
abbrev donors : Fin copies → Fin oldN := FixedOneOrder17.bankIndex
abbrev donorTime : Fin copies → ℚ := FixedOneOrder17.bankTime

def firstDonor : Fin copies := ⟨0, by decide⟩
def secondDonor : Fin copies := ⟨1, by decide⟩
private theorem firstClock : clocks A0 (donors firstDonor) = donorTime firstDonor :=
  FixedOneOrder17.bank_clock firstDonor
private theorem secondClock : clocks A0 (donors secondDonor) = donorTime secondDonor :=
  FixedOneOrder17.bank_clock secondDonor

def oldObs : Matrix (Fin (q+1)) (Fin oldN) ℚ := fun j =>
  if j.val < q-1 then b0 * c0^j.val
  else if j.val = q-1 then Pi.single (donors firstDonor) 1 else Pi.single (donors secondDonor) 1

def oldPred : Matrix (Fin copies) (Fin oldN) ℚ :=
  fun i => A0 (donors i) - Pi.single (donors i) 1

def bank : Matrix (Fin (q+1) ⊕ Fin copies) (Fin oldN) ℚ :=
  combineRows oldObs oldPred

abbrev scalarMix := mixed ℚ q (donorTime firstDonor) (donorTime secondDonor)

def donorResponse : Matrix (Fin copies) (Fin (q+1)) ℚ :=
  fun i j => donorTime i^(j.val+1) / ((j.val+1 : ℕ) : ℚ) - donorTime i^j.val

def bankResponse : Matrix (Fin (q+1) ⊕ Fin copies) (Fin (q+1)) ℚ :=
  combineRows scalarMix donorResponse

def feedMap : Matrix (Fin newN) (Fin (q+1) ⊕ Fin copies) ℚ :=
  fun i j => feedCoeffs i (finSumFinEquiv j)

theorem mixed_inv : mixInv * scalarMix = (1 : Matrix (Fin (q+1)) (Fin (q+1)) ℚ) :=
  checkMat _ _ (by decide +kernel)

theorem decoder : IsDecoder A0 q (mixInv * observations q A0 b0 (donors firstDonor) (donors secondDonor)) := by
  apply twoDonorDecoder FixedOneOrder17.order
    (FixedOneOrder17.pure_bank firstDonor) (FixedOneOrder17.pure_bank secondDonor)
  rw [firstClock, secondClock]
  exact mixed_inv

private theorem oldObs_eq : oldObs = observations q A0 b0 (donors firstDonor) (donors secondDonor) := by
  funext i
  simp [oldObs, observations, FixedOneOrder17.clocks_eq]

private theorem obs_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1) :
    oldObs *ᵥ normalized A0 t =
      scalarMix.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have h := observed_eq_column (q := q) (a₀ := donors firstDonor) (a₁ := donors secondDonor) FixedOneOrder17.order
    (FixedOneOrder17.pure_bank firstDonor) (FixedOneOrder17.pure_bank secondDonor) t ht
  rw [← oldObs_eq, firstClock, secondClock] at h
  exact h

private theorem bank_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q) :
    bank *ᵥ normalized A0 t =
      bankResponse.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ho := t.order.pos
  have hk : (t.order : ℕ)-1+1 = (t.order : ℕ) := by omega
  funext j
  cases j with
  | inl j => exact congrFun (obs_exact t (by omega)) j
  | inr j =>
    have hp := pure_predecessor (donors j) (FixedOneOrder17.pure_bank j) (1 : ℚ) t ht
    rw [FixedOneOrder17.bank_clock, one_mul] at hp
    change (A0 (donors j) - Pi.single (donors j) 1) ⬝ᵥ normalized A0 t =
      donorTime j ^ (((t.order : ℕ)-1)+1) / (((t.order : ℕ)-1+1 : ℕ) : ℚ) -
        donorTime j ^ ((t.order : ℕ)-1)
    rw [hk]
    exact hp

private theorem feed_decomp : blockU = feedMap * bank :=
  checkMat _ _ (by decide +kernel)

def powerBasis : Matrix (Fin newN) (Fin (q+1)) ℚ := fun i k => site i^k.val
def primitiveBasis : Matrix (Fin newN) (Fin (q+1)) ℚ :=
  fun i k => site i^(k.val+1) / ((k.val+1 : ℕ) : ℚ)

private theorem integrated_columns (i : Fin newN) (k : Fin q) :
    (feedMap * bankResponse + blockB * powerBasis) i k.castSucc =
      primitiveBasis i k.castSucc :=
  of_decide_eq_true (check2 (fun (i : Fin newN) (k : Fin q) =>
    decide ((feedMap * bankResponse + blockB * powerBasis) i (Fin.castSucc k) =
      primitiveBasis i (Fin.castSucc k))) (by decide +kernel) i k)

private theorem feed_paid (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q) :
    blockU *ᵥ normalized A0 t + blockB *ᵥ (site^((t.order : ℕ)-1)) =
      ((1 / (t.order : ℚ)) : ℚ) • site^(t.order : ℕ) := by
  have ho := t.order.pos
  let k : Fin q := ⟨(t.order : ℕ)-1, by omega⟩
  have hk : k.castSucc.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  have he : site^((t.order : ℕ)-1) = powerBasis.col k.castSucc := rfl
  rw [feed_decomp, ← Matrix.mulVec_mulVec, bank_exact t ht, he]
  funext i
  have heq := integrated_columns i k
  change (feedMap *ᵥ (bankResponse.col k.castSucc)) i +
    (blockB *ᵥ (powerBasis.col k.castSucc)) i =
    ((1 / (t.order : ℚ)) : ℚ) * site i^(t.order : ℕ)
  have hx : (feedMap * bankResponse) i k.castSucc =
    (feedMap *ᵥ (bankResponse.col k.castSucc)) i := rfl
  have hy : (blockB * powerBasis) i k.castSucc =
    (blockB *ᵥ (powerBasis.col k.castSucc)) i := rfl
  rw [← hx, ← hy, ← Matrix.add_apply, heq]
  simp only [primitiveBasis, hk, div_eq_mul_inv, one_mul, mul_comm]

private theorem pays_quad (j : Fin target) :
    read weights site j.val 1 = 1 / ((j.val+1 : ℕ) : ℚ) :=
  of_decide_eq_true (check1 (fun i : Fin target => decide
    (read weights site i.val 1 = 1 / ((i.val+1 : ℕ) : ℚ)))
    (by decide +kernel) j)

private theorem g_rows : momentRows q weights site * blockB = G * momentRows (q+1) weights site :=
  checkMat _ _ (by decide +kernel)

private theorem h_rows : momentRows q weights site * blockU = H * momentRows (q+1) b0 (clocks A0) := by
  rw [FixedOneOrder17.clocks_eq]
  exact checkMat _ _ (by decide +kernel)

private theorem g_bounds (j : Fin q) (k : Fin (q+1)) (h : j.val+1 < k.val) : G j k = 0 :=
  (of_decide_eq_true (check2 (fun j k => decide (j.val+1 ≥ k.val ∨ G j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h)

private theorem h_bounds (j : Fin q) (k : Fin (q+1)) (h : j.val ≤ k.val) : H j k = 0 :=
  (of_decide_eq_true (check2 (fun j k => decide (k.val < j.val ∨ H j k = 0))
    (by decide +kernel) j k)).resolve_left (not_lt_of_ge h)

private theorem scalarPay (j : Fin q) (m : ℕ) (hm : q < m) (hp : m+j.val+1 ≤ target) :
    (m : ℚ) * (∑ k : Fin (q+1), G j k * (1 / ((m+k.val : ℕ) : ℚ)) +
      ∑ k : Fin (q+1), H j k * (1 / ((m+k.val : ℕ) : ℚ))) =
      1 / ((m+j.val+1 : ℕ) : ℚ) := by
  let m' : Fin target := ⟨m,by omega⟩
  have hh := of_decide_eq_true (check2 (fun (j : Fin q) (n : Fin target) => decide (
    n.val ≤ q ∨ target < n.val+j.val+1 ∨
    (n.val : ℚ) * (∑ k : Fin (q+1), G j k * (1 / ((n.val+k.val : ℕ) : ℚ)) +
      ∑ k : Fin (q+1), H j k * (1 / ((n.val+k.val : ℕ) : ℚ))) =
      1 / ((n.val+j.val+1 : ℕ) : ℚ))) (by decide +kernel) j m')
  exact (hh.resolve_left (not_le_of_gt hm)).resolve_left (not_lt_of_ge hp)

private def adjoint : Adjoints q A0 b0 blockU blockB weights site where
  G := G
  H := H
  gbound := g_bounds
  hbound := h_bounds
  rows := adjoint_rows_from_matrices G H g_rows h_rows
  scalar := scalarPay

def Ablock := tableau A0 blockU blockB
def bblock : Fin oldN ⊕ Fin newN → ℚ := Sum.elim 0 weights

theorem paidBlock : HasOrder target Ablock bblock :=
  tail_hasOrder FixedOneOrder17.order (fun j hj => pays_quad ⟨j,hj⟩) feed_paid adjoint

private theorem unpaid_bush : ((target+1 : ℕ) : ℚ) * read weights site target 1 ≠ 1 := by decide +kernel

theorem noNextBlock : ¬ HasOrder (target+1) Ablock bblock := by
  intro h
  have ht := h.hasQuadratureOrder target (by decide)
  have hclock := tail_clocks_from_feed (by decide : 1 ≤ q) feed_paid
  change ((target+1 : ℕ) : ℚ) * (bblock ⬝ᵥ (clocks Ablock)^target) = 1 at ht
  apply unpaid_bush
  have he : bblock ⬝ᵥ (clocks Ablock)^target = read weights site target 1 := by
    rw [Matrix.dotProduct_block]
    have hx : ((clocks Ablock)^target) ∘ Sum.inr = site^target := by
      funext i
      simpa [Function.comp_apply, Pi.pow_apply, tail, Ablock] using congrArg (fun x : ℚ => x^target)
        (congrFun hclock i)
    rw [hx]
    simp [bblock, read_eq_moment]
  rw [← he]
  exact ht

def flatten : (Fin oldN ⊕ Fin newN) ≃ Fin virtualN := finSumFinEquiv
def Av : Matrix (Fin virtualN) (Fin virtualN) ℚ := shifted flatten Ablock
def bv : Fin virtualN → ℚ := bblock ∘ flatten.symm
def Sv : Matrix (Fin virtualN) (Fin virtualN) ℚ := fun i j => if i ≤ j then 0 else Av i j

private theorem strictS : ∀ i j : Fin virtualN, i ≤ j → Sv i j = 0 := by
  intro i j h
  simp [Sv, h]

private theorem new_lower : blockB.IsLowerTriangular := by
  change ∀ ⦃i j : Fin newN⦄, i < j → blockB i j = 0
  intro i j h
  have hh := of_decide_eq_true (check2 (fun (i j : Fin newN) => decide (j ≤ i ∨ blockB i j = 0))
    (by decide +kernel) i j)
  exact hh.resolve_left (not_le_of_gt h)

private theorem new_diag (i : Fin newN) : blockB i i = 1 :=
  of_decide_eq_true (check1 (fun i : Fin newN => decide (blockB i i = 1)) (by decide +kernel) i)

private theorem virtual_decomp : Av = Sv + Matrix.diagonal (fun _ => (1 : ℚ)) :=
  strict_diag_reassembly Av (1 : ℚ)
    (chronological_lower (U := blockU) (FixedOneOrder17.physical_merge FixedOneOrder17.target).1 new_lower)
    (chronological_diagonal (U := blockU) 1 (FixedOneOrder17.physical_merge FixedOneOrder17.target).2.1 new_diag)

abbrev redirect : Fin virtualN → Fin physicalN := redirectHead (fresh := fresh) donors
abbrev keep : Fin physicalN → Fin virtualN := keepHead oldN copies fresh

/-- Only the actual removed strict rows require arithmetic checks. -/
theorem virtual_copies (i j : Fin virtualN) :
    Sv i j = Sv (keep (redirect i)) j := by
  apply eq_of_actual_copies (fresh := fresh) donors Sv _ i j
  intro k l
  exact of_decide_eq_true (check2 (fun (k : Fin copies) (l : Fin virtualN) => decide
    (Sv (copyIndex oldN fresh k) l = Sv (keep (donorLift fresh (donors k))) l))
    (by decide +kernel) k l)

def A : Matrix (Fin physicalN) (Fin physicalN) ℚ := fastFoldMatrix (fresh := fresh) donors Av
def b : Fin physicalN → ℚ := fastFoldWeights (fresh := fresh) donors bv

theorem A_eq : A = foldedMatrix redirect keep Av := fastFoldMatrix_eq (fresh := fresh) donors Av
theorem b_eq : b = foldedWeights redirect bv := fastFoldWeights_eq (fresh := fresh) donors bv

private theorem physical_merge (p : ℕ) :
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (HasOrder p Av bv ↔ HasOrder p A b) := by
  rw [A_eq, b_eq]
  have h := copiedHead_merge (fresh := fresh) donors Sv (1 : ℚ) virtual_copies strictS bv p
  rw [virtual_decomp]
  exact h

theorem order : HasOrder target A b :=
  (physical_merge target).2.2.mp ((order_shifted flatten Ablock bblock target).mpr paidBlock)

theorem noNext : ¬ HasOrder (target+1) A b := by
  intro h
  exact noNextBlock ((order_shifted flatten Ablock bblock (target+1)).mp ((physical_merge (target+1)).2.2.mpr h))

theorem witness : ∃ (A : Matrix (Fin physicalN) (Fin physicalN) ℚ) (b : Fin physicalN → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder target A b ∧ ¬ HasOrder (target+1) A b :=
  ⟨A,b,(physical_merge target).1,(physical_merge target).2.1,one_ne_zero,order,noNext⟩

private theorem respects : Respects Av redirect keep := by
  have h := respects_literal Sv (1 : ℚ) redirect keep
    (redirect_keepHead (fresh := fresh) donors) virtual_copies
  rw [← virtual_decomp] at h
  exact h

/-- Actual physical clocks and location of the next protected bank. -/
def c : Fin physicalN → ℚ := (Sum.elim c0 site) ∘ flatten.symm ∘ keep
def protectedIndex (i : Fin protectedN) : Fin newN := ⟨copies+i.val, by
  have := i.isLt
  dsimp [protectedN, newN, copies, q] at *
  omega⟩
def bankIndex (i : Fin protectedN) : Fin physicalN := redirect (flatten (Sum.inr (protectedIndex i)))
def bankTime (i : Fin protectedN) : ℚ := site (protectedIndex i)

theorem clocks_eq : clocks A = c := by
  rw [A_eq]
  have hv : clocks Av = clocks (foldedMatrix redirect keep Av) ∘ redirect :=
    mulVec_pullback respects 1
  have hv0 : clocks Av = clocks Ablock ∘ flatten.symm :=
    action_shifted flatten Ablock 1
  have hh : clocks Ablock = Sum.elim c0 site := by
    funext i
    cases i with
    | inl i =>
      have h := congrFun (head_action A0 blockU blockB 1) i
      change clocks Ablock (Sum.inl i) = clocks A0 i at h
      rw [FixedOneOrder17.clocks_eq] at h
      exact h
    | inr i =>
      exact congrFun (tail_clocks_from_feed (by decide : 1 ≤ q) feed_paid) i
  rw [hh] at hv0
  rw [hv0] at hv
  funext i
  have h := congrFun hv (keep i)
  simp only [Function.comp_apply, redirect_keepHead] at h
  exact h.symm

theorem bankIndex_val (i : Fin protectedN) : (bankIndex i).val = oldN+i.val :=
  of_decide_eq_true (check1 (fun j : Fin protectedN =>
    decide ((bankIndex j).val = oldN+j.val)) (by decide +kernel) i)

theorem bank_clock (i : Fin protectedN) : clocks A (bankIndex i) = bankTime i := by
  rw [clocks_eq]
  exact of_decide_eq_true (check1 (fun j : Fin protectedN => decide (c (bankIndex j) = bankTime j))
    (by decide +kernel) i)

private theorem zero_pred (i : Fin protectedN) (j : Fin copies) :
    feedMap (protectedIndex i) (Sum.inr j) = 0 :=
  of_decide_eq_true (check2 (fun (i : Fin protectedN) (j : Fin copies) => decide
    (feedMap (protectedIndex i) (Sum.inr j) = 0)) (by decide +kernel) i j)

private theorem protected_integrates (i : Fin protectedN) (k : Fin (q+1)) :
    (feedMap * bankResponse + blockB * powerBasis) (protectedIndex i) k =
      primitiveBasis (protectedIndex i) k :=
  of_decide_eq_true (check2 (fun (i : Fin protectedN) (k : Fin (q+1)) => decide
    ((feedMap * bankResponse + blockB * powerBasis) (protectedIndex i) k =
      primitiveBasis (protectedIndex i) k)) (by decide +kernel) i k)

private theorem protected_paid (i : Fin protectedN) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ q+1) :
    (blockU *ᵥ normalized A0 t + blockB *ᵥ (site^((t.order : ℕ)-1))) (protectedIndex i) =
      site (protectedIndex i) ^ (t.order : ℕ)/(t.order : ℚ) := by
  have ho := t.order.pos
  let k : Fin (q+1) := ⟨(t.order : ℕ)-1, by omega⟩
  have he := protected_bank_action (i := protectedIndex i) (j := k)
    feedMap oldObs oldPred scalarMix donorResponse (zero_pred i) (obs_exact t ht)
  change ((feedMap * bank) *ᵥ normalized A0 t) (protectedIndex i) =
    (feedMap * bankResponse) (protectedIndex i) k at he
  rw [feed_decomp, Pi.add_apply, he]
  change (feedMap * bankResponse + blockB * powerBasis) (protectedIndex i) k =
      site (protectedIndex i)^(t.order : ℕ)/(t.order : ℚ)
  rw [protected_integrates]
  have hk : k.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  simp only [primitiveBasis, hk]

theorem pure_bank (i : Fin protectedN) : PureAt A (bankIndex i) (q+2) := by
  have h := protected_pure (by decide : 1 ≤ q) feed_paid (protectedIndex i) (protected_paid i)
  have hv : PureAt Av (flatten (Sum.inr (protectedIndex i))) (q+2) := by
    apply (pure_shifted_iff Ablock flatten _ _).mpr
    rw [Equiv.symm_apply_apply]
    exact h
  rw [A_eq]
  exact (pure_folded_iff respects _ _).mp hv

#print axioms witness
#print axioms pure_bank
end RKResearch.Certified.FixedOneOrder19
