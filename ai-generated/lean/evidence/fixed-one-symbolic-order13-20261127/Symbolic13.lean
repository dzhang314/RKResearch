module

public import Seed11Donors
public import Symbolic13Data
public import RKCert.ReviewedNative.TailMatrixReceipts
public import RKCert.ReviewedNative.CausalStageMerge
import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Native rational order thirteen in 35 physical strict SDIRK stages

Use the unchanged 26-stage order-eleven seed. All signed moment and
row-array obligations below are finite scalar or matrix equalities.
The rooted order proof is the symbolic moment induction, not a replay
of size-thirteen rooted trees.
-/

namespace RKResearch.Certified.FixedOneOrder13

open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge
open Symbolic13Data
open scoped Matrix FiniteRootedTree BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
set_option Elab.async false

private theorem finiteOne {m : ℕ} (P : Fin m → Prop)
    [DecidablePred P]
    (h : (List.finRange m).all (fun i => decide (P i)) = true) :
    ∀ i, P i := fun i => of_decide_eq_true (List.all_eq_true.mp h i (List.mem_finRange i))

private theorem finiteTwo {m n : ℕ} (f : Fin m → Fin n → Bool)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => f i j)) = true) :
    ∀ i j, f i j = true := by
  intro i j
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  exact List.all_eq_true.mp hi j (List.mem_finRange j)

private theorem finiteMat {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℚ)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => decide (X i j = Y i j))) = true) :
    X = Y := Matrix.ext (fun i j => of_decide_eq_true (finiteTwo (fun i j => decide (X i j = Y i j)) h i j))

abbrev A0 := StrictSDIRKGram26Order11.A
abbrev b0 := StrictSDIRKGram26Order11.b
abbrev c0 := StrictSDIRKGram26Order11.clocks

/-- The three actual old chronological donors, zero-based. -/
def donors (i : Fin 3) : Fin 26 :=
  #[18,19,20][i.val]!

def donorTime (i : Fin 3) : ℚ :=
  #[-9, -11, (251647454237400205 / 337389807870474227 : ℚ)][i.val]!

theorem donor_pure (i : Fin 3) : PureAt A0 (donors i) 7 := by
  fin_cases i
  · exact Seed11Donors.pure18
  · exact Seed11Donors.pure19
  · exact Seed11Donors.pure20

theorem donor_clock (i : Fin 3) : clocks A0 (donors i) = donorTime i := by
  fin_cases i
  · exact Seed11Donors.clock18
  · exact Seed11Donors.clock19
  · exact Seed11Donors.clock20

def oldObs (j : Fin 7) : Fin 26 → ℚ :=
  if j.val < 5 then b0 * c0^j.val
  else if j.val = 5 then Pi.single (18 : Fin 26) 1 else Pi.single (19 : Fin 26) 1

def bank : Matrix (Fin 7 ⊕ Fin 3) (Fin 26) ℚ :=
  Sum.elim oldObs fun i => A0 (donors i) - Pi.single (donors i) 1

def bankResponse : Matrix (Fin 7 ⊕ Fin 3) (Fin 7) ℚ :=
  Sum.elim (mixed ℚ 6 (-9) (-11)) fun i j =>
    donorTime i^(j.val+1) / ((j.val+1 : ℕ) : ℚ) - donorTime i^j.val

def feedMap : Matrix (Fin 12) (Fin 7 ⊕ Fin 3) ℚ :=
  fun i j => feedCoeffs i (finSumFinEquiv j)

theorem left_inverse : mixInv * mixed ℚ 6 (-9) (-11) = (1 : Matrix (Fin 7) (Fin 7) ℚ) :=
  finiteMat _ _ (by decide +kernel)

theorem decoder : IsDecoder A0 6 (mixInv * observations 6 A0 b0 (18 : Fin 26) (19 : Fin 26)) := by
  apply twoDonorDecoder StrictSDIRKGram26Order11.order Seed11Donors.pure18 Seed11Donors.pure19
  rw [Seed11Donors.clock18, Seed11Donors.clock19]
  exact left_inverse

private theorem oldObs_eq : oldObs = observations 6 A0 b0 (18 : Fin 26) (19 : Fin 26) := by
  funext i
  simp [oldObs, observations, Seed11Donors.clockVec]

private theorem bank_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 6) :
    bank *ᵥ normalized A0 t =
      bankResponse.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ho := t.order.pos
  have hk : (t.order : ℕ)-1+1 = (t.order : ℕ) := by omega
  funext j
  cases j with
  | inl j =>
    have h := observed_eq_column StrictSDIRKGram26Order11.order
      Seed11Donors.pure18 Seed11Donors.pure19 t (by omega : (t.order : ℕ) ≤ 7)
    rw [← oldObs_eq, Seed11Donors.clock18, Seed11Donors.clock19] at h
    exact congrFun h j
  | inr j =>
    have hp := pure_predecessor (donors j) (donor_pure j) (1 : ℚ) t ht
    rw [donor_clock, one_mul] at hp
    change (A0 (donors j) - Pi.single (donors j) 1) ⬝ᵥ normalized A0 t =
      donorTime j ^ (((t.order : ℕ)-1)+1) / (((t.order : ℕ)-1+1 : ℕ) : ℚ) -
        donorTime j ^ ((t.order : ℕ)-1)
    rw [hk]
    exact hp

/-- The finite factors express all virtual feed rows on the actual old
weighted moments, two point samples, and three literal old strict rows. -/
private theorem feed_decomp : (blockU : Matrix (Fin 12) (Fin 26) ℚ) = feedMap * bank :=
  finiteMat _ _ (by decide +kernel)

def powerBasis : Matrix (Fin 12) (Fin 7) ℚ := fun i k => site i^k.val
def primitiveBasis : Matrix (Fin 12) (Fin 7) ℚ :=
  fun i k => site i^(k.val+1) / ((k.val+1 : ℕ) : ℚ)

private theorem integrated_columns (i : Fin 12) (k : Fin 6) :
    (feedMap * bankResponse + (blockB : Matrix (Fin 12) (Fin 12) ℚ) * powerBasis) i k.castSucc =
      primitiveBasis i k.castSucc :=
  of_decide_eq_true (finiteTwo (fun (i : Fin 12) (k : Fin 6) => decide ((feedMap * bankResponse + blockB * powerBasis)
    i (Fin.castSucc k) = primitiveBasis i (Fin.castSucc k))) (by decide +kernel) i k)

private theorem feed_paid (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 6) :
    blockU *ᵥ normalized A0 t + blockB *ᵥ (site^((t.order : ℕ)-1)) =
      ((1 / (t.order : ℚ)) : ℚ) • site^(t.order : ℕ) := by
  have ho := t.order.pos
  let k : Fin 6 := ⟨(t.order : ℕ)-1, by omega⟩
  have hk : k.castSucc.val + 1 = (t.order : ℕ) := by dsimp [k]; omega
  have he : site^((t.order : ℕ)-1) = (powerBasis : Matrix (Fin 12) (Fin 7) ℚ).col k.castSucc := rfl
  rw [feed_decomp, ← Matrix.mulVec_mulVec, bank_exact t ht, he]
  funext i
  have heq := integrated_columns i k
  change (feedMap *ᵥ (bankResponse.col k.castSucc)) i +
    (blockB *ᵥ ((powerBasis : Matrix (Fin 12) (Fin 7) ℚ).col k.castSucc)) i =
    ((1 / (t.order : ℚ)) : ℚ) * site i^(t.order : ℕ)
  have hx : ((feedMap * bankResponse) i k.castSucc) =
    (feedMap *ᵥ (bankResponse.col k.castSucc)) i := rfl
  have hy : ((blockB : Matrix (Fin 12) (Fin 12) ℚ) * powerBasis) i k.castSucc =
    (blockB *ᵥ ((powerBasis : Matrix (Fin 12) (Fin 7) ℚ).col k.castSucc)) i := rfl
  rw [← hx, ← hy, ← Matrix.add_apply, heq]
  simp only [primitiveBasis, hk, div_eq_mul_inv, one_mul, mul_comm]

private theorem pays_quad (j : Fin 13) :
    read weights site j.val 1 = 1 / ((j.val+1 : ℕ) : ℚ) :=
  finiteOne (fun i : Fin 13 => read weights site i.val 1 = 1 / ((i.val+1 : ℕ) : ℚ))
    (by decide +kernel) j

private theorem g_rows : momentRows 6 weights site * blockB = G * momentRows 7 weights site :=
  finiteMat _ _ (by decide +kernel)

private theorem h_rows : momentRows 6 weights site * blockU = H * momentRows 7 b0 (clocks A0) := by
  rw [Seed11Donors.clockVec]
  exact finiteMat _ _ (by decide +kernel)

private theorem g_bounds (j : Fin 6) (k : Fin 7) (h : j.val+1 < k.val) : G j k = 0 :=
  (of_decide_eq_true (finiteTwo (fun j k => decide (j.val+1 ≥ k.val ∨ G j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h)

private theorem h_bounds (j : Fin 6) (k : Fin 7) (h : j.val ≤ k.val) : H j k = 0 :=
  (of_decide_eq_true (finiteTwo (fun j k => decide (k.val < j.val ∨ H j k = 0))
    (by decide +kernel) j k)).resolve_left (not_lt_of_ge h)

private theorem scalarPay (j : Fin 6) (m : ℕ) (hm : 6 < m) (hp : m+j.val+1 ≤ 13) :
    (m : ℚ) * (∑ k : Fin 7, G j k * (1 / ((m+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 7, H j k * (1 / ((m+k.val : ℕ) : ℚ))) =
      1 / ((m+j.val+1 : ℕ) : ℚ) := by
  let m' : Fin 13 := ⟨m,by omega⟩
  have hh := of_decide_eq_true (finiteTwo (fun (j : Fin 6) (n : Fin 13) => decide (
    n.val ≤ 6 ∨ 13 < n.val+j.val+1 ∨
    (n.val : ℚ) * (∑ k : Fin 7, G j k * (1 / ((n.val+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 7, H j k * (1 / ((n.val+k.val : ℕ) : ℚ))) =
      1 / ((n.val+j.val+1 : ℕ) : ℚ))) (by decide +kernel) j m')
  exact (hh.resolve_left (not_le_of_gt hm)).resolve_left (not_lt_of_ge hp)

private def adjoint : Adjoints 6 A0 b0 blockU blockB weights site where
  G := G
  H := H
  gbound := g_bounds
  hbound := h_bounds
  rows := adjoint_rows_from_matrices G H g_rows h_rows
  scalar := scalarPay

def Ablock := tableau A0 blockU blockB
def bblock : Fin 26 ⊕ Fin 12 → ℚ := Sum.elim 0 weights

theorem paidBlock : HasOrder 13 Ablock bblock :=
  tail_hasOrder StrictSDIRKGram26Order11.order
    (fun j hj => pays_quad ⟨j,hj⟩) feed_paid adjoint

private theorem unpaid_bush : (14 : ℚ) * read weights site 13 1 ≠ 1 := by decide +kernel

theorem noNextBlock : ¬ HasOrder 14 Ablock bblock := by
  intro h
  have h13 := h.hasQuadratureOrder 13 (by decide)
  have hclock := tail_clocks_from_feed (by decide : 1 ≤ 6) feed_paid
  change (14 : ℚ) * (bblock ⬝ᵥ (clocks Ablock)^13) = 1 at h13
  apply unpaid_bush
  have he : bblock ⬝ᵥ (clocks Ablock)^13 = read weights site 13 1 := by
    rw [Matrix.dotProduct_block]
    have ht : ((clocks Ablock)^13) ∘ Sum.inr = site^13 := by
      funext i
      simpa [Function.comp_apply, Pi.pow_apply, tail, Ablock] using congrArg (fun x : ℚ => x^13)
        (congrFun hclock i)
    rw [ht]
    simp [bblock, read_eq_moment]
  rw [← he]
  exact h13

def flatten : (Fin 26 ⊕ Fin 12) ≃ Fin 38 := finSumFinEquiv
def A38 : Matrix (Fin 38) (Fin 38) ℚ := shifted flatten Ablock
def b38 : Fin 38 → ℚ := bblock ∘ flatten.symm
/-- Remove only the common diagonal and all vacuous upper entries. -/
def S38 : Matrix (Fin 38) (Fin 38) ℚ := fun i j => if i ≤ j then 0 else A38 i j

private theorem strictS : ∀ i j : Fin 38, i ≤ j → S38 i j = 0 := by
  intro i j h
  simp [S38, h]
private theorem virtual_decomp : A38 = S38 + Matrix.diagonal (fun _ => (1 : ℚ)) :=
  finiteMat _ _ (by decide +kernel)

abbrev redirect : Fin 38 → Fin 35 := redirectHead (fresh := 9) donors
abbrev keep : Fin 35 → Fin 38 := keepHead 26 3 9

/-- Physical equality of the complete strict predecessor rows after
removing the two self taps. Distinct equal clocks do not suffice. -/
theorem virtual_copies (i j : Fin 38) :
    S38 i j = S38 (keep (redirect i)) j :=
  of_decide_eq_true (finiteTwo (fun i j => decide (S38 i j = S38 (keep (redirect i)) j)) (by decide +kernel) i j)

def A : Matrix (Fin 35) (Fin 35) ℚ := foldedMatrix redirect keep A38
def b : Fin 35 → ℚ := foldedWeights redirect b38

private theorem physical_merge (p : ℕ) :
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (HasOrder p A38 b38 ↔ HasOrder p A b) := by
  have h := copiedHead_merge (fresh := 9) donors S38 (1 : ℚ) virtual_copies strictS b38 p
  unfold A b
  rw [virtual_decomp] 
  exact h

theorem order : HasOrder 13 A b :=
  (physical_merge 13).2.2.mp ((order_shifted flatten Ablock bblock 13).mpr paidBlock)

theorem noNext : ¬ HasOrder 14 A b := by
  intro h
  exact noNextBlock ((order_shifted flatten Ablock bblock 14).mp ((physical_merge 14).2.2.mpr h))

theorem witness : ∃ (A : Matrix (Fin 35) (Fin 35) ℚ) (b : Fin 35 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = 1) ∧ (1 : ℚ) ≠ 0 ∧
    HasOrder 13 A b ∧ ¬ HasOrder 14 A b :=
  ⟨A,b,(physical_merge 13).1,(physical_merge 13).2.1,one_ne_zero,order,noNext⟩

#print axioms witness
end RKResearch.Certified.FixedOneOrder13
