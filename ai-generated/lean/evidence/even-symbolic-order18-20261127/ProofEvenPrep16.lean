module

public import ProofEvenPrep14
import all ProofEvenPrep14
public import EvenPrep16Data
public import RKCert.ReviewedNative.CausalCopyLocal
public import RKCert.ReviewedNative.FastCausalFold
public import RKCert.ReviewedNative.GeneralMomentTail
public import RKCert.ReviewedNative.ProtectedTail

@[expose] public section

namespace RKResearch.Certified.EvenPrep16

open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge EvenPrep16Data
open scoped Matrix BigOperators
abbrev A0 := EvenPrep14.A
abbrev b0 := EvenPrep14.b
abbrev c0 := EvenPrep14.c
abbrev γ : ℚ := 1/4

set_option maxHeartbeats 12000000
set_option maxRecDepth 18000
set_option Elab.async false

private theorem check1 {m : ℕ} (f : Fin m → Bool) (h : (List.finRange m).all f = true) :
    ∀ i, f i = true :=
  fun i => List.all_eq_true.mp h i (List.mem_finRange i)

private theorem check2 {m n : ℕ} (f : Fin m → Fin n → Bool)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (f i)) = true) :
    ∀ i j, f i j = true := by
  intro i j
  exact check1 (f i) (check1 (fun i => (List.finRange n).all (f i)) h i) j

private theorem checkMat {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) ℚ)
    (h : (List.finRange m).all (fun i => (List.finRange n).all (fun j => decide (X i j = Y i j))) = true) :
    X = Y := Matrix.ext (fun i j => of_decide_eq_true (check2 (fun i j => decide (X i j = Y i j)) h i j))

def donor (i : Fin 4) : Fin 41 := EvenPrep14.highIndex i

def recPoint : Matrix (Fin 3) (Fin 41) ℚ :=
  fun j => Pi.single (EvenPrep14.highIndex (j.castLE (by decide))) 1
def recPred : Matrix (Fin 4) (Fin 41) ℚ :=
  fun j => A0 (donor j) - Pi.single (donor j) γ

abbrev BankIndex := Fin 6 ⊕ (Fin 3 ⊕ Fin 4)

def bank : Matrix BankIndex (Fin 41) ℚ :=
  combineRows (momentRows 6 b0 c0) (combineRows recPoint recPred)
def respMom : Matrix (Fin 6) (Fin 9) ℚ :=
  fun i k => 1 / ((i.val+k.val+1 : ℕ) : ℚ)
def respPoint : Matrix (Fin 3) (Fin 9) ℚ :=
  fun i k => EvenPrep14.highTime (i.castLE (by decide))^k.val
def respPred : Matrix (Fin 4) (Fin 9) ℚ := fun i k =>
  EvenPrep14.highTime i^(k.val+1)/((k.val+1 : ℕ):ℚ) - γ*EvenPrep14.highTime i^k.val
def resp : Matrix BankIndex (Fin 9) ℚ :=
  combineRows respMom (combineRows respPoint respPred)
def F : Matrix (Fin 15) BankIndex ℚ :=
  fun i j => feedMap i (finSumFinEquiv (Sum.map id finSumFinEquiv j))

private theorem obsMom (i : Fin 6) (t : FiniteRootedTree) (hs : (t.order : ℕ) ≤ 9) :
    momentRows 6 b0 c0 i ⬝ᵥ normalized A0 t =
      respMom i ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ht := t.order.pos
  have h' : i.val+((t.order : ℕ)-1)+1 = (t.order : ℕ)+i.val := by omega
  have h : (t.order : ℕ)+i.val ≤ 14 := by have := i.isLt; omega
  have hc : clocks A0 = c0 := EvenPrep14.clocks_eq
  change read b0 c0 i.val (normalized A0 t) = _
  rw [← hc, read_eq_moment, moment EvenPrep14.order t i.val h]
  simp only [respMom,h']

private theorem obsPt (i : Fin 3) (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ 9) :
    recPoint i ⬝ᵥ normalized A0 t =
      respPoint i ⟨(t.order : ℕ)-1, by omega⟩ := by
  have hh := EvenPrep14.pure_high (i.castLE (by decide : 3 ≤ 4)) t h
  rw [EvenPrep14.high_clock] at hh
  simpa only [recPoint,respPoint,single_dotProduct,one_mul] using hh

private theorem obsPred (i : Fin 4) (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ 8) :
    recPred i ⬝ᵥ normalized A0 t =
      respPred i ⟨(t.order : ℕ)-1, by omega⟩ := by
  have hh := pure_predecessor (donor i) (EvenPrep14.pure_high i) γ t h
  rw [show donor i = EvenPrep14.highIndex i by rfl, EvenPrep14.high_clock] at hh
  have e : (t.order : ℕ)-1+1 = (t.order : ℕ) := by have := t.order.pos; omega
  simpa only [recPred,respPred,donor,e] using hh

private theorem obs_col (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ 8) :
    bank *ᵥ normalized A0 t = resp.col ⟨(t.order : ℕ)-1, by omega⟩ := by
  funext i
  cases i with
  | inl j => exact obsMom j t (by omega)
  | inr idx =>
    cases idx with
    | inl j => exact obsPt j t (by omega)
    | inr j => exact obsPred j t h

private theorem Ueq : Utail=F*bank := checkMat _ _ (by decide +kernel)
def E : Matrix (Fin 15) (Fin 9) ℚ := fun i k => site i^k.val
def IE : Matrix (Fin 15) (Fin 9) ℚ := fun i k => site i^(k.val+1)/((k.val+1 : ℕ) : ℚ)

private theorem integrated (i : Fin 15) (k : Fin 8) :
    (F*resp+Btail*E) i k.castSucc = IE i k.castSucc :=
  of_decide_eq_true (check2 (fun (i : Fin 15) (k : Fin 8) =>
    decide ((F*resp+Btail*E) i k.castSucc = IE i k.castSucc)) (by decide +kernel) i k)

private theorem paidFeed (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 8) :
    Utail *ᵥ normalized A0 t + Btail *ᵥ (site^((t.order : ℕ)-1)) =
      ((1 / (t.order : ℚ)) : ℚ) • site^(t.order : ℕ) := by
  have ho := t.order.pos
  let k : Fin 8 := ⟨(t.order : ℕ)-1, by omega⟩
  have hk : k.castSucc.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  have he : site^((t.order : ℕ)-1) = E.col k.castSucc := rfl
  rw [Ueq, ← Matrix.mulVec_mulVec, obs_col t ht, he]
  funext i
  change (F*resp+Btail*E) i k.castSucc = ((1 / (t.order : ℚ)) : ℚ) * site i^(t.order : ℕ)
  rw [integrated]
  simp only [IE,hk,div_eq_mul_inv,one_mul,mul_comm]

private theorem quad (j : Fin 16) :
    read weights site j.val 1 = 1 / ((j.val+1 : ℕ) : ℚ) :=
  of_decide_eq_true (check1 (fun i : Fin 16 => decide (read weights site i.val 1=1/((i.val+1 : ℕ):ℚ)))
    (by decide +kernel) j)
private theorem Grows : momentRows 7 weights site * Btail = G * momentRows 8 weights site :=
  checkMat _ _ (by decide +kernel)
private theorem Urows : momentRows 7 weights site * Utail = H * momentRows 8 b0 (clocks A0) := by
  rw [EvenPrep14.clocks_eq]
  exact checkMat _ _ (by decide +kernel)
private theorem Gbound (j : Fin 7) (k : Fin 8) (h : j.val+1 < k.val) : G j k = 0 :=
  (of_decide_eq_true (check2 (fun j k => decide (j.val+1 ≥ k.val ∨ G j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h)
private theorem Hbound (j : Fin 7) (k : Fin 8) (hk : j.val ≤ k.val) : H j k = 0 :=
  (of_decide_eq_true (check2 (fun (j : Fin 7) (k : Fin 8) =>
      decide (k.val < j.val ∨ H j k = 0)) (by decide +kernel) j k)).resolve_left (not_lt_of_ge hk)
private theorem payOld (j : Fin 7) (t : FiniteRootedTree) (_ : 8 < (t.order : ℕ))
    (ht : (t.order : ℕ)+j.val+1 ≤ 16) :
    (H * momentRows 8 b0 (clocks A0)) j ⬝ᵥ normalized A0 t =
      ∑ k : Fin 8, H j k * (1 / (((t.order : ℕ)+k.val : ℕ) : ℚ)) := by
  change (H j ᵥ* momentRows 8 b0 (clocks A0)) ⬝ᵥ normalized A0 t = _
  rw [← Matrix.dotProduct_mulVec]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : j.val ≤ k.val
  · rw [Hbound j k hk, zero_mul, zero_mul]
  · change H j k * read b0 (clocks A0) k.val (normalized A0 t) = _
    rw [read_eq_moment, moment EvenPrep14.order t k.val (by omega)]

private theorem scalarPay (j : Fin 7) (m : ℕ) (hm : 8 < m) (hp : m+j.val+1 ≤ 16) :
    (m : ℚ) * (∑ k : Fin 8, G j k * (1 / ((m+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 8, H j k * (1 / ((m+k.val : ℕ) : ℚ))) =
      1 / ((m+j.val+1 : ℕ) : ℚ) := by
  let m' : Fin 16 := ⟨m,by omega⟩
  have hh := of_decide_eq_true (check2 (fun (j : Fin 7) (n : Fin 16) => decide (
    n.val ≤ 8 ∨ 16 < n.val+j.val+1 ∨
    (n.val : ℚ) * (∑ k : Fin 8, G j k * (1 / ((n.val+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 8, H j k * (1 / ((n.val+k.val : ℕ) : ℚ))) =
      1 / ((n.val+j.val+1 : ℕ) : ℚ))) (by decide +kernel) j m')
  exact (hh.resolve_left (not_le_of_gt hm)).resolve_left (not_lt_of_ge hp)
private def transfer : GeneralAdjoints 8 7 A0 Utail Btail weights site where
  G := G
  H := H
  oldRow := H * momentRows 8 b0 (clocks A0)
  gbound := Gbound
  rows := general_rows_from_matrices G _ Grows Urows
  old_pay := payOld
  scalar := scalarPay

def Ablock := tableau A0 Utail Btail
def bblock : Fin 41 ⊕ Fin 15 → ℚ := Sum.elim 0 weights
theorem orderBlock : HasOrder 16 Ablock bblock :=
  general_tail_hasOrder (by decide : 7 ≤ 8+1) (fun j hj => quad ⟨j,hj⟩) paidFeed transfer

def flat : (Fin 41 ⊕ Fin 15) ≃ Fin 56 := finSumFinEquiv
def Av := shifted flat Ablock
def bv := bblock ∘ flat.symm
def Sv : Matrix (Fin 56) (Fin 56) ℚ := fun i j => if i≤j then 0 else Av i j
private theorem strictS : ∀ i j : Fin 56, i≤j → Sv i j=0 := by
  intro i j hij
  simp [Sv,hij]
private theorem new_lower : Btail.IsLowerTriangular := by
  change ∀ ⦃i j : Fin 15⦄, i < j → Btail i j = 0
  intro i j z
  have hh := of_decide_eq_true (check2 (fun (i j : Fin 15) => decide (j ≤ i ∨ Btail i j = 0))
    (by decide +kernel) i j)
  exact hh.resolve_left (not_le_of_gt z)
private theorem new_diagonal (i : Fin 15) : Btail i i = γ :=
  of_decide_eq_true (check1 (fun i : Fin 15 => decide (Btail i i = γ)) (by decide +kernel) i)
private theorem virt_eq : Av=Sv+Matrix.diagonal (fun _ => γ) :=
  strict_diag_reassembly Av γ
    (chronological_lower (U := Utail) (EvenPrep14.physical 14).1 new_lower)
    (chronological_diagonal (U := Utail) γ (EvenPrep14.physical 14).2.1 new_diagonal)
abbrev redirect : Fin 56 → Fin 52 := redirectHead (fresh := 11) donor
abbrev keep : Fin 52 → Fin 56 := keepHead 41 4 11

theorem copies (i j : Fin 56) : Sv i j = Sv (keep (redirect i)) j := by
  apply eq_of_actual_copies (fresh := 11) donor Sv _ i j
  intro kk ll
  exact of_decide_eq_true (check2 (fun (i : Fin 4) (j : Fin 56) => decide
    (Sv (copyIndex 41 11 i) j = Sv (keep (donorLift 11 (donor i))) j))
    (by decide +kernel) kk ll)

def A : Matrix (Fin 52) (Fin 52) ℚ := fastFoldMatrix (fresh := 11) donor Av
def b : Fin 52 → ℚ := fastFoldWeights (fresh := 11) donor bv
theorem Aeq : A = foldedMatrix redirect keep Av := fastFoldMatrix_eq (fresh := 11) donor Av
theorem beq : b = foldedWeights redirect bv := fastFoldWeights_eq (fresh := 11) donor bv
private theorem physical (p : ℕ) :
    A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ (HasOrder p Av bv ↔ HasOrder p A b) := by
  have h := copiedHead_merge (fresh := 11) donor Sv γ copies strictS bv p
  rw [Aeq,beq,virt_eq]
  exact h
theorem order : HasOrder 16 A b :=
  (physical 16).2.2.mp ((order_shifted flat Ablock bblock 16).mpr orderBlock)

private theorem respects : Respects Av redirect keep := by
  have h := respects_literal Sv γ redirect keep (redirect_keepHead (fresh := 11) donor) copies
  rw [← virt_eq] at h
  exact h

def c : Fin 52 → ℚ := (Sum.elim c0 site) ∘ flat.symm ∘ keep
theorem clocks_eq : clocks A = c := by
  rw [Aeq]
  have hv : clocks Av = clocks (foldedMatrix redirect keep Av) ∘ redirect :=
    mulVec_pullback respects 1
  have hv0 : clocks Av = clocks Ablock ∘ flat.symm := action_shifted flat Ablock 1
  have hh : clocks Ablock = Sum.elim c0 site := by
    funext i
    cases i with
    | inl i =>
      have h := congrFun (head_action A0 Utail Btail 1) i
      change clocks Ablock (Sum.inl i) = clocks A0 i at h
      rw [EvenPrep14.clocks_eq] at h
      exact h
    | inr i => exact congrFun (tail_clocks_from_feed (by decide : 1 ≤ 8) paidFeed) i
  rw [hh] at hv0
  rw [hv0] at hv
  funext i
  have h := congrFun hv (keep i)
  simp only [Function.comp_apply, redirect_keepHead] at h
  exact h.symm

def headVirtual (i : Fin 8) : Fin 15 := i.castLE (by decide)
def headIndex (i : Fin 8) : Fin 52 := redirect (flat (Sum.inr (headVirtual i)))
def headTime (i : Fin 8) : ℚ := site (headVirtual i)
def highVirtual (i : Fin 4) : Fin 15 := ⟨4+i.val,by have := i.isLt; omega⟩
def highIndex (i : Fin 4) : Fin 52 := redirect (flat (Sum.inr (highVirtual i)))
def highTime (i : Fin 4) : ℚ := site (highVirtual i)

theorem head_clock (i : Fin 8) : clocks A (headIndex i) = headTime i := by
  rw [clocks_eq]
  exact of_decide_eq_true (check1 (fun i : Fin 8 => decide (c (headIndex i) = headTime i))
    (by decide +kernel) i)
theorem high_clock (i : Fin 4) : clocks A (highIndex i) = highTime i := by
  rw [clocks_eq]
  exact of_decide_eq_true (check1 (fun i : Fin 4 => decide (c (highIndex i) = highTime i))
    (by decide +kernel) i)

private theorem transport_pure (j : Fin 15) (n : ℕ)
    (hp : PureAt Ablock (Sum.inr j) n) :
    PureAt A (redirect (flat (Sum.inr j))) n := by
  have hv : PureAt Av (flat (Sum.inr j)) n := by
    apply (pure_shifted_iff Ablock flat _ _).mpr
    rw [Equiv.symm_apply_apply]
    exact hp
  rw [Aeq]
  exact (pure_folded_iff respects _ _).mp hv

theorem pure_head (i : Fin 8) : PureAt A (headIndex i) 9 := by
  apply transport_pure
  intro t ht
  have h := congrFun (low_pure paidFeed t ht) (headVirtual i)
  have hc := congrFun (tail_clocks_from_feed (by decide : 1≤8) paidFeed) (headVirtual i)
  change clocks Ablock (Sum.inr (headVirtual i)) = site (headVirtual i) at hc
  rw [hc]
  exact h

private theorem FzeroPred (i : Fin 4) (j : Fin 4) :
    F (highVirtual i) (Sum.inr (Sum.inr j)) = 0 :=
  of_decide_eq_true (check2 (fun (i : Fin 4) (j : Fin 4) => decide
    (F (highVirtual i) (Sum.inr (Sum.inr j)) = 0)) (by decide +kernel) i j)

private theorem top_bank (i : Fin 4) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 9) :
    (Utail *ᵥ normalized A0 t) (highVirtual i) =
      (F*resp) (highVirtual i) ⟨(t.order : ℕ)-1,by omega⟩ := by
  rw [Ueq, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases j with
  | inl j =>
    have hh := obsMom j t ht
    change F (highVirtual i) (Sum.inl j) * (momentRows 6 b0 c0 j ⬝ᵥ normalized A0 t) =
      F (highVirtual i) (Sum.inl j) * respMom j ⟨(t.order : ℕ)-1,by omega⟩
    rw [hh]
  | inr k =>
    cases k with
    | inl j =>
      have hh := obsPt j t ht
      change F (highVirtual i) (Sum.inr (Sum.inl j)) * (recPoint j ⬝ᵥ normalized A0 t) =
        F (highVirtual i) (Sum.inr (Sum.inl j)) * respPoint j ⟨(t.order : ℕ)-1,by omega⟩
      rw [hh]
    | inr j => simp [FzeroPred]

private theorem top_integrates (i : Fin 4) (k : Fin 9) :
    (F*resp+Btail*E) (highVirtual i) k = IE (highVirtual i) k :=
  of_decide_eq_true (check2 (fun (i : Fin 4) (k : Fin 9) => decide
    ((F*resp+Btail*E) (highVirtual i) k = IE (highVirtual i) k)) (by decide +kernel) i k)

private theorem top_paid (i : Fin 4) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 9) :
    (Utail *ᵥ normalized A0 t+Btail *ᵥ (site^((t.order : ℕ)-1))) (highVirtual i) =
      site (highVirtual i) ^ (t.order : ℕ)/(t.order : ℚ) := by
  rw [Pi.add_apply,top_bank i t ht]
  let k : Fin 9 := ⟨(t.order : ℕ)-1,by omega⟩
  change (F*resp+Btail*E) (highVirtual i) k = site (highVirtual i)^(t.order : ℕ)/(t.order : ℚ)
  rw [top_integrates]
  have hk : k.val+1=(t.order : ℕ) := by dsimp [k]; have := t.order.pos; omega
  simp only [IE,hk]

theorem pure_high (i : Fin 4) : PureAt A (highIndex i) 10 :=
  transport_pure _ _ (protected_pure (by decide : 1≤8) paidFeed (highVirtual i) (top_paid i))

#print axioms order
#print axioms pure_head
#print axioms pure_high
end RKResearch.Certified.EvenPrep16
