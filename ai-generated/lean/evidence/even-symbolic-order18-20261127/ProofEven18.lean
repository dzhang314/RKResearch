module

public import ProofEvenPrep16
import all ProofEvenPrep16
public import Even18Data
public import RKCert.ReviewedNative.GeneralMomentTail
public import RKCert.ReviewedNative.CausalCopyLocal
public import RKCert.ReviewedNative.ProtectedTail

@[expose] public section

namespace RKResearch.Certified.EvenTerminal18
open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge Even18Data
open scoped Matrix BigOperators

set_option maxHeartbeats 10000000
set_option maxRecDepth 16000
set_option Elab.async false
abbrev A0 := EvenPrep16.A
abbrev b0 := EvenPrep16.b
abbrev c0 := EvenPrep16.c
abbrev γ : ℚ := (1:ℚ)/4

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

def observed : Matrix (Fin 9) (Fin 52) ℚ := fun i =>
  if i.val < 8 then b0*c0^i.val else Pi.single (EvenPrep16.headIndex 0) 1
def momentMatrix : Matrix (Fin 9) (Fin 9) ℚ := fun i k =>
  if i.val < 8 then 1 / ((i.val+k.val+1 : ℕ) : ℚ) else EvenPrep16.headTime 0 ^ k.val
def D : Matrix (Fin 9) (Fin 52) ℚ := inverse * observed

private theorem observed_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 9) :
    observed *ᵥ normalized A0 t =
      momentMatrix.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  funext j
  have hn := t.order.pos
  have hk : j.val+((t.order : ℕ)-1)+1 = (t.order : ℕ)+j.val := by omega
  simp only [Matrix.mulVec, observed, Matrix.col_apply, momentMatrix]
  split_ifs with hs
  · rw [hk, ← moment EvenPrep16.order t j.val (by omega), EvenPrep16.clocks_eq]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ac_rfl
  · have hd := EvenPrep16.pure_head 0 t ht
    have hc := EvenPrep16.head_clock 0
    rw [hc] at hd
    simpa only [single_dotProduct,one_mul] using hd

theorem decoder : IsDecoder A0 8 D := by
  have hmul : inverse * momentMatrix = (1 : Matrix (Fin 9) (Fin 9) ℚ) :=
    checkMat _ _ (by decide +kernel)
  intro t ht
  rw [D, ← Matrix.mulVec_mulVec, observed_exact t ht,
    ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

def predRows : Matrix (Fin 8) (Fin 52) ℚ := fun i =>
  A0 (EvenPrep16.headIndex i) - Pi.single (EvenPrep16.headIndex i) γ
def targetRows : Matrix (Fin 8) (Fin 9) ℚ := fun i k =>
  EvenPrep16.headTime i^(k.val+1) / ((k.val+1 : ℕ) : ℚ) - γ*EvenPrep16.headTime i^k.val

def bank : Matrix (Fin 9 ⊕ Fin 8) (Fin 52) ℚ := combineRows observed predRows
def bankResp : Matrix (Fin 9 ⊕ Fin 8) (Fin 9) ℚ := combineRows momentMatrix targetRows
def F : Matrix (Fin 17) (Fin 9 ⊕ Fin 8) ℚ := fun i j => feedMap i (finSumFinEquiv j)

private theorem bank_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 8) :
    bank *ᵥ normalized A0 t =
      bankResp.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ho := t.order.pos
  have hk : (t.order : ℕ)-1+1 = (t.order : ℕ) := by omega
  funext j
  cases j with
  | inl i => exact congrFun (observed_exact t (by omega)) i
  | inr i =>
    have h := pure_predecessor (EvenPrep16.headIndex i) (EvenPrep16.pure_head i) γ t ht
    rw [EvenPrep16.head_clock] at h
    change (A0 (EvenPrep16.headIndex i) - Pi.single (EvenPrep16.headIndex i) γ) ⬝ᵥ normalized A0 t =
      EvenPrep16.headTime i^(((t.order : ℕ)-1)+1)/(((t.order : ℕ)-1+1 : ℕ):ℚ) -
      γ*EvenPrep16.headTime i^((t.order : ℕ)-1)
    rw [hk]
    exact h

private theorem Ueq : Utail = F*bank := checkMat _ _ (by decide +kernel)
def E : Matrix (Fin 17) (Fin 9) ℚ := fun i k => site i^k.val
def IE : Matrix (Fin 17) (Fin 9) ℚ := fun i k => site i^(k.val+1)/((k.val+1 : ℕ) : ℚ)
private theorem integrated (i : Fin 17) (k : Fin 8) :
    (F*bankResp+Btail*E) i k.castSucc = IE i k.castSucc :=
  of_decide_eq_true (check2 (fun (i : Fin 17) (k : Fin 8) =>
    decide ((F*bankResp+Btail*E) i k.castSucc = IE i k.castSucc)) (by decide +kernel) i k)

private theorem paidFeed (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 8) :
    Utail *ᵥ normalized A0 t + Btail *ᵥ (site^((t.order : ℕ)-1)) =
      ((1 / (t.order : ℚ)) : ℚ) • site^(t.order : ℕ) := by
  have ho := t.order.pos
  let k : Fin 8 := ⟨(t.order : ℕ)-1, by omega⟩
  have hk : k.castSucc.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  have he : site^((t.order : ℕ)-1) = E.col k.castSucc := rfl
  rw [Ueq, ← Matrix.mulVec_mulVec, bank_exact t ht, he]
  funext i
  change (F*bankResp+Btail*E) i k.castSucc = ((1 / (t.order : ℚ)) : ℚ) * site i^(t.order : ℕ)
  rw [integrated]
  simp only [IE,hk,div_eq_mul_inv,one_mul,mul_comm]

private theorem quad (j : Fin 18) :
    read weights site j.val 1 = 1 / ((j.val+1 : ℕ) : ℚ) :=
  of_decide_eq_true (check1 (fun i : Fin 18 => decide (read weights site i.val 1=1/((i.val+1 : ℕ):ℚ)))
    (by decide +kernel) j)
private theorem Grows : momentRows 9 weights site * Btail = G * momentRows 10 weights site :=
  checkMat _ _ (by decide +kernel)
private theorem Urows : momentRows 9 weights site * Utail = oneSpareOld b0 (clocks A0) D H := by
  rw [EvenPrep16.clocks_eq]
  exact checkMat _ _ (by decide +kernel)
private theorem Gbound (j : Fin 9) (k : Fin 10) (h : j.val+1 < k.val) : G j k = 0 :=
  (of_decide_eq_true (check2 (fun j k => decide (j.val+1 ≥ k.val ∨ G j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h)
private theorem Hbound (j : Fin 9) (k : Fin 10) (h : j.val+1 < 9) (hk : j.val ≤ k.val) : H j k = 0 :=
  (of_decide_eq_true (check2 (fun (j : Fin 9) (k : Fin 10) =>
      decide (9 ≤ j.val+1 ∨ k.val < j.val ∨ H j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h) |>.resolve_left (not_lt_of_ge hk)
private theorem scalarPay (j : Fin 9) (m : ℕ) (hm : 8 < m) (hp : m+j.val+1 ≤ 18) :
    (m : ℚ) * (∑ k : Fin 10, G j k * (1 / ((m+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 10, H j k * (1 / ((m+k.val : ℕ) : ℚ))) =
      1 / ((m+j.val+1 : ℕ) : ℚ) := by
  let m' : Fin 18 := ⟨m,by omega⟩
  have hh := of_decide_eq_true (check2 (fun (j : Fin 9) (n : Fin 18) => decide (
    n.val ≤ 8 ∨ 18 < n.val+j.val+1 ∨
    (n.val : ℚ) * (∑ k : Fin 10, G j k * (1 / ((n.val+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 10, H j k * (1 / ((n.val+k.val : ℕ) : ℚ))) =
      1 / ((n.val+j.val+1 : ℕ) : ℚ))) (by decide +kernel) j m')
  exact (hh.resolve_left (not_le_of_gt hm)).resolve_left (not_lt_of_ge hp)

private def transfer : GeneralAdjoints 8 9 A0 Utail Btail weights site where
  G := G
  H := H
  oldRow := oneSpareOld b0 (clocks A0) D H
  gbound := Gbound
  rows := general_rows_from_matrices G _ Grows Urows
  old_pay := oneSpare_pay decoder EvenPrep16.order H Hbound
  scalar := scalarPay

def Ablock := tableau A0 Utail Btail
def bblock : Fin 52 ⊕ Fin 17 → ℚ := Sum.elim 0 weights
theorem orderBlock : HasOrder 18 Ablock bblock :=
  general_tail_hasOrder (by decide : 9 ≤ 8+1) (fun j hj => quad ⟨j,hj⟩) paidFeed transfer
private theorem unpaid_bush : (19 : ℚ) * read weights site 18 1 ≠ 1 := by decide +kernel
theorem noNextBlock : ¬ HasOrder 19 Ablock bblock := by
  intro h
  have hb := h.hasQuadratureOrder 18 (by decide)
  have hc := tail_clocks_from_feed (by decide : 1 ≤ 8) paidFeed
  change (19 : ℚ) * (bblock ⬝ᵥ (clocks Ablock)^18) = 1 at hb
  apply unpaid_bush
  have he : bblock ⬝ᵥ (clocks Ablock)^18 = read weights site 18 1 := by
    rw [Matrix.dotProduct_block]
    have htail : ((clocks Ablock)^18) ∘ Sum.inr = site^18 := by
      funext i
      simpa [Function.comp_apply, Pi.pow_apply, tail, Ablock] using
        congrArg (fun x : ℚ => x^18) (congrFun hc i)
    rw [htail]
    simp [bblock,read_eq_moment]
  rw [← he]
  exact hb

def flat : (Fin 52 ⊕ Fin 17) ≃ Fin 69 := finSumFinEquiv
def Av := shifted flat Ablock
def bv := bblock ∘ flat.symm
def Sv : Matrix (Fin 69) (Fin 69) ℚ := fun i j => if i≤j then 0 else Av i j
private theorem strictS : ∀ i j : Fin 69, i≤j → Sv i j=0 := by
  intro i j hij
  simp [Sv,hij]
private theorem new_lower : Btail.IsLowerTriangular := by
  change ∀ ⦃i j : Fin 17⦄, i < j → Btail i j = 0
  intro i j h
  have hh := of_decide_eq_true (check2 (fun (i j : Fin 17) => decide (j ≤ i ∨ Btail i j = 0))
    (by decide +kernel) i j)
  exact hh.resolve_left (not_le_of_gt h)
private theorem new_diagonal (i : Fin 17) : Btail i i = γ :=
  of_decide_eq_true (check1 (fun i : Fin 17 => decide (Btail i i = γ)) (by decide +kernel) i)
private theorem virt_eq : Av=Sv+Matrix.diagonal (fun _ => γ) :=
  strict_diag_reassembly Av γ
    (chronological_lower (U := Utail) (EvenPrep16.physical 16).1 new_lower)
    (chronological_diagonal (U := Utail) γ (EvenPrep16.physical 16).2.1 new_diagonal)
abbrev redirect : Fin 69 → Fin 61 := redirectHead (fresh := 9) EvenPrep16.headIndex
abbrev keep : Fin 61 → Fin 69 := keepHead 52 8 9

theorem copies (i j : Fin 69) : Sv i j = Sv (keep (redirect i)) j := by
  apply eq_of_actual_copies (fresh := 9) EvenPrep16.headIndex Sv _ i j
  intro k l
  exact of_decide_eq_true (check2 (fun (k : Fin 8) (l : Fin 69) => decide
    (Sv (copyIndex 52 9 k) l = Sv (keep (donorLift 9 (EvenPrep16.headIndex k))) l))
    (by decide +kernel) k l)

def A := foldedMatrix redirect keep Av
def b := foldedWeights redirect bv
private theorem physical (p : ℕ) :
    A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ (HasOrder p Av bv ↔ HasOrder p A b) := by
  have h := copiedHead_merge (fresh := 9) EvenPrep16.headIndex Sv γ copies strictS bv p
  unfold A b
  rw [virt_eq]
  exact h
theorem order : HasOrder 18 A b :=
  (physical 18).2.2.mp ((order_shifted flat Ablock bblock 18).mpr orderBlock)
theorem noNext : ¬ HasOrder 19 A b := by
  intro h
  exact noNextBlock ((order_shifted flat Ablock bblock 19).mp ((physical 19).2.2.mpr h))

theorem witness : ∃ (A : Matrix (Fin 61) (Fin 61) ℚ) (b : Fin 61 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ≠0 ∧ HasOrder 18 A b ∧ ¬ HasOrder 19 A b :=
  ⟨A,b,(physical 18).1,(physical 18).2.1,by decide +kernel,order,noNext⟩

#print axioms witness
#print axioms copies
end RKResearch.Certified.EvenTerminal18
