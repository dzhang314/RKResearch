module

public import Seed10Even
public import Even12Data
public import RKCert.ReviewedNative.GeneralMomentTail
public import RKCert.ReviewedNative.CausalStageMerge
public import RKCert.ReviewedNative.ProtectedTail

@[expose] public section

namespace RKResearch.Certified.EvenTerminal12
open FiniteRootedTree TwoDonorDense TwoOrderMomentTail CausalStageMerge Even12Data
open scoped Matrix BigOperators

set_option maxHeartbeats 10000000
set_option maxRecDepth 16000
set_option Elab.async false
abbrev A0 := StrictSDIRKGram22Order10.A
abbrev b0 := StrictSDIRKGram22Order10.b
abbrev c0 := StrictSDIRKGram22Order10.clocks
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

def observed : Matrix (Fin 6) (Fin 22) ℚ := fun i =>
  if i.val < 5 then b0*c0^i.val else Pi.single (Seed10Even.donor 0) 1
def momentMatrix : Matrix (Fin 6) (Fin 6) ℚ := fun i k =>
  if i.val < 5 then 1 / ((i.val+k.val+1 : ℕ) : ℚ) else (-3:ℚ)^k.val
def D : Matrix (Fin 6) (Fin 22) ℚ := inverse * observed

private theorem observed_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 6) :
    observed *ᵥ normalized A0 t =
      momentMatrix.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  funext j
  have hn := t.order.pos
  have hk : j.val+((t.order : ℕ)-1)+1 = (t.order : ℕ)+j.val := by omega
  simp only [Matrix.mulVec, observations, observed, Matrix.col_apply, momentMatrix]
  split_ifs with hs
  · rw [hk, ← moment StrictSDIRKGram22Order10.order t j.val (by omega), Seed10Even.clocks_eq]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ac_rfl
  · have hd := Seed10Even.donor_pure 0 t ht
    have hc := Seed10Even.donor_clock 0
    have hval : Seed10Even.donorTime 0 = (-3:ℚ) := by decide +kernel
    rw [hc,hval] at hd
    simpa only [single_dotProduct,one_mul] using hd

theorem decoder : IsDecoder A0 5 D := by
  have hmul : inverse * momentMatrix = (1 : Matrix (Fin 6) (Fin 6) ℚ) :=
    checkMat _ _ (by decide +kernel)
  intro t ht
  rw [D, ← Matrix.mulVec_mulVec, observed_exact t ht,
    ← Matrix.mulVec_single_one, Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]

def predRows : Matrix (Fin 5) (Fin 22) ℚ := fun i =>
  A0 (Seed10Even.donor i) - Pi.single (Seed10Even.donor i) γ
def targetRows : Matrix (Fin 5) (Fin 6) ℚ := fun i k =>
  Seed10Even.donorTime i^(k.val+1) / ((k.val+1 : ℕ) : ℚ) - γ*Seed10Even.donorTime i^k.val

def bank : Matrix (Fin 6 ⊕ Fin 5) (Fin 22) ℚ := combineRows observed predRows
def bankResp : Matrix (Fin 6 ⊕ Fin 5) (Fin 6) ℚ := combineRows momentMatrix targetRows
def F : Matrix (Fin 11) (Fin 6 ⊕ Fin 5) ℚ := fun i j => feedMap i (finSumFinEquiv j)

private theorem bank_exact (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 5) :
    bank *ᵥ normalized A0 t =
      bankResp.col ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ho := t.order.pos
  have hk : (t.order : ℕ)-1+1 = (t.order : ℕ) := by omega
  funext j
  cases j with
  | inl i => exact congrFun (observed_exact t (by omega)) i
  | inr i =>
    have h := pure_predecessor (Seed10Even.donor i) (Seed10Even.donor_pure i) γ t ht
    rw [Seed10Even.donor_clock] at h
    change (A0 (Seed10Even.donor i) - Pi.single (Seed10Even.donor i) γ) ⬝ᵥ normalized A0 t =
      Seed10Even.donorTime i^(((t.order : ℕ)-1)+1)/(((t.order : ℕ)-1+1 : ℕ):ℚ) -
      γ*Seed10Even.donorTime i^((t.order : ℕ)-1)
    rw [hk]
    exact h

private theorem Ueq : Utail = F*bank := checkMat _ _ (by decide +kernel)
def E : Matrix (Fin 11) (Fin 6) ℚ := fun i k => site i^k.val
def IE : Matrix (Fin 11) (Fin 6) ℚ := fun i k => site i^(k.val+1)/((k.val+1 : ℕ) : ℚ)
private theorem integrated (i : Fin 11) (k : Fin 5) :
    (F*bankResp+Btail*E) i k.castSucc = IE i k.castSucc :=
  of_decide_eq_true (check2 (fun (i : Fin 11) (k : Fin 5) =>
    decide ((F*bankResp+Btail*E) i k.castSucc = IE i k.castSucc)) (by decide +kernel) i k)

private theorem paidFeed (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ 5) :
    Utail *ᵥ normalized A0 t + Btail *ᵥ (site^((t.order : ℕ)-1)) =
      ((1 / (t.order : ℚ)) : ℚ) • site^(t.order : ℕ) := by
  have ho := t.order.pos
  let k : Fin 5 := ⟨(t.order : ℕ)-1, by omega⟩
  have hk : k.castSucc.val+1 = (t.order : ℕ) := by dsimp [k]; omega
  have he : site^((t.order : ℕ)-1) = E.col k.castSucc := rfl
  rw [Ueq, ← Matrix.mulVec_mulVec, bank_exact t ht, he]
  funext i
  change (F*bankResp+Btail*E) i k.castSucc = ((1 / (t.order : ℚ)) : ℚ) * site i^(t.order : ℕ)
  rw [integrated]
  simp only [IE,hk,div_eq_mul_inv,one_mul,mul_comm]

private theorem quad (j : Fin 12) :
    read weights site j.val 1 = 1 / ((j.val+1 : ℕ) : ℚ) :=
  of_decide_eq_true (check1 (fun i : Fin 12 => decide (read weights site i.val 1=1/((i.val+1 : ℕ):ℚ)))
    (by decide +kernel) j)
private theorem Grows : momentRows 6 weights site * Btail = G * momentRows 7 weights site :=
  checkMat _ _ (by decide +kernel)
private theorem Urows : momentRows 6 weights site * Utail = oneSpareOld b0 (clocks A0) D H := by
  rw [Seed10Even.clocks_eq]
  exact checkMat _ _ (by decide +kernel)
private theorem Gbound (j : Fin 6) (k : Fin 7) (h : j.val+1 < k.val) : G j k = 0 :=
  (of_decide_eq_true (check2 (fun j k => decide (j.val+1 ≥ k.val ∨ G j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h)
private theorem Hbound (j : Fin 6) (k : Fin 7) (h : j.val+1 < 6) (hk : j.val ≤ k.val) : H j k = 0 :=
  (of_decide_eq_true (check2 (fun (j : Fin 6) (k : Fin 7) =>
      decide (6 ≤ j.val+1 ∨ k.val < j.val ∨ H j k = 0))
    (by decide +kernel) j k)).resolve_left (not_le_of_gt h) |>.resolve_left (not_lt_of_ge hk)
private theorem scalarPay (j : Fin 6) (m : ℕ) (hm : 5 < m) (hp : m+j.val+1 ≤ 12) :
    (m : ℚ) * (∑ k : Fin 7, G j k * (1 / ((m+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 7, H j k * (1 / ((m+k.val : ℕ) : ℚ))) =
      1 / ((m+j.val+1 : ℕ) : ℚ) := by
  let m' : Fin 12 := ⟨m,by omega⟩
  have hh := of_decide_eq_true (check2 (fun (j : Fin 6) (n : Fin 12) => decide (
    n.val ≤ 5 ∨ 12 < n.val+j.val+1 ∨
    (n.val : ℚ) * (∑ k : Fin 7, G j k * (1 / ((n.val+k.val : ℕ) : ℚ)) +
      ∑ k : Fin 7, H j k * (1 / ((n.val+k.val : ℕ) : ℚ))) =
      1 / ((n.val+j.val+1 : ℕ) : ℚ))) (by decide +kernel) j m')
  exact (hh.resolve_left (not_le_of_gt hm)).resolve_left (not_lt_of_ge hp)

private def transfer : GeneralAdjoints 5 6 A0 Utail Btail weights site where
  G := G
  H := H
  oldRow := oneSpareOld b0 (clocks A0) D H
  gbound := Gbound
  rows := general_rows_from_matrices G _ Grows Urows
  old_pay := oneSpare_pay decoder StrictSDIRKGram22Order10.order H Hbound
  scalar := scalarPay

def Ablock := tableau A0 Utail Btail
def bblock : Fin 22 ⊕ Fin 11 → ℚ := Sum.elim 0 weights
theorem orderBlock : HasOrder 12 Ablock bblock :=
  general_tail_hasOrder (by decide : 6 ≤ 5+1) (fun j hj => quad ⟨j,hj⟩) paidFeed transfer
private theorem unpaid_bush : (13 : ℚ) * read weights site 12 1 ≠ 1 := by decide +kernel
theorem noNextBlock : ¬ HasOrder 13 Ablock bblock := by
  intro h
  have hb := h.hasQuadratureOrder 12 (by decide)
  have hc := tail_clocks_from_feed (by decide : 1 ≤ 5) paidFeed
  change (13 : ℚ) * (bblock ⬝ᵥ (clocks Ablock)^12) = 1 at hb
  apply unpaid_bush
  have he : bblock ⬝ᵥ (clocks Ablock)^12 = read weights site 12 1 := by
    rw [Matrix.dotProduct_block]
    have htail : ((clocks Ablock)^12) ∘ Sum.inr = site^12 := by
      funext i
      simpa [Function.comp_apply, Pi.pow_apply, tail, Ablock] using
        congrArg (fun x : ℚ => x^12) (congrFun hc i)
    rw [htail]
    simp [bblock,read_eq_moment]
  rw [← he]
  exact hb

def flat : (Fin 22 ⊕ Fin 11) ≃ Fin 33 := finSumFinEquiv
def Av := shifted flat Ablock
def bv := bblock ∘ flat.symm
def Sv : Matrix (Fin 33) (Fin 33) ℚ := fun i j => if i≤j then 0 else Av i j
private theorem strictS : ∀ i j : Fin 33, i≤j → Sv i j=0 := by
  intro i j hij
  simp [Sv,hij]
private theorem virt_eq : Av=Sv+Matrix.diagonal (fun _ => γ) := checkMat _ _ (by decide +kernel)
abbrev redirect : Fin 33 → Fin 28 := redirectHead (fresh := 6) Seed10Even.donor
abbrev keep : Fin 28 → Fin 33 := keepHead 22 5 6

theorem copies (i j : Fin 33) : Sv i j = Sv (keep (redirect i)) j :=
  of_decide_eq_true (check2 (fun i j => decide (Sv i j = Sv (keep (redirect i)) j)) (by decide +kernel) i j)

def A := foldedMatrix redirect keep Av
def b := foldedWeights redirect bv
private theorem physical (p : ℕ) :
    A.IsLowerTriangular ∧ (∀ i,A i i=γ) ∧ (HasOrder p Av bv ↔ HasOrder p A b) := by
  have h := copiedHead_merge (fresh := 6) Seed10Even.donor Sv γ copies strictS bv p
  unfold A b
  rw [virt_eq]
  exact h
theorem order : HasOrder 12 A b :=
  (physical 12).2.2.mp ((order_shifted flat Ablock bblock 12).mpr orderBlock)
theorem noNext : ¬ HasOrder 13 A b := by
  intro h
  exact noNextBlock ((order_shifted flat Ablock bblock 13).mp ((physical 13).2.2.mpr h))

theorem witness : ∃ (A : Matrix (Fin 28) (Fin 28) ℚ) (b : Fin 28 → ℚ),
    A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ≠0 ∧ HasOrder 12 A b ∧ ¬ HasOrder 13 A b :=
  ⟨A,b,(physical 12).1,(physical 12).2.1,by decide +kernel,order,noNext⟩

#print axioms witness
#print axioms copies
end RKResearch.Certified.EvenTerminal12
