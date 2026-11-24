module

public import RKCert.Dirk15SampleLift
public import RKCert.Dirk15NumericCoefficients
public import RKCert.CompanionNumericEntries
public import RKCert.ModularLUCompact

@[expose] public section

/-! # Actual companion samples discharged by packed determinant witnesses -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound RKCert.LU
open scoped Classical

local notation "F" => ZMod 1009

def singleAxes (n : ℕ) : OrderedAxes n 1 n where
  axis i _ := i
  strict _ _ _ h := by simp only [Fin.eq_zero _,lt_self_iff_false] at h
  injective := fun _ _ h => congrFun h 0
  card := (Nat.choose_one_right n).symm

def codeAxis (n : ℕ) (n0 : 0<n) (codes : Array ℕ) (i j : ℕ) : Fin n :=
  ⟨(get codes i/(8^j)%8)%n,Nat.mod_lt _ n0⟩

def codedAxes (n k h : ℕ) (n0 : 0<n) (codes : Array ℕ)
    (strict : ∀ i : Fin h, StrictMono (fun j : Fin k => codeAxis n n0 codes i.val j.val))
    (inj : Function.Injective (fun i : Fin h => fun j : Fin k => codeAxis n n0 codes i.val j.val))
    (ct : h=n.choose k) : OrderedAxes n k h :=
  ⟨fun i j => codeAxis n n0 codes i.val j.val,strict,inj,ct⟩

def rawPack : ℕ → (ℕ→ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0+base*rawPack n (fun r=>f (r+1))

theorem rawPack_exact (n : ℕ) (f : ℕ→ℕ) : rawPack n f=pack base n f := by
  induction n generalizing f with
  | zero => simp [rawPack,pack]
  | succ n ih => rw [rawPack,pack_succ,ih]

/-- Pack exactly one actual finite numeric row in the PLU verifier's radix. -/
def packedRow {h : ℕ} (f : Fin h→F) : ℕ :=
  rawPack h fun j => if lt : j<h then (f ⟨j,lt⟩).val else 0

theorem digit_packedRow {h : ℕ} (f : Fin h→F) (j : Fin h) :
    (digit (packedRow f) j.val:F)=f j := by
  unfold packedRow
  rw [rawPack_exact]
  change (lane _ (pack _ _ _) j.val:F)=_
  rw [lane_pack base (by decide) h _ _ j.isLt,dite_eq_left j.isLt,ZMod.natCast_zmod_val]
  intro k lt
  rw [dite_eq_left lt]
  exact (ZMod.val_lt _).trans_le (by decide : 1009≤base)

def sampleMomentEntry {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ)
    (u : F) (b : Fin (n+1)→F) (i t : Fin h) : F :=
  numericMomentEntry E M j w u b (fun s => s.val) i t

theorem rawMomentNorm_eval_of_packed {n k h : ℕ} (E : OrderedAxes n k h) (ks : k<1009)
    (M j w : ℕ) (u : F) (b : Fin (n+1)→F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin h,packedRow (sampleMomentEntry E M j w u b i)=get rows i.val)
    (paid : (rowMatrix 1009 h rows).det=v) :
    rawMomentNorm k M j w u b=v := by
  classical
  unfold rawMomentNorm
  apply of_rows_equiv _ E.index rows v _ paid
  intro i t
  rw [←entry i,digit_packedRow]
  exact (numericMomentEntry_exact E M j w u b _ (sampleSite_injective ks) i t).symm

theorem nodeMomentNorm_eval_from_rows {n k h : ℕ} (E : OrderedAxes n k h) (ks : k<1009)
    (j w : ℕ) (u : F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin h,packedRow (sampleMomentEntry E order15Scale j w u (nodeCoefficientsAt n u) i)=
      get rows i.val)
    (paid : (rowMatrix 1009 h rows).det=v) :
    (nodeMomentNorm n k j w).eval₂ order15Reduce u=v := by
  rw [nodeMomentNorm_at]
  exact rawMomentNorm_eval_of_packed E ks order15Scale j w u _ rows v entry paid

theorem anchorMomentNorm_eval_from_rows {n k h : ℕ} (E : OrderedAxes (n+1) k h) (ks : k<1009)
    (j : ℕ) (a : F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin h,packedRow (sampleMomentEntry E order15Scale j 0 1 (anchorCoefficientsAt n a) i)=
      get rows i.val)
    (paid : (rowMatrix 1009 h rows).det=v) :
    (anchorMomentNorm n k j).eval₂ order15Reduce a=v := by
  rw [anchorMomentNorm_at]
  exact rawMomentNorm_eval_of_packed E ks order15Scale j 0 1 _ rows v entry paid

def sampleGramEntry {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ)
    (u : F) (b : Fin (n+1)→F) (i t : Fin h ⊕ Fin h) : F :=
  match i,t with
  | .inl i,.inl t => sampleMomentEntry E M j w u b i t
  | .inl i,.inr t => sampleMomentEntry E M (j+1) w u b i t
  | .inr i,.inl t => sampleMomentEntry E M (j+1) w u b i t
  | .inr i,.inr t => sampleMomentEntry E M (j+2) w u b i t

abbrev blockIndex (h : ℕ) : Fin (h+h) ≃ Fin h ⊕ Fin h := finSumFinEquiv.symm

theorem rawGramNorm_eval_of_packed {n k h : ℕ} (E : OrderedAxes n k h) (ks : k<1009)
    (M j w : ℕ) (u : F) (b : Fin (n+1)→F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin (h+h),packedRow
      (sampleGramEntry E M j w u b (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    rawGramNorm k M j w u b=v := by
  classical
  unfold rawGramNorm
  apply of_rows_equiv _ ((blockIndex h).trans (Equiv.sumCongr E.index E.index)) rows v _ paid
  intro i t
  rw [←entry i,digit_packedRow]
  change rawGramMatrix _ _ _ _ _
    (Equiv.sumCongr E.index E.index (blockIndex h i)) (Equiv.sumCongr E.index E.index (blockIndex h t))=
    sampleGramEntry E M j w u b (blockIndex h i) (blockIndex h t)
  generalize blockIndex h i=v₁
  generalize blockIndex h t=v₂
  cases v₁ <;> cases v₂
  all_goals exact (numericMomentEntry_exact E M _ w u b _ (sampleSite_injective ks) _ _).symm

theorem nodeGramNorm_eval_from_rows {n k h : ℕ} (E : OrderedAxes n k h) (ks : k<1009)
    (j w : ℕ) (u : F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin (h+h),packedRow (sampleGramEntry E order15Scale j w u
      (nodeCoefficientsAt n u) (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    (nodeGramNorm n k j w).eval₂ order15Reduce u=v := by
  rw [nodeGramNorm_at]
  exact rawGramNorm_eval_of_packed E ks order15Scale j w u _ rows v entry paid

theorem anchorGramNorm_eval_from_rows {n k h : ℕ} (E : OrderedAxes (n+1) k h) (ks : k<1009)
    (a : F) (rows : Array ℕ) (v : F)
    (entry : ∀ i : Fin (h+h),packedRow (sampleGramEntry E order15Scale 1 0 1
      (anchorCoefficientsAt n a) (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    (anchorGramNorm n k).eval₂ order15Reduce a=v := by
  rw [anchorGramNorm_at]
  exact rawGramNorm_eval_of_packed E ks order15Scale 1 0 1 _ rows v entry paid

end RKCert.FixedPolynomial
