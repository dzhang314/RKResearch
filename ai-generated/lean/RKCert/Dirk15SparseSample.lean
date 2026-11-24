module

public import RKCert.CompanionBandMoments
public import RKCert.Dirk15ParameterSample
public import RKCert.Dirk15ReflectResidue

@[expose] public section

/-! # Exact packed sample evaluation from sparse signed companion minors -/
namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound RKCert.LU
local notation "F" => ZMod 1009

def sparseGramEntry {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (M j w : ℕ) (u : F) (b : Fin (n+1)→F) (i t : Fin h ⊕ Fin h) : F :=
  match i,t with
  | .inl i,.inl t => sparseMomentEntry E M j w u b i t
  | .inl i,.inr t => sparseMomentEntry E M (j+1) w u b i t
  | .inr i,.inl t => sparseMomentEntry E M (j+1) w u b i t
  | .inr i,.inr t => sparseMomentEntry E M (j+2) w u b i t

private theorem rawMomentNorm_sparse {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (M j w : ℕ) (w1 : w≤1) (u : F) (b : Fin (n+1)→F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=b i)
    (entry : ∀ i : Fin h,packedRow (sparseMomentEntry E M j w u (residueArray B) i)=get rows i.val)
    (checked : (rowMatrix 1009 h rows).det=v) :
    rawMomentNorm (k+1) M j w u b=v := by
  classical
  unfold rawMomentNorm
  apply of_rows_equiv _ E.index rows v _ checked
  intro i t
  rw [←entry i,digit_packedRow]
  have ee : (residueArray B : Fin (n+1)→F)=b := funext hB
  rw [ee]
  exact (sparseMomentEntry_exact E M j w w1 u b i t).symm

private theorem rawGramNorm_sparse {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (M j w : ℕ) (w1 : w≤1) (u : F) (b : Fin (n+1)→F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=b i)
    (entry : ∀ i : Fin (h+h),packedRow
      (sparseGramEntry E M j w u (residueArray B) (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (checked : (rowMatrix 1009 (h+h) rows).det=v) :
    rawGramNorm (k+1) M j w u b=v := by
  classical
  unfold rawGramNorm
  apply of_rows_equiv _ ((blockIndex h).trans (Equiv.sumCongr E.index E.index)) rows v _ checked
  intro i t
  rw [←entry i,digit_packedRow]
  have ee : (residueArray B : Fin (n+1)→F)=b := funext hB
  rw [ee]
  change rawGramMatrix M j w u b
    (Equiv.sumCongr E.index E.index (blockIndex h i)) (Equiv.sumCongr E.index E.index (blockIndex h t))=
    sparseGramEntry E M j w u b (blockIndex h i) (blockIndex h t)
  generalize blockIndex h i=s
  generalize blockIndex h t=t'
  cases s <;> cases t' <;> exact (sparseMomentEntry_exact E M _ w w1 u b _ _).symm

theorem nodeMomentNorm_eval_sparse {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (j w : ℕ) (w1 : w≤1) (u : F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (entry : ∀ i : Fin h,packedRow (sparseMomentEntry E order15Scale j w u (residueArray B) i)=
      get rows i.val)
    (checked : (rowMatrix 1009 h rows).det=v) :
    (nodeMomentNorm n (k+1) j w).eval₂ order15Reduce u=v := by
  rw [nodeMomentNorm_at]
  exact rawMomentNorm_sparse E order15Scale j w w1 u _ rows B v hB entry checked

theorem anchorMomentNorm_eval_sparse {n k h : ℕ} (E : OrderedAxes (n+1) (k+1) h)
    (j : ℕ) (a : F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (entry : ∀ i : Fin h,packedRow (sparseMomentEntry E order15Scale j 0 1 (residueArray B) i)=
      get rows i.val)
    (checked : (rowMatrix 1009 h rows).det=v) :
    (anchorMomentNorm n (k+1) j).eval₂ order15Reduce a=v := by
  rw [anchorMomentNorm_at]
  exact rawMomentNorm_sparse E order15Scale j 0 (by decide) 1 _ rows B v hB entry checked

theorem nodeGramNorm_eval_sparse {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (j w : ℕ) (w1 : w≤1) (u : F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (entry : ∀ i : Fin (h+h),packedRow (sparseGramEntry E order15Scale j w u (residueArray B)
      (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (checked : (rowMatrix 1009 (h+h) rows).det=v) :
    (nodeGramNorm n (k+1) j w).eval₂ order15Reduce u=v := by
  rw [nodeGramNorm_at]
  exact rawGramNorm_sparse E order15Scale j w w1 u _ rows B v hB entry checked

theorem anchorGramNorm_eval_sparse {n k h : ℕ} (E : OrderedAxes (n+1) (k+1) h)
    (a : F) (rows B : Array ℕ) (v : F)
    (hB : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (entry : ∀ i : Fin (h+h),packedRow (sparseGramEntry E order15Scale 1 0 1 (residueArray B)
      (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (checked : (rowMatrix 1009 (h+h) rows).det=v) :
    (anchorGramNorm n (k+1)).eval₂ order15Reduce a=v := by
  rw [anchorGramNorm_at]
  exact rawGramNorm_sparse E order15Scale 1 0 (by decide) 1 _ rows B v hB entry checked


/-- Check the concrete natural packed rows as one closed Boolean, instead
of storing a large proof term with all Fin cases. The checked Boolean 
still compares every single original row. -/
def packedRowsCheck {h : ℕ} (f : Fin h→ℕ) (rows : Array ℕ) : Bool :=
  (List.finRange h).all (fun i => f i == get rows i.val)

theorem packedRowsCheck_sound {h : ℕ} {f : Fin h→ℕ} {rows : Array ℕ}
    (checked : packedRowsCheck f rows=true) : ∀ i,f i=get rows i.val := by
  intro i
  exact beq_iff_eq.mp (List.all_eq_true.mp checked i (by simp))

end RKCert.FixedPolynomial
