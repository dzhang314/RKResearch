module

public import RKCert.Dirk15SampleMatrix

@[expose] public section

/-! # Check repeated scalar inputs once, then prune zero small-minor terms -/
namespace RKCert.Compound
open scoped Classical
variable {R : Type*} [CommRing R] [DecidableEq R]

def tinyDetPruned : (k : ℕ) → Matrix (Fin k) (Fin k) R → R
  | 0, _ => 1
  | k+1, A => (List.ofFn fun j : Fin (k+1) =>
      if A 0 j=0 then 0 else (-1:R)^j.val*A 0 j*tinyDetPruned k (A.submatrix Fin.succ j.succAbove)).sum

theorem tinyDetPruned_eq_tinyDet (k : ℕ) (A : Matrix (Fin k) (Fin k) R) :
    tinyDetPruned k A=tinyDet k A := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tinyDetPruned,tinyDet,List.sum_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]
    split_ifs with e <;> simp [e]

end RKCert.Compound

namespace RKCert.FixedPolynomial
open RKCert.LU RKCert.Compound Polynomial
local notation "F" => ZMod 1009

def residueArray (A : Array Nat) {n : Nat} (i : Fin n) : F := get A i.val

def readyMomentEntry {n k h : Nat} (E : OrderedAxes n k h) (B W : Array Nat) (i t : Fin h) : F :=
  (List.ofFn fun a : Fin (k+1) =>
    tinyDetPruned k (Matrix.of fun c d =>
      rawEntryValue (residueArray B : Fin (n+1)→F) (a.val:F) (E.axis i c) (E.axis t d))*
      residueArray W a).sum

theorem readyMomentEntry_exact {n k h : Nat} (E : OrderedAxes n k h) (M j w : Nat)
    (u : F) (b : Fin (n+1)→F) (B W : Array Nat)
    (hB : ∀ i,residueArray B i=b i)
    (hW : ∀ i : Fin (k+1),residueArray W i=numericWeight M j w u (fun s => (s.val:F)) i)
    (i t : Fin h) : readyMomentEntry E B W i t=sampleMomentEntry E M j w u b i t := by
  have hb : (residueArray B : Fin (n+1)→F)=b := funext hB
  unfold readyMomentEntry sampleMomentEntry numericMomentEntry
  simp only [tinyDetPruned_eq_tinyDet,hb,hW]

theorem nodeMomentNorm_eval_ready {n k h : Nat} (E : OrderedAxes n k h) (ks : k<1009)
    (j w : Nat) (u : F) (rows B W : Array Nat) (v : F)
    (hB : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (hW : ∀ i : Fin (k+1),residueArray W i=numericWeight order15Scale j w u (fun s=>(s.val:F)) i)
    (check : ∀ i : Fin h,packedRow (readyMomentEntry E B W i)=get rows i.val)
    (paid : (rowMatrix 1009 h rows).det=v) :
    (nodeMomentNorm n k j w).eval₂ order15Reduce u=v := by
  apply nodeMomentNorm_eval_from_rows E ks j w u rows v _ paid
  intro i
  have e := funext (readyMomentEntry_exact E order15Scale j w u _ B W hB hW i)
  rw [←e]
  exact check i

theorem anchorMomentNorm_eval_ready {n k h : Nat} (E : OrderedAxes (n+1) k h) (ks : k<1009)
    (j : Nat) (a : F) (rows B W : Array Nat) (v : F)
    (hB : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (hW : ∀ i : Fin (k+1),residueArray W i=numericWeight order15Scale j 0 1 (fun s=>(s.val:F)) i)
    (check : ∀ i : Fin h,packedRow (readyMomentEntry E B W i)=get rows i.val)
    (paid : (rowMatrix 1009 h rows).det=v) :
    (anchorMomentNorm n k j).eval₂ order15Reduce a=v := by
  apply anchorMomentNorm_eval_from_rows E ks j a rows v _ paid
  intro i
  have e := funext (readyMomentEntry_exact E order15Scale j 0 1 _ B W hB hW i)
  rw [←e]
  exact check i

def readyGramEntry {n k h : Nat} (E : OrderedAxes n k h) (B W₀ W₁ W₂ : Array Nat)
    (i t : Fin h ⊕ Fin h) : F :=
  match i,t with
  | .inl i,.inl t => readyMomentEntry E B W₀ i t
  | .inl i,.inr t => readyMomentEntry E B W₁ i t
  | .inr i,.inl t => readyMomentEntry E B W₁ i t
  | .inr i,.inr t => readyMomentEntry E B W₂ i t

theorem rawGramNorm_eval_ready {n k h : Nat} (E : OrderedAxes n k h) (ks : k<1009)
    (M j w : Nat) (u : F) (b : Fin (n+1)→F) (rows B W₀ W₁ W₂ : Array Nat) (v : F)
    (hB : ∀ i,residueArray B i=b i)
    (hW0 : ∀ i : Fin (k+1),residueArray W₀ i=numericWeight M j w u (fun s=>(s.val:F)) i)
    (hW1 : ∀ i : Fin (k+1),residueArray W₁ i=numericWeight M (j+1) w u (fun s=>(s.val:F)) i)
    (hW2 : ∀ i : Fin (k+1),residueArray W₂ i=numericWeight M (j+2) w u (fun s=>(s.val:F)) i)
    (check : ∀ i : Fin (h+h),packedRow
      (readyGramEntry E B W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    rawGramNorm k M j w u b=v := by
  apply rawGramNorm_eval_of_packed E ks M j w u b rows v _ paid
  intro i
  have eq (s t : Fin h ⊕ Fin h) :
      readyGramEntry E B W₀ W₁ W₂ s t=sampleGramEntry E M j w u b s t := by
    cases s <;> cases t
    · exact readyMomentEntry_exact E M j w u b B W₀ hB hW0 _ _
    · exact readyMomentEntry_exact E M (j+1) w u b B W₁ hB hW1 _ _
    · exact readyMomentEntry_exact E M (j+1) w u b B W₁ hB hW1 _ _
    · exact readyMomentEntry_exact E M (j+2) w u b B W₂ hB hW2 _ _
  have e : readyGramEntry E B W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h=
      sampleGramEntry E M j w u b (blockIndex h i) ∘ blockIndex h :=
    funext (fun t => eq (blockIndex h i) (blockIndex h t))
  rw [←e]
  exact check i

theorem nodeGramNorm_eval_ready {n k h : Nat} (E : OrderedAxes n k h) (ks : k<1009)
    (j w : Nat) (u : F) (rows B W₀ W₁ W₂ : Array Nat) (v : F)
    (hB : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (hW0 : ∀ i : Fin (k+1),residueArray W₀ i=numericWeight order15Scale j w u (fun s=>(s.val:F)) i)
    (hW1 : ∀ i : Fin (k+1),residueArray W₁ i=numericWeight order15Scale (j+1) w u (fun s=>(s.val:F)) i)
    (hW2 : ∀ i : Fin (k+1),residueArray W₂ i=numericWeight order15Scale (j+2) w u (fun s=>(s.val:F)) i)
    (check : ∀ i : Fin (h+h),packedRow
      (readyGramEntry E B W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    (nodeGramNorm n k j w).eval₂ order15Reduce u=v := by
  rw [nodeGramNorm_at]
  exact rawGramNorm_eval_ready E ks order15Scale j w u _ rows B W₀ W₁ W₂ v hB hW0 hW1 hW2 check paid

theorem anchorGramNorm_eval_ready {n k h : Nat} (E : OrderedAxes (n+1) k h) (ks : k<1009)
    (a : F) (rows B W₀ W₁ W₂ : Array Nat) (v : F)
    (hB : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (hW0 : ∀ i : Fin (k+1),residueArray W₀ i=numericWeight order15Scale 1 0 1 (fun s=>(s.val:F)) i)
    (hW1 : ∀ i : Fin (k+1),residueArray W₁ i=numericWeight order15Scale 2 0 1 (fun s=>(s.val:F)) i)
    (hW2 : ∀ i : Fin (k+1),residueArray W₂ i=numericWeight order15Scale 3 0 1 (fun s=>(s.val:F)) i)
    (check : ∀ i : Fin (h+h),packedRow
      (readyGramEntry E B W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (paid : (rowMatrix 1009 (h+h) rows).det=v) :
    (anchorGramNorm n k).eval₂ order15Reduce a=v := by
  rw [anchorGramNorm_at]
  exact rawGramNorm_eval_ready E ks order15Scale 1 0 1 _ rows B W₀ W₁ W₂ v hB hW0 hW1 hW2 check paid

end RKCert.FixedPolynomial
