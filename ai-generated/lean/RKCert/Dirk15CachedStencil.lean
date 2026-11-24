module
public import RKCert.CompanionReplayStencil
public import RKCert.Dirk15SparseSample

@[expose] public section

namespace RKCert.FixedPolynomial
open Polynomial RKCert.Compound RKCert.LU
local notation "F" => ZMod 1009

structure NumericallyCheckedStencil {n k h : ℕ}
    (E : OrderedAxes n (k+1) h) where
  data : Array ℕ
  checked : ∀ i t, stencilAt (k+1) data i t=exactStencil E i t

def CachedWeightOK (M j w : ℕ) (u : F) (W : Array ℕ) : Prop :=
  ∀ d : Fin W.size, (W[d]:F)=monomialMomentWeight M j w u d.val

def stenciledEntry {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (M j w : ℕ) (u : F)
    (b : Fin (n+1)→F) (W : Array ℕ) (i t : Fin h) : F :=
  evalReplayStencil b (cachedWeight M j w u W) (stencilAt (k+1) S.data i t)

theorem stenciledEntry_eq {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (M j w : ℕ) (u : F)
    (b : Fin (n+1)→F) (W : Array ℕ) (pay : CachedWeightOK M j w u W) (i t : Fin h) :
    stenciledEntry S M j w u b W i t=sparseMomentEntry E M j w u b i t := by
  unfold stenciledEntry
  rw [S.checked i t,cachedWeight_sound pay]
  exact eval_exactStencil E M j w u b i t

def stenciledGram {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (M j w : ℕ) (u : F)
    (b : Fin (n+1)→F) (W₀ W₁ W₂ : Array ℕ) (i t : Fin h ⊕ Fin h) : F :=
  match i,t with
  | .inl i,.inl t => stenciledEntry S M j w u b W₀ i t
  | .inl i,.inr t => stenciledEntry S M (j+1) w u b W₁ i t
  | .inr i,.inl t => stenciledEntry S M (j+1) w u b W₁ i t
  | .inr i,.inr t => stenciledEntry S M (j+2) w u b W₂ i t

theorem stenciledGram_eq {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (M j w : ℕ) (u : F)
    (b : Fin (n+1)→F) (W₀ W₁ W₂ : Array ℕ)
    (p₀ : CachedWeightOK M j w u W₀) (p₁ : CachedWeightOK M (j+1) w u W₁)
    (p₂ : CachedWeightOK M (j+2) w u W₂) (i t : Fin h ⊕ Fin h) :
    stenciledGram S M j w u b W₀ W₁ W₂ i t=sparseGramEntry E M j w u b i t := by
  cases i <;> cases t
  · exact stenciledEntry_eq S M _ w u b _ p₀ _ _
  · exact stenciledEntry_eq S M _ w u b _ p₁ _ _
  · exact stenciledEntry_eq S M _ w u b _ p₁ _ _
  · exact stenciledEntry_eq S M _ w u b _ p₂ _ _

theorem nodeMomentNorm_eval_stencil {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (j w : ℕ) (w1 : w≤1)
    (u : F) (rows B W : Array ℕ) (v : F)
    (coeff : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (pay : CachedWeightOK order15Scale j w u W)
    (entry : ∀ i : Fin h,packedRow (stenciledEntry S order15Scale j w u (residueArray B) W i)=get rows i.val)
    (checked : (rowMatrix 1009 h rows).det=v) :
    (nodeMomentNorm n (k+1) j w).eval₂ order15Reduce u=v := by
  refine nodeMomentNorm_eval_sparse E j w w1 u rows B v coeff ?_ checked
  intro i
  exact (congrArg packedRow (funext fun t =>
    (stenciledEntry_eq S _ _ _ _ _ _ pay i t).symm)).trans (entry i)

theorem anchorMomentNorm_eval_stencil {n k h : ℕ} {E : OrderedAxes (n+1) (k+1) h}
    (S : NumericallyCheckedStencil E) (j : ℕ)
    (a : F) (rows B W : Array ℕ) (v : F)
    (coeff : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (pay : CachedWeightOK order15Scale j 0 1 W)
    (entry : ∀ i : Fin h,packedRow (stenciledEntry S order15Scale j 0 1 (residueArray B) W i)=get rows i.val)
    (checked : (rowMatrix 1009 h rows).det=v) :
    (anchorMomentNorm n (k+1) j).eval₂ order15Reduce a=v := by
  refine anchorMomentNorm_eval_sparse E j a rows B v coeff ?_ checked
  intro i
  exact (congrArg packedRow (funext fun t =>
    (stenciledEntry_eq S _ _ _ _ _ _ pay i t).symm)).trans (entry i)

theorem nodeGramNorm_eval_stencil {n k h : ℕ} {E : OrderedAxes n (k+1) h}
    (S : NumericallyCheckedStencil E) (j w : ℕ) (w1 : w≤1)
    (u : F) (rows B W₀ W₁ W₂ : Array ℕ) (v : F)
    (coeff : ∀ i,residueArray B i=nodeCoefficientsAt n u i)
    (p₀ : CachedWeightOK order15Scale j w u W₀) (p₁ : CachedWeightOK order15Scale (j+1) w u W₁)
    (p₂ : CachedWeightOK order15Scale (j+2) w u W₂)
    (entry : ∀ i : Fin (h+h),packedRow (stenciledGram S order15Scale j w u (residueArray B)
      W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (checked : (rowMatrix 1009 (h+h) rows).det=v) :
    (nodeGramNorm n (k+1) j w).eval₂ order15Reduce u=v := by
  refine nodeGramNorm_eval_sparse E j w w1 u rows B v coeff ?_ checked
  intro i
  exact (congrArg packedRow (funext fun t =>
    (stenciledGram_eq S _ _ _ _ _ _ _ _ p₀ p₁ p₂ (blockIndex h i) (blockIndex h t)).symm)).trans (entry i)

theorem anchorGramNorm_eval_stencil {n k h : ℕ} {E : OrderedAxes (n+1) (k+1) h}
    (S : NumericallyCheckedStencil E)
    (a : F) (rows B W₀ W₁ W₂ : Array ℕ) (v : F)
    (coeff : ∀ i,residueArray B i=anchorCoefficientsAt n a i)
    (p₀ : CachedWeightOK order15Scale 1 0 1 W₀) (p₁ : CachedWeightOK order15Scale 2 0 1 W₁)
    (p₂ : CachedWeightOK order15Scale 3 0 1 W₂)
    (entry : ∀ i : Fin (h+h),packedRow (stenciledGram S order15Scale 1 0 1 (residueArray B)
      W₀ W₁ W₂ (blockIndex h i) ∘ blockIndex h)=get rows i.val)
    (checked : (rowMatrix 1009 (h+h) rows).det=v) :
    (anchorGramNorm n (k+1)).eval₂ order15Reduce a=v := by
  refine anchorGramNorm_eval_sparse E a rows B v coeff ?_ checked
  intro i
  exact (congrArg packedRow (funext fun t =>
    (stenciledGram_eq S _ _ _ _ _ _ _ _ p₀ p₁ p₂ (blockIndex h i) (blockIndex h t)).symm)).trans (entry i)

end RKCert.FixedPolynomial
