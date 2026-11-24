module

public import RKCert.CompanionRawNorm

@[expose] public section

/-! # Finite concrete ordered-subset axes and small minors

Inputs that enumerate all increasing tuples are proved to reindex the
true exterior basis. Large determinants remain Mathlib determinants;
only the small companion minors are recursively evaluated. -/
namespace RKCert.Compound
open Polynomial Set Set.powersetCard
open scoped Classical

structure OrderedAxes (n k h : ℕ) where
  axis : Fin h → Fin k → Fin n
  strict : ∀ i, StrictMono (axis i)
  injective : Function.Injective axis
  card : h=n.choose k

namespace OrderedAxes
variable {n k h : ℕ} (E : OrderedAxes n k h)

def embed (i : Fin h) : Fin k ↪o Fin n :=
  OrderEmbedding.ofStrictMono (E.axis i) (E.strict i)

noncomputable def index : Fin h ≃ powersetCard (Fin n) k := by
  refine Equiv.ofBijective (fun i => powersetCard.ofFinEmbEquiv (E.embed i)) ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨fun i j z => E.injective (congrArg (fun f : Fin k ↪o Fin n => (f:Fin k→Fin n))
    (powersetCard.ofFinEmbEquiv.injective z)),?_⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fin,←E.card] using
    (powersetCard.card (α:=Fin n) (n:=k)).symm

@[simp] theorem unindex (i : Fin h) (j : Fin k) :
    powersetCard.ofFinEmbEquiv.symm (E.index i) j=E.axis i j := by
  change (powersetCard.ofFinEmbEquiv.symm (powersetCard.ofFinEmbEquiv (E.embed i))) j=_
  rw [Equiv.symm_apply_apply]
  rfl

end OrderedAxes

variable {R : Type*} [CommRing R]

/-- List-summed Laplace recurrence, useful only at the small generic
minor dimension, not on the full compound or the Gram block. -/
def tinyDet : (k : ℕ) → Matrix (Fin k) (Fin k) R → R
  | 0, _ => 1
  | k+1, A => (List.ofFn fun j : Fin (k+1) =>
      (-1:R)^j.val*A 0 j*tinyDet k (A.submatrix Fin.succ j.succAbove)).sum

theorem tinyDet_eq_det (k : ℕ) (A : Matrix (Fin k) (Fin k) R) :
    tinyDet k A=A.det := by
  induction k with
  | zero => simp [tinyDet,Matrix.det_fin_zero]
  | succ k ih =>
    rw [tinyDet,Matrix.det_succ_row_zero,List.sum_ofFn]
    simp only [ih]

theorem rawMinor_on_axes {n k h : ℕ} (E : OrderedAxes n k h) (b : Fin (n+1)→R)
    (i j : Fin h) :
    rawMinor b (E.index i) (E.index j)=
      tinyDet k (fun a t => rawResolvent b (E.axis i a) (E.axis j t)) := by
  let A : Matrix (Fin k) (Fin k) R[X] :=
    Matrix.of (fun a t => rawResolvent b (E.axis i a) (E.axis j t))
  change rawMinor b (E.index i) (E.index j)=tinyDet k A
  rw [tinyDet_eq_det k A,rawMinor]
  congr 1
  apply Matrix.ext
  intro a t
  simp only [Matrix.submatrix_apply,OrderedAxes.unindex,A,Matrix.of_apply]

theorem rawMomentNorm_on_axes {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ)
    (u : R) (b : Fin (n+1)→R) :
    rawMomentNorm k M j w u b=
      (Matrix.of fun i t : Fin h => scaledMoment M j (k+w) u
        ((1-X)^w*tinyDet k (fun a s => rawResolvent b (E.axis i a) (E.axis t s)))).det := by
  classical
  rw [rawMomentNorm,←Matrix.det_submatrix_equiv_self E.index]
  congr 1
  apply Matrix.ext
  intro i t
  change scaledMoment M j (k+w) u ((1-X)^w*rawMinor b (E.index i) (E.index t))=_
  rw [rawMinor_on_axes,Matrix.of_apply]

theorem rawGramNorm_on_axes {n k h : ℕ} (E : OrderedAxes n k h) (M j w : ℕ)
    (u : R) (b : Fin (n+1)→R) :
    rawGramNorm k M j w u b=
      (Matrix.fromBlocks
        (Matrix.of fun i t : Fin h => scaledMoment M j (k+w) u
          ((1-X)^w*tinyDet k (fun a s => rawResolvent b (E.axis i a) (E.axis t s))))
        (Matrix.of fun i t : Fin h => scaledMoment M (j+1) (k+w) u
          ((1-X)^w*tinyDet k (fun a s => rawResolvent b (E.axis i a) (E.axis t s))))
        (Matrix.of fun i t : Fin h => scaledMoment M (j+1) (k+w) u
          ((1-X)^w*tinyDet k (fun a s => rawResolvent b (E.axis i a) (E.axis t s))))
        (Matrix.of fun i t : Fin h => scaledMoment M (j+2) (k+w) u
          ((1-X)^w*tinyDet k (fun a s => rawResolvent b (E.axis i a) (E.axis t s))))).det := by
  classical
  rw [rawGramNorm,←Matrix.det_submatrix_equiv_self (Equiv.sumCongr E.index E.index)]
  congr 1
  apply Matrix.ext
  intro i t
  cases i <;> cases t
  all_goals simp only [rawGramMatrix,Matrix.submatrix_apply,Equiv.sumCongr_apply,
    Sum.map_inl,Sum.map_inr,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,rawMomentMatrix,Matrix.of_apply,
    rawMinor_on_axes]

end RKCert.Compound
