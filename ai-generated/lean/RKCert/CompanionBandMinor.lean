module

public import RKCert.CompanionOrderedBand

@[expose] public section

/-! # A single Laplace column suffices for any ordered companion minor -/
namespace RKCert.Compound
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

def fullBandPairs {n k h : ℕ} (E : OrderedAxes n k h) (i t : Fin h) : List (ℕ×ℕ) :=
  List.ofFn fun a : Fin k => ((E.axis i a).val,(E.axis t a).val)

def reducedBandPairs {n k h : ℕ} (E : OrderedAxes n (k+1) h) (i t : Fin h)
    (s : Fin (k+1)) : List (ℕ×ℕ) :=
  List.ofFn fun a : Fin k => ((E.axis i (s.succAbove a)).val,(E.axis t a.castSucc).val)

theorem ordered_minor_expansion {n k h : ℕ} (E : OrderedAxes n (k+1) h)
    (b : Fin (n+1)→R) (i t : Fin h) :
    rawMinor b (E.index i) (E.index t)=
      if (E.axis t (Fin.last k)).val+1<n then (bandPolynomial (fullBandPairs E i t):R[X])
      else ∑ s : Fin (k+1),(-1:R[X])^(s.val+k)*
        ((if E.axis i s=E.axis t (Fin.last k) then C (b (Fin.last n))*X else 0)+
          C (b (E.axis i s).castSucc))*bandPolynomial (reducedBandPairs E i t s) := by
  let M := (rawResolvent b).submatrix (E.axis i) (E.axis t)
  have exactM : rawMinor b (E.index i) (E.index t)=M.det := by
    unfold rawMinor
    congr 1
    apply Matrix.ext
    intro j l
    simp only [M,Matrix.submatrix_apply,OrderedAxes.unindex]
  rw [exactM]
  by_cases last : (E.axis t (Fin.last k)).val+1<n
  · rw [ite_eq_left last]
    apply band_submatrix_det (E.axis i) (E.axis t) (E.strict i) (E.strict t) b
    intro j
    have e := (E.strict t).monotone (Fin.le_last j)
    change (E.axis t j).val≤(E.axis t (Fin.last k)).val at e
    omega
  · rw [ite_eq_right last,Matrix.det_succ_column M (Fin.last k)]
    apply Finset.sum_congr rfl
    intro s _
    have hd : (M.submatrix s.succAbove (Fin.last k).succAbove).det=
        bandPolynomial (reducedBandPairs E i t s) := by
      simp only [M,Matrix.submatrix_submatrix,Fin.succAbove_last]
      apply band_submatrix_det ((E.axis i) ∘ s.succAbove) ((E.axis t) ∘ Fin.castSucc)
        ((E.strict i).comp (Fin.strictMono_succAbove s))
        ((E.strict t).comp Fin.strictMono_castSucc) b
      intro j
      have e := E.strict t (Fin.castSucc_lt_last j)
      have l := (E.axis t (Fin.last k)).isLt
      change (E.axis t j.castSucc).val < (E.axis t (Fin.last k)).val at e
      change (E.axis t j.castSucc).val+1<n
      omega
    rw [hd]
    simp only [M,Matrix.submatrix_apply,Fin.val_last,rawResolvent,ite_eq_right last]

end RKCert.Compound
