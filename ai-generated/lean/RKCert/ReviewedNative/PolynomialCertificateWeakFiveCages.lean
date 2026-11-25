module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData01
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData02
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData03
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData04
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData05
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData06
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData07
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData08
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData09
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData10
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData11
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData12
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData13
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData14
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData15
import Mathlib.Tactic.Linarith

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 18000
set_option maxHeartbeats 8000000

def ordinaryRows : List CageRow :=
  rows00 ++ rows01 ++ rows02 ++ rows03 ++ rows04 ++ rows05 ++ rows06 ++ rows07 ++ rows08 ++ rows09 ++ rows10 ++ rows11 ++ rows12 ++ rows13 ++ rows14 ++ rows15

theorem ordinaryRows_ok : ordinaryRows.all CageRow.ok = true := by
  simp only [ordinaryRows, List.all_append, rows00_ok, rows01_ok, rows02_ok, rows03_ok, rows04_ok, rows05_ok, rows06_ok, rows07_ok, rows08_ok, rows09_ok, rows10_ok, rows11_ok, rows12_ok, rows13_ok, rows14_ok, rows15_ok, Bool.true_and]

/-- The published geometry row is either one of the 123 ordinary rows or
one of the four already certified exclusions. No replacement geometry is assumed. -/
theorem row_classes : cellRows.all (fun c => decide (c ∈ ordinaryRows.map CageRow.rect ∨
    c = cut12.rect ∨ c = cut16.rect ∨ c = cut42.rect ∨ c = cut44.rect)) = true := by
  decide +kernel

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- All 123 finite row decisions transfer to the actual ordered sites. -/
theorem all_ordinary_cages (r : CageRow) (hr : r ∈ ordinaryRows) {s t : K}
    (cell : InDyadicRect r.rect s t) {β : Fin 8 → K} (order : StrictMono β)
    (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1)) (i : Fin 8) :
    β i ∈ Set.Icc (((r.endpoint i.val).1 : K) / 32768)
      (((r.endpoint i.val).2 : K) / 32768) :=
  CageRow.unit_sites (List.all_eq_true.mp ordinaryRows_ok r hr) cell order unit roots i

/-- Every genuine site tuple on the closed chart has one certified
simultaneous eight-site cage. The rectangles and sites need not be separated. -/
theorem exists_ordinary_cage {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1)) :
    ∃ r ∈ ordinaryRows, InDyadicRect r.rect s t ∧ ∀ i : Fin 8,
      β i ∈ Set.Icc (((r.endpoint i.val).1 : K) / 32768)
        (((r.endpoint i.val).2 : K) / 32768) := by
  obtain ⟨c, hc, hcell⟩ := covers hs ht
  have hclass := of_decide_eq_true (List.all_eq_true.mp row_classes c hc)
  rcases hclass with hnormal | hcut
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hnormal
    exact ⟨r, hr, hcell, all_ordinary_cages r hr hcell order unit roots⟩
  · have inside : InDyadicRect cut12.rect s t ∨ InDyadicRect cut16.rect s t ∨
        InDyadicRect cut42.rect s t ∨ InDyadicRect cut44.rect s t := by
      rcases hcut with h | h | h | h
      · exact Or.inl (h ▸ hcell)
      · exact Or.inr (Or.inl (h ▸ hcell))
      · exact Or.inr (Or.inr (Or.inl (h ▸ hcell)))
      · exact Or.inr (Or.inr (Or.inr (h ▸ hcell)))
    have inj : Function.Injective (fun j : Fin 8 => 2 * β j - 1) := by
      intro i j hij
      apply order.injective
      change 2 * β i - 1 = 2 * β j - 1 at hij
      linarith only [hij]
    exact False.elim (no_eight_sites_in_four_cut_cells inside inj roots)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
