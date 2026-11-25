module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCages
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData00
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData01
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData02
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData03
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData04
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData05
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData06
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData07
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData08
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData09
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData10
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData11
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData12
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData13
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData14
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortData15

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 24000
set_option maxHeartbeats 16000000

def allPortPlans : List (CageRow × List SignedPort) :=
  plans00 ++ plans01 ++ plans02 ++ plans03 ++ plans04 ++ plans05 ++ plans06 ++ plans07 ++ plans08 ++ plans09 ++ plans10 ++ plans11 ++ plans12 ++ plans13 ++ plans14 ++ plans15

theorem allPortPlans_rows : allPortPlans.map Prod.fst = ordinaryRows := by
  simp only [allPortPlans, ordinaryRows, List.map_append, plans00_rows, plans01_rows, plans02_rows, plans03_rows, plans04_rows, plans05_rows, plans06_rows, plans07_rows, plans08_rows, plans09_rows, plans10_rows, plans11_rows, plans12_rows, plans13_rows, plans14_rows, plans15_rows]

theorem allPortPlans_ok : allPortPlans.all (fun p => planOK retainedWords p.1 p.2) = true := by
  simp only [allPortPlans, List.all_append, plans00_ok, plans01_ok, plans02_ok, plans03_ok, plans04_ok, plans05_ok, plans06_ok, plans07_ok, plans08_ok, plans09_ok, plans10_ok, plans11_ok, plans12_ok, plans13_ok, plans14_ok, plans15_ok, Bool.true_and]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordinary_word_has_port {r : CageRow} (hr : r ∈ ordinaryRows) {w : PortWord}
    (hw : w ∈ retainedWords) {β : Fin 8 → K} (hb : InCages r β) :
    ∃ p ∈ w.six, p.value β ≠ 0 := by
  rw [← allPortPlans_rows] at hr
  obtain ⟨⟨r', plan⟩, hm, he⟩ := List.mem_map.mp hr
  change r' = r at he
  subst r'
  exact plan_forces_nonzero (List.all_eq_true.mp allPortPlans_ok _ hm) hw hb

/-- The closed-square geometry, all 123 cages, all 141 permitted words and
the six true normalized formal integrals are assembled in one implication.
The upstream physical packet must still establish the chart and ordering hypotheses. -/
theorem no_six_paid_ports_on_chart {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {σ : List (Fin 8)} (perm : σ.Perm (List.finRange 8)) (good : (decodeWord σ).permitted = true)
    (paid : ∀ p ∈ (decodeWord σ).six, p.value β = 0) : False := by
  obtain ⟨r, hr, _, hb⟩ := exists_ordinary_cage hs ht order unit roots
  obtain ⟨p, hp, hz⟩ := ordinary_word_has_port hr (retained_of_permitted perm good) hb
  exact hz (paid p hp)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
