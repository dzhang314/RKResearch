module

public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCages
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData01
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData03
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData04
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData05
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData06
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData07
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData08
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData09
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData10
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData11
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData12
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData13
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData14
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData15

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem allOrdinaryWords : AllWordRows K allMarkGroups ordinaryRows :=
  (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append (allWordRows_append fullWordRows00 fullWordRows01) fullWordRows02) fullWordRows03) fullWordRows04) fullWordRows05) fullWordRows06) fullWordRows07) fullWordRows08) fullWordRows09) fullWordRows10) fullWordRows11) fullWordRows12) fullWordRows13) fullWordRows14) fullWordRows15)

/-- No chronological sign-window hypothesis and no permutation input. -/
theorem no_six_ports_all_orders {s t : K} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {β : Fin 8 → K} (order : StrictMono β) (unit : ∀ i, β i ∈ Set.Icc 0 1)
    (roots : ∀ i, (centeredPolynomial s t).IsRoot (2 * β i - 1))
    {u a h z : Fin 8} (d : ([u, a, h, z] : List (Fin 8)).Nodup)
    (paid : ∀ p ∈ (wordOfMarks u a h z).six, p.value β = 0) : False := by
  obtain ⟨r, hr, _, hb⟩ := exists_ordinary_cage hs ht order unit roots
  obtain ⟨p, hp, hn⟩ := allOrdinaryWords r hr hb (all_mark_word_spec u a h z d).2
  exact hn (paid p hp)

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
