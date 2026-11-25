module

public import RKCert.ReviewedNative.PolynomialCertificateAllWordSeparatedCheck
public import RKCert.ReviewedNative.PolynomialCertificateWeakFivePortWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData15

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 24000
set_option maxHeartbeats 16000000

def plan124 : List SignedPort :=
  [
   ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 0, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 2, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 7, 1, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩,
   ⟨⟨[1, 4, 5, 7], 6, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 4, 5, 6], 7, 1, false⟩, false⟩,
   ⟨⟨[0, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 4, 7], 0, 2, true⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 4, 6], 1, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 5, 6], 4, 1, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 3, 5, 7], 1, 2, true⟩, false⟩,
   ⟨⟨[1, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 6], 2, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 3, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 5, 7], 2, 2, true⟩, false⟩,
   ⟨⟨[0, 1, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 4, 7], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 6], 4, 2, false⟩, true⟩,
   ⟨⟨[1, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[0, 3, 4, 6], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 3, 4, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 2, 2, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 7, 6], 2, 1, false⟩, true⟩,
   ⟨⟨[1, 3, 5, 7, 6], 4, 1, false⟩, true⟩]

theorem plan124_ok : planOK retainedWords row124 plan124 = true := by
  rw [← SeparatedCheck.planCheck_eq]
  decide +kernel

def plan125 : List SignedPort :=
  [
   ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, false⟩,
   ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 0, 1, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 7, 1, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 2, 2, true⟩, true⟩,
   ⟨⟨[1, 4, 5, 7], 6, 1, false⟩, false⟩,
   ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩,
   ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 4, 5, 6], 7, 1, false⟩, false⟩,
   ⟨⟨[0, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 4, 7], 0, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 5, 6], 4, 1, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 3, 5, 7], 1, 2, true⟩, false⟩,
   ⟨⟨[1, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 6], 2, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 3, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩,
   ⟨⟨[0, 3, 5, 7], 2, 2, true⟩, false⟩,
   ⟨⟨[0, 1, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 7], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 6], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 4, 6], 7, 1, false⟩, false⟩,
   ⟨⟨[1, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[0, 2, 4, 6], 3, 2, false⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 2, 2, true⟩, false⟩,
   ⟨⟨[0, 2, 4, 6], 5, 2, false⟩, false⟩,
   ⟨⟨[1, 3, 5, 7, 6], 2, 1, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 6, 1], 5, 1, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7, 6], 4, 1, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 6, 1], 3, 1, true⟩, true⟩]

theorem plan125_ok : planOK retainedWords row125 plan125 = true := by
  rw [← SeparatedCheck.planCheck_eq]
  decide +kernel

def plan126 : List SignedPort :=
  [
   ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 0, 1, true⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 2, 2, true⟩, true⟩,
   ⟨⟨[0, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 7, 1, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩,
   ⟨⟨[1, 4, 5, 7], 6, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 4, 5, 6], 7, 1, false⟩, false⟩,
   ⟨⟨[0, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 7], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 4, 7], 0, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩,
   ⟨⟨[0, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[1, 3, 5, 6], 7, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 4, 6], 1, 2, true⟩, true⟩,
   ⟨⟨[0, 3, 5, 7], 6, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 0, 1, true⟩, false⟩,
   ⟨⟨[0, 2, 5, 6], 4, 1, false⟩, true⟩,
   ⟨⟨[1, 2, 5, 7], 3, 1, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩,
   ⟨⟨[0, 1, 4, 6], 2, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 6, 7], 5, 2, false⟩, true⟩,
   ⟨⟨[0, 2, 5, 6], 3, 2, false⟩, true⟩,
   ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩,
   ⟨⟨[1, 2, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩,
   ⟨⟨[1, 3, 6, 7], 4, 2, false⟩, true⟩,
   ⟨⟨[0, 1, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩,
   ⟨⟨[0, 3, 5, 7], 4, 1, false⟩, false⟩,
   ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 4, 7], 0, 1, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 6], 4, 2, false⟩, true⟩,
   ⟨⟨[1, 2, 4, 6], 3, 2, true⟩, true⟩,
   ⟨⟨[0, 3, 4, 6], 7, 1, false⟩, false⟩,
   ⟨⟨[1, 3, 5, 7], 4, 2, true⟩, true⟩,
   ⟨⟨[1, 3, 5, 7], 2, 2, true⟩, false⟩,
   ⟨⟨[1, 3, 5, 7, 6], 2, 1, false⟩, true⟩,
   ⟨⟨[1, 3, 5, 7, 6], 4, 1, false⟩, true⟩]

theorem plan126_ok : planOK retainedWords row126 plan126 = true := by
  rw [← SeparatedCheck.planCheck_eq]
  decide +kernel

def plans15 : List (CageRow × List SignedPort) :=
  [(row124, plan124), (row125, plan125), (row126, plan126)]

theorem plans15_rows : plans15.map Prod.fst = rows15 := rfl

theorem plans15_ok : plans15.all (fun p => planOK retainedWords p.1 p.2) = true := by
  simp only [plans15, List.all_cons, List.all_nil, plan124_ok, plan125_ok, plan126_ok, Bool.true_and]

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
