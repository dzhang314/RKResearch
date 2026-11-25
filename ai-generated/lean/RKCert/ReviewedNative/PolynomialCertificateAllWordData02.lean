module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData02
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row018L
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row018R
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row019
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row020
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row021
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row022
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row023
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row024
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData02Row025

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

theorem forces018 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row018 := by
  apply allWordCage_join (slot := 3) (cut := 10896)
  · rw [← sub018L_eq]
    exact @forces018L K _ _ _
  · rw [← sub018R_eq]
    exact @forces018R K _ _ _

theorem fullWordRows02 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordRows K allMarkGroups rows02 :=
  allWordRows_cons forces018 (allWordRows_cons forces019 (allWordRows_cons forces020 (allWordRows_cons forces021 (allWordRows_cons forces022 (allWordRows_cons forces023 (allWordRows_cons forces024 (allWordRows_cons forces025 (allWordRows_nil))))))))

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
