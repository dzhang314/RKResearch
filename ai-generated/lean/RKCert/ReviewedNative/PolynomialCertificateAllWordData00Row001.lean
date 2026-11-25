module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group09Word45to47
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group09Word48
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group09Word49
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group10Word50
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group10Word51
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group10Word52
public import RKCert.ReviewedNative.PolynomialCertificateAllWordData00Row001Group10Word53to54

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan001_00 : GroupPortPlan :=
  [(markWords00, [⟨⟨[0, 1, 2, 3], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 4, 1, true⟩, true⟩]),
   (markWords01, [⟨⟨[0, 1, 2, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 3, 1, true⟩, true⟩]),
   (markWords02, [⟨⟨[0, 1, 2, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 3, 1, true⟩, true⟩]),
   (markWords03, [⟨⟨[0, 1, 2, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 3, 1, true⟩, false⟩]),
   (markWords04, [⟨⟨[0, 1, 2, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 3, 1, true⟩, false⟩])]
theorem groupPlan001_00_ok : groupChecks row001 groupPlan001_00 = true := by decide +kernel

def groupPlan001_01 : GroupPortPlan :=
  [(markWords05, [⟨⟨[0, 1, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 2, 1, true⟩, true⟩]),
   (markWords06, [⟨⟨[0, 1, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 2, 1, true⟩, true⟩]),
   (markWords07, [⟨⟨[0, 1, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩]),
   (markWords08, [⟨⟨[0, 1, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 2, 1, true⟩, false⟩]),
   (markWords09, [⟨⟨[0, 1, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 2, 1, true⟩, true⟩])]
theorem groupPlan001_01_ok : groupChecks row001 groupPlan001_01 = true := by decide +kernel

def groupPlan001_02 : GroupPortPlan :=
  [(markWords10, [⟨⟨[0, 1, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 2, 1, true⟩, false⟩]),
   (markWords11, [⟨⟨[0, 1, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords12, [⟨⟨[0, 1, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords13, [⟨⟨[0, 1, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 5, 7], 2, 2, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 3, 2, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 4, 2, true⟩, true⟩]),
   (markWords14, [⟨⟨[0, 1, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 2, 1, false⟩, true⟩])]
theorem groupPlan001_02_ok : groupChecks row001 groupPlan001_02 = true := by decide +kernel

def groupPlan001_03 : GroupPortPlan :=
  [(markWords15, [⟨⟨[0, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 1, 1, true⟩, true⟩]),
   (markWords16, [⟨⟨[0, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 1, 1, true⟩, true⟩]),
   (markWords17, [⟨⟨[0, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 4, 1, true⟩, false⟩]),
   (markWords18, [⟨⟨[0, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 1, 1, true⟩, false⟩]),
   (markWords19, [⟨⟨[0, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 1, 1, true⟩, true⟩])]
theorem groupPlan001_03_ok : groupChecks row001 groupPlan001_03 = true := by decide +kernel

def groupPlan001_04 : GroupPortPlan :=
  [(markWords20, [⟨⟨[0, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 3, 1, true⟩, false⟩]),
   (markWords21, [⟨⟨[0, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩]),
   (markWords22, [⟨⟨[0, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 2, 5, 6], 1, 1, false⟩, false⟩, ⟨⟨[0, 2, 5, 6], 3, 1, false⟩, false⟩, ⟨⟨[0, 2, 5, 6], 4, 1, false⟩, false⟩]),
   (markWords23, [⟨⟨[0, 2, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 2, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 2, 5, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 2, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords24, [⟨⟨[0, 2, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 2, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 2, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 2, 6, 7], 5, 2, false⟩, true⟩])]
theorem groupPlan001_04_ok : groupChecks row001 groupPlan001_04 = true := by decide +kernel

def groupPlan001_05 : GroupPortPlan :=
  [(markWords25, [⟨⟨[0, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords26, [⟨⟨[0, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 2, 1, true⟩, false⟩]),
   (markWords27, [⟨⟨[0, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords28, [⟨⟨[0, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 1, 2, true⟩, false⟩, ⟨⟨[0, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 1, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 6], 4, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 6], 7, 2, false⟩, true⟩]),
   (markWords29, [⟨⟨[0, 3, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 6, 1, false⟩, false⟩])]
theorem groupPlan001_05_ok : groupChecks row001 groupPlan001_05 = true := by decide +kernel

def groupPlan001_06 : GroupPortPlan :=
  [(markWords30, [⟨⟨[0, 3, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 5, 2, false⟩, true⟩]),
   (markWords31, [⟨⟨[0, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 4, 5, 6], 1, 2, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 4, 5, 6], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 6], 3, 1, false⟩, false⟩]),
   (markWords32, [⟨⟨[0, 4, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords33, [⟨⟨[0, 4, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 1, 2, true⟩, false⟩, ⟨⟨[0, 4, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 4, 6, 7], 2, 1, true⟩, true⟩]),
   (markWords34, [⟨⟨[0, 5, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 1, 1, false⟩, false⟩])]
theorem groupPlan001_06_ok : groupChecks row001 groupPlan001_06 = true := by decide +kernel

def groupPlan001_07 : GroupPortPlan :=
  [(markWords35, [⟨⟨[1, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 0, 1, true⟩, true⟩]),
   (markWords36, [⟨⟨[1, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 0, 1, true⟩, true⟩]),
   (markWords37, [⟨⟨[1, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 3, 6], 7, 2, false⟩, true⟩, ⟨⟨[1, 2, 3, 6, 0], 7, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6, 4], 7, 1, false⟩, true⟩]),
   (markWords38, [⟨⟨[1, 2, 3, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 3, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 3, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 0, 1, true⟩, false⟩]),
   (markWords39, [⟨⟨[1, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 0, 1, true⟩, true⟩])]
theorem groupPlan001_07_ok : groupChecks row001 groupPlan001_07 = true := by decide +kernel

def groupPlan001_08 : GroupPortPlan :=
  [(markWords40, [⟨⟨[1, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords41, [⟨⟨[1, 2, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 0, 1, true⟩, false⟩]),
   (markWords42, [⟨⟨[1, 2, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩]),
   (markWords43, [⟨⟨[1, 2, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 0, 2, true⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 2, 5, 7, 4], 0, 1, false⟩, false⟩, ⟨⟨[1, 2, 5, 7, 3], 0, 1, false⟩, false⟩, ⟨⟨[1, 2, 5, 7, 4], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 7, 3], 0, 1, true⟩, true⟩]),
   (markWords44, [⟨⟨[1, 2, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, true⟩, true⟩])]
theorem groupPlan001_08_ok : groupChecks row001 groupPlan001_08 = true := by decide +kernel

def groupPlan001_09 : GroupPortPlan :=
  [(markWords45, [⟨⟨[1, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 0, 1, true⟩, true⟩]),
   (markWords46, [⟨⟨[1, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 2, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords47, [⟨⟨[1, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7, 0], 5, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 7, 0], 6, 1, true⟩, true⟩]),
   (markWords48, [⟨⟨[1, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 6, 4], 7, 1, false⟩, true⟩]),
   (markWords49, [⟨⟨[1, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 0, 2, true⟩, true⟩, ⟨⟨[1, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 4], 0, 1, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 2], 0, 1, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 4], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 7, 2], 0, 1, true⟩, true⟩])]
theorem groupPlan001_09_ok : groupChecks row001 groupPlan001_09 = true := by
  change groupChecks row001 (groupPlan001_09_Word45to47 ++ groupPlan001_09_Word48 ++ groupPlan001_09_Word49) = true
  simp only [groupChecks_append, groupPlan001_09_Word45to47_ok, groupPlan001_09_Word48_ok, groupPlan001_09_Word49_ok, Bool.true_and]

def groupPlan001_10 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 1, true⟩, true⟩]),
   (markWords51, [⟨⟨[1, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[1, 4, 5, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6, 3], 7, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6, 2], 7, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6, 3], 7, 1, false⟩, true⟩]),
   (markWords52, [⟨⟨[1, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 0, 2, true⟩, true⟩, ⟨⟨[1, 4, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 3], 0, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 2], 0, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7, 3], 0, 1, true⟩, true⟩, ⟨⟨[1, 4, 5, 7, 2], 0, 1, true⟩, true⟩]),
   (markWords53, [⟨⟨[1, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 0, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 2, 1, true⟩, true⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 4, 2, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 3, 2, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 2, 2, false⟩, false⟩])]
theorem groupPlan001_10_ok : groupChecks row001 groupPlan001_10 = true := by
  change groupChecks row001 (groupPlan001_10_Word50 ++ groupPlan001_10_Word51 ++ groupPlan001_10_Word52 ++ groupPlan001_10_Word53to54) = true
  simp only [groupChecks_append, groupPlan001_10_Word50_ok, groupPlan001_10_Word51_ok, groupPlan001_10_Word52_ok, groupPlan001_10_Word53to54_ok, Bool.true_and]

def groupPlan001_11 : GroupPortPlan :=
  [(markWords55, [⟨⟨[2, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords56, [⟨⟨[2, 3, 4, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 6], 0, 2, true⟩, true⟩, ⟨⟨[2, 3, 4, 6, 5], 0, 1, false⟩, false⟩, ⟨⟨[2, 3, 4, 6, 1], 0, 1, true⟩, true⟩]),
   (markWords57, [⟨⟨[2, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 6, 2, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 0, 2, true⟩, true⟩, ⟨⟨[2, 3, 4, 7, 5], 0, 1, false⟩, false⟩, ⟨⟨[2, 3, 4, 7, 1], 0, 1, true⟩, true⟩]),
   (markWords58, [⟨⟨[2, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords59, [⟨⟨[2, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan001_11_ok : groupChecks row001 groupPlan001_11 = true := by decide +kernel

def groupPlan001_12 : GroupPortPlan :=
  [(markWords60, [⟨⟨[2, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords61, [⟨⟨[2, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords62, [⟨⟨[2, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords63, [⟨⟨[2, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords64, [⟨⟨[2, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 4, 1, false⟩, true⟩])]
theorem groupPlan001_12_ok : groupChecks row001 groupPlan001_12 = true := by decide +kernel

def groupPlan001_13 : GroupPortPlan :=
  [(markWords65, [⟨⟨[3, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords66, [⟨⟨[3, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords67, [⟨⟨[3, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords68, [⟨⟨[3, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords69, [⟨⟨[4, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan001_13_ok : groupChecks row001 groupPlan001_13 = true := by decide +kernel

def totalPlan001 : GroupPortPlan :=
  groupPlan001_00 ++ groupPlan001_01 ++ groupPlan001_02 ++ groupPlan001_03 ++ groupPlan001_04 ++ groupPlan001_05 ++ groupPlan001_06 ++ groupPlan001_07 ++ groupPlan001_08 ++ groupPlan001_09 ++ groupPlan001_10 ++ groupPlan001_11 ++ groupPlan001_12 ++ groupPlan001_13

theorem totalPlan001_keys : totalPlan001.map Prod.fst = allMarkGroups := rfl

theorem totalPlan001_ok : groupChecks row001 totalPlan001 = true := by
  simp only [totalPlan001, groupChecks_append, groupPlan001_00_ok, groupPlan001_01_ok, groupPlan001_02_ok, groupPlan001_03_ok, groupPlan001_04_ok, groupPlan001_05_ok, groupPlan001_06_ok, groupPlan001_07_ok, groupPlan001_08_ok, groupPlan001_09_ok, groupPlan001_10_ok, groupPlan001_11_ok, groupPlan001_12_ok, groupPlan001_13_ok, Bool.true_and]

theorem forces001 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row001 := allWordCage_of_plan totalPlan001_keys totalPlan001_ok

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
