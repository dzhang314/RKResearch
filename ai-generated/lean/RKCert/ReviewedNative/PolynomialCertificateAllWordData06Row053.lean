module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData06
public import RKCert.ReviewedNative.PolynomialCertificateAllWordSeparatedCheck

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan053_00 : GroupPortPlan :=
  [(markWords00, [⟨⟨[0, 1, 2, 3], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 4, 1, true⟩, true⟩]),
   (markWords01, [⟨⟨[0, 1, 2, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 3, 1, true⟩, true⟩]),
   (markWords02, [⟨⟨[0, 1, 2, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 3, 2, true⟩, false⟩]),
   (markWords03, [⟨⟨[0, 1, 2, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 5, 2, true⟩, false⟩]),
   (markWords04, [⟨⟨[0, 1, 2, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 6, 1, true⟩, false⟩])]
theorem groupPlan053_00_ok : groupChecks row053 groupPlan053_00 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_01 : GroupPortPlan :=
  [(markWords05, [⟨⟨[0, 1, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 2, 1, true⟩, true⟩]),
   (markWords06, [⟨⟨[0, 1, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 2, 1, true⟩, true⟩]),
   (markWords07, [⟨⟨[0, 1, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩]),
   (markWords08, [⟨⟨[0, 1, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 2, 1, true⟩, false⟩]),
   (markWords09, [⟨⟨[0, 1, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 2, 1, true⟩, true⟩])]
theorem groupPlan053_01_ok : groupChecks row053 groupPlan053_01 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_02 : GroupPortPlan :=
  [(markWords10, [⟨⟨[0, 1, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 2, 2, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, false⟩, false⟩, ⟨⟨[0, 1, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 1, 4, 6], 2, 2, false⟩, true⟩]),
   (markWords11, [⟨⟨[0, 1, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 2, 2, true⟩, true⟩]),
   (markWords12, [⟨⟨[0, 1, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords13, [⟨⟨[0, 1, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 6, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 2, 2, false⟩, true⟩]),
   (markWords14, [⟨⟨[0, 1, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 2, 2, false⟩, true⟩])]
theorem groupPlan053_02_ok : groupChecks row053 groupPlan053_02 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_03 : GroupPortPlan :=
  [(markWords15, [⟨⟨[0, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 1, 1, true⟩, true⟩]),
   (markWords16, [⟨⟨[0, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 1, 1, true⟩, true⟩]),
   (markWords17, [⟨⟨[0, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩]),
   (markWords18, [⟨⟨[0, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 1, 1, true⟩, false⟩]),
   (markWords19, [⟨⟨[0, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 1, 1, true⟩, true⟩])]
theorem groupPlan053_03_ok : groupChecks row053 groupPlan053_03 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_04 : GroupPortPlan :=
  [(markWords20, [⟨⟨[0, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 1, 2, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 3, 1, true⟩, false⟩]),
   (markWords21, [⟨⟨[0, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords22, [⟨⟨[0, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 1, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords23, [⟨⟨[0, 2, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 2, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 2, 5, 7], 6, 1, false⟩, true⟩, ⟨⟨[0, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩]),
   (markWords24, [⟨⟨[0, 2, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 2, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 2, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 2, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 5, 1, true⟩, true⟩])]
theorem groupPlan053_04_ok : groupChecks row053 groupPlan053_04 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_05 : GroupPortPlan :=
  [(markWords25, [⟨⟨[0, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords26, [⟨⟨[0, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 1, 1, true⟩, false⟩]),
   (markWords27, [⟨⟨[0, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords28, [⟨⟨[0, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[0, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 4, 2, false⟩, true⟩, ⟨⟨[0, 3, 5, 6, 1], 7, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 6, 1], 7, 1, false⟩, true⟩, ⟨⟨[0, 3, 5, 6, 2], 7, 1, false⟩, true⟩]),
   (markWords29, [⟨⟨[0, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 3, 5, 7], 4, 2, false⟩, true⟩, ⟨⟨[0, 3, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[0, 3, 5, 7, 1], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 7, 2], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 7, 2], 6, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7, 1], 6, 1, false⟩, false⟩])]
theorem groupPlan053_05_ok : groupChecks row053 groupPlan053_05 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_06 : GroupPortPlan :=
  [(markWords30, [⟨⟨[0, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 3, 6, 7], 4, 2, false⟩, true⟩, ⟨⟨[0, 3, 6, 7, 1], 4, 1, true⟩, false⟩, ⟨⟨[0, 3, 6, 7, 1], 5, 1, true⟩, false⟩]),
   (markWords31, [⟨⟨[0, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 4, 5, 6], 2, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 3, 2, true⟩, false⟩]),
   (markWords32, [⟨⟨[0, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 7], 1, 1, true⟩, false⟩]),
   (markWords33, [⟨⟨[0, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 5, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[0, 4, 6, 7], 3, 2, true⟩, false⟩, ⟨⟨[0, 4, 6, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 4, 6, 7], 1, 1, true⟩, false⟩]),
   (markWords34, [⟨⟨[0, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 5, 6, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 5, 6, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 5, 6, 7], 1, 1, true⟩, false⟩])]
theorem groupPlan053_06_ok : groupChecks row053 groupPlan053_06 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_07 : GroupPortPlan :=
  [(markWords35, [⟨⟨[1, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 0, 1, true⟩, true⟩]),
   (markWords36, [⟨⟨[1, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 0, 1, true⟩, true⟩]),
   (markWords37, [⟨⟨[1, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩]),
   (markWords38, [⟨⟨[1, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 0, 1, true⟩, false⟩]),
   (markWords39, [⟨⟨[1, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 0, 1, true⟩, true⟩])]
theorem groupPlan053_07_ok : groupChecks row053 groupPlan053_07 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_08 : GroupPortPlan :=
  [(markWords40, [⟨⟨[1, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 3, 1, true⟩, false⟩]),
   (markWords41, [⟨⟨[1, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 0, 1, true⟩, false⟩]),
   (markWords42, [⟨⟨[1, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords43, [⟨⟨[1, 2, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 7], 4, 2, true⟩, true⟩]),
   (markWords44, [⟨⟨[1, 2, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 6, 7], 5, 1, true⟩, true⟩])]
theorem groupPlan053_08_ok : groupChecks row053 groupPlan053_08 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_09 : GroupPortPlan :=
  [(markWords45, [⟨⟨[1, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 0, 1, true⟩, true⟩]),
   (markWords46, [⟨⟨[1, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 0, 1, true⟩, false⟩]),
   (markWords47, [⟨⟨[1, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 0, 1, true⟩, false⟩]),
   (markWords48, [⟨⟨[1, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 2, false⟩, true⟩, ⟨⟨[1, 3, 5, 6, 0], 7, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 6, 0], 7, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 6, 2], 7, 1, false⟩, true⟩]),
   (markWords49, [⟨⟨[1, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[1, 3, 5, 7], 4, 2, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 0], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 7, 2], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 7, 2], 6, 1, false⟩, false⟩, ⟨⟨[1, 3, 5, 7, 0], 6, 1, false⟩, false⟩])]
theorem groupPlan053_09_ok : groupChecks row053 groupPlan053_09 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_10 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 1, true⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 2, false⟩, true⟩, ⟨⟨[1, 3, 6, 7, 0], 4, 1, true⟩, false⟩, ⟨⟨[1, 3, 6, 7, 0], 5, 1, true⟩, false⟩]),
   (markWords51, [⟨⟨[1, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 4, 5, 6], 2, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6], 0, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 6], 3, 2, true⟩, false⟩]),
   (markWords52, [⟨⟨[1, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 7], 3, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 7], 2, 1, true⟩, false⟩, ⟨⟨[1, 4, 5, 7], 0, 1, true⟩, false⟩]),
   (markWords53, [⟨⟨[1, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, false⟩, ⟨⟨[1, 4, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 2, true⟩, false⟩, ⟨⟨[1, 4, 6, 7], 2, 1, true⟩, false⟩, ⟨⟨[1, 4, 6, 7], 0, 1, true⟩, false⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 3, 1, true⟩, false⟩, ⟨⟨[1, 5, 6, 7], 4, 1, true⟩, false⟩, ⟨⟨[1, 5, 6, 7], 2, 1, true⟩, false⟩, ⟨⟨[1, 5, 6, 7], 0, 1, true⟩, false⟩])]
theorem groupPlan053_10_ok : groupChecks row053 groupPlan053_10 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_11 : GroupPortPlan :=
  [(markWords55, [⟨⟨[2, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 1, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 0, 1, true⟩, true⟩]),
   (markWords56, [⟨⟨[2, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[2, 3, 4, 6], 5, 2, false⟩, false⟩, ⟨⟨[2, 3, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 0, 1, false⟩, true⟩]),
   (markWords57, [⟨⟨[2, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 0, 1, false⟩, true⟩]),
   (markWords58, [⟨⟨[2, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 4, 1, false⟩, true⟩]),
   (markWords59, [⟨⟨[2, 3, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan053_11_ok : groupChecks row053 groupPlan053_11 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_12 : GroupPortPlan :=
  [(markWords60, [⟨⟨[2, 3, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords61, [⟨⟨[2, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 4, 5, 6], 3, 2, true⟩, false⟩, ⟨⟨[2, 4, 5, 6], 3, 2, false⟩, false⟩, ⟨⟨[2, 4, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 0, 1, false⟩, true⟩]),
   (markWords62, [⟨⟨[2, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 3, 2, false⟩, false⟩, ⟨⟨[2, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords63, [⟨⟨[2, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 3, 2, false⟩, false⟩, ⟨⟨[2, 4, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords64, [⟨⟨[2, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[2, 5, 6, 7], 3, 2, false⟩, false⟩])]
theorem groupPlan053_12_ok : groupChecks row053 groupPlan053_12 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan053_13 : GroupPortPlan :=
  [(markWords65, [⟨⟨[3, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords66, [⟨⟨[3, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords67, [⟨⟨[3, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords68, [⟨⟨[3, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords69, [⟨⟨[4, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan053_13_ok : groupChecks row053 groupPlan053_13 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def totalPlan053 : GroupPortPlan :=
  groupPlan053_00 ++ groupPlan053_01 ++ groupPlan053_02 ++ groupPlan053_03 ++ groupPlan053_04 ++ groupPlan053_05 ++ groupPlan053_06 ++ groupPlan053_07 ++ groupPlan053_08 ++ groupPlan053_09 ++ groupPlan053_10 ++ groupPlan053_11 ++ groupPlan053_12 ++ groupPlan053_13

theorem totalPlan053_keys : totalPlan053.map Prod.fst = allMarkGroups := rfl

theorem totalPlan053_ok : groupChecks row053 totalPlan053 = true := by
  simp only [totalPlan053, groupChecks_append, groupPlan053_00_ok, groupPlan053_01_ok, groupPlan053_02_ok, groupPlan053_03_ok, groupPlan053_04_ok, groupPlan053_05_ok, groupPlan053_06_ok, groupPlan053_07_ok, groupPlan053_08_ok, groupPlan053_09_ok, groupPlan053_10_ok, groupPlan053_11_ok, groupPlan053_12_ok, groupPlan053_13_ok, Bool.true_and]

theorem forces053 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row053 := allWordCage_of_plan totalPlan053_keys totalPlan053_ok

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
