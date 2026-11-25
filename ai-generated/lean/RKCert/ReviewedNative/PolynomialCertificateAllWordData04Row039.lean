module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData04
public import RKCert.ReviewedNative.PolynomialCertificateAllWordSeparatedCheck

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan039_00 : GroupPortPlan :=
  [(markWords00, [⟨⟨[0, 1, 2, 3], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 4, 1, true⟩, true⟩]),
   (markWords01, [⟨⟨[0, 1, 2, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 3, 1, true⟩, true⟩]),
   (markWords02, [⟨⟨[0, 1, 2, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 3, 1, true⟩, true⟩]),
   (markWords03, [⟨⟨[0, 1, 2, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 3, 1, true⟩, false⟩]),
   (markWords04, [⟨⟨[0, 1, 2, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 3, 1, true⟩, false⟩])]
theorem groupPlan039_00_ok : groupChecks row039 groupPlan039_00 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_01 : GroupPortPlan :=
  [(markWords05, [⟨⟨[0, 1, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 2, 1, true⟩, true⟩]),
   (markWords06, [⟨⟨[0, 1, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 2, 1, true⟩, true⟩]),
   (markWords07, [⟨⟨[0, 1, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩]),
   (markWords08, [⟨⟨[0, 1, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 2, 1, true⟩, false⟩]),
   (markWords09, [⟨⟨[0, 1, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 2, 1, true⟩, true⟩])]
theorem groupPlan039_01_ok : groupChecks row039 groupPlan039_01 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_02 : GroupPortPlan :=
  [(markWords10, [⟨⟨[0, 1, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 5, 2, false⟩, false⟩, ⟨⟨[0, 1, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 1, 4, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 6, 3], 7, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 6, 2], 7, 1, false⟩, true⟩, ⟨⟨[0, 1, 4, 6, 3], 7, 1, false⟩, true⟩]),
   (markWords11, [⟨⟨[0, 1, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords12, [⟨⟨[0, 1, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 2, 1, true⟩, true⟩]),
   (markWords13, [⟨⟨[0, 1, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 2, 1, true⟩, true⟩]),
   (markWords14, [⟨⟨[0, 1, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 5, 1, true⟩, true⟩])]
theorem groupPlan039_02_ok : groupChecks row039 groupPlan039_02 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_03 : GroupPortPlan :=
  [(markWords15, [⟨⟨[0, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 1, 1, true⟩, true⟩]),
   (markWords16, [⟨⟨[0, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 1, 1, true⟩, true⟩]),
   (markWords17, [⟨⟨[0, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩]),
   (markWords18, [⟨⟨[0, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 1, 1, true⟩, false⟩]),
   (markWords19, [⟨⟨[0, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 1, 1, true⟩, true⟩])]
theorem groupPlan039_03_ok : groupChecks row039 groupPlan039_03 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_04 : GroupPortPlan :=
  [(markWords20, [⟨⟨[0, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 5, 2, false⟩, false⟩, ⟨⟨[0, 2, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 2, 4, 6, 1], 7, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 6, 3], 7, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 6, 1], 7, 1, false⟩, true⟩, ⟨⟨[0, 2, 4, 6, 3], 7, 1, false⟩, true⟩]),
   (markWords21, [⟨⟨[0, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords22, [⟨⟨[0, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[0, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords23, [⟨⟨[0, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩]),
   (markWords24, [⟨⟨[0, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 1, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 5, 1, true⟩, true⟩])]
theorem groupPlan039_04_ok : groupChecks row039 groupPlan039_04 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_05 : GroupPortPlan :=
  [(markWords25, [⟨⟨[0, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords26, [⟨⟨[0, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 5, 2, false⟩, false⟩, ⟨⟨[0, 3, 4, 6], 7, 2, false⟩, true⟩, ⟨⟨[0, 3, 4, 6, 2], 7, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6, 1], 7, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6, 2], 7, 1, false⟩, true⟩, ⟨⟨[0, 3, 4, 6, 1], 7, 1, false⟩, true⟩]),
   (markWords27, [⟨⟨[0, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords28, [⟨⟨[0, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 7, 1, false⟩, true⟩, ⟨⟨[0, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 4, 2, false⟩, true⟩, ⟨⟨[0, 3, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords29, [⟨⟨[0, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 3, 5, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 7], 1, 1, true⟩, true⟩])]
theorem groupPlan039_05_ok : groupChecks row039 groupPlan039_05 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_06 : GroupPortPlan :=
  [(markWords30, [⟨⟨[0, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 1, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 5, 1, true⟩, true⟩]),
   (markWords31, [⟨⟨[0, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 4, 5, 6], 2, 2, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 1, 2, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 3, 2, true⟩, false⟩]),
   (markWords32, [⟨⟨[0, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords33, [⟨⟨[0, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords34, [⟨⟨[0, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 1, 1, false⟩, false⟩])]
theorem groupPlan039_06_ok : groupChecks row039 groupPlan039_06 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_07 : GroupPortPlan :=
  [(markWords35, [⟨⟨[1, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 0, 1, true⟩, true⟩]),
   (markWords36, [⟨⟨[1, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 0, 1, true⟩, true⟩]),
   (markWords37, [⟨⟨[1, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩]),
   (markWords38, [⟨⟨[1, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 0, 1, true⟩, false⟩]),
   (markWords39, [⟨⟨[1, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 3, 1, true⟩, true⟩])]
theorem groupPlan039_07_ok : groupChecks row039 groupPlan039_07 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_08 : GroupPortPlan :=
  [(markWords40, [⟨⟨[1, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords41, [⟨⟨[1, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 3, 1, false⟩, true⟩]),
   (markWords42, [⟨⟨[1, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩]),
   (markWords43, [⟨⟨[1, 2, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords44, [⟨⟨[1, 2, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan039_08_ok : groupChecks row039 groupPlan039_08 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_09 : GroupPortPlan :=
  [(markWords45, [⟨⟨[1, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 2, 1, true⟩, true⟩]),
   (markWords46, [⟨⟨[1, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords47, [⟨⟨[1, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 2, 1, false⟩, true⟩]),
   (markWords48, [⟨⟨[1, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 2, 1, true⟩, true⟩]),
   (markWords49, [⟨⟨[1, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan039_09_ok : groupChecks row039 groupPlan039_09 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_10 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 1, false⟩, true⟩]),
   (markWords51, [⟨⟨[1, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 2, false⟩, true⟩]),
   (markWords52, [⟨⟨[1, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords53, [⟨⟨[1, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 5, 2, false⟩, true⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 4, 2, false⟩, false⟩])]
theorem groupPlan039_10_ok : groupChecks row039 groupPlan039_10 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_11 : GroupPortPlan :=
  [(markWords55, [⟨⟨[2, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords56, [⟨⟨[2, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[2, 3, 4, 6], 1, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords57, [⟨⟨[2, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 1, 1, true⟩, false⟩, ⟨⟨[2, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 1, 1, false⟩, true⟩]),
   (markWords58, [⟨⟨[2, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[2, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[2, 3, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords59, [⟨⟨[2, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan039_11_ok : groupChecks row039 groupPlan039_11 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_12 : GroupPortPlan :=
  [(markWords60, [⟨⟨[2, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 1, 1, false⟩, true⟩]),
   (markWords61, [⟨⟨[2, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 7, 2, false⟩, true⟩]),
   (markWords62, [⟨⟨[2, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords63, [⟨⟨[2, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 5, 2, false⟩, true⟩]),
   (markWords64, [⟨⟨[2, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 4, 2, false⟩, false⟩])]
theorem groupPlan039_12_ok : groupChecks row039 groupPlan039_12 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan039_13 : GroupPortPlan :=
  [(markWords65, [⟨⟨[3, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords66, [⟨⟨[3, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords67, [⟨⟨[3, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords68, [⟨⟨[3, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 0, 2, true⟩, true⟩, ⟨⟨[3, 5, 6, 7, 4], 0, 1, false⟩, false⟩, ⟨⟨[3, 5, 6, 7, 4], 2, 1, false⟩, false⟩, ⟨⟨[3, 5, 6, 7, 4], 1, 1, false⟩, false⟩]),
   (markWords69, [⟨⟨[4, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan039_13_ok : groupChecks row039 groupPlan039_13 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def totalPlan039 : GroupPortPlan :=
  groupPlan039_00 ++ groupPlan039_01 ++ groupPlan039_02 ++ groupPlan039_03 ++ groupPlan039_04 ++ groupPlan039_05 ++ groupPlan039_06 ++ groupPlan039_07 ++ groupPlan039_08 ++ groupPlan039_09 ++ groupPlan039_10 ++ groupPlan039_11 ++ groupPlan039_12 ++ groupPlan039_13

theorem totalPlan039_keys : totalPlan039.map Prod.fst = allMarkGroups := rfl

theorem totalPlan039_ok : groupChecks row039 totalPlan039 = true := by
  simp only [totalPlan039, groupChecks_append, groupPlan039_00_ok, groupPlan039_01_ok, groupPlan039_02_ok, groupPlan039_03_ok, groupPlan039_04_ok, groupPlan039_05_ok, groupPlan039_06_ok, groupPlan039_07_ok, groupPlan039_08_ok, groupPlan039_09_ok, groupPlan039_10_ok, groupPlan039_11_ok, groupPlan039_12_ok, groupPlan039_13_ok, Bool.true_and]

theorem forces039 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row039 := allWordCage_of_plan totalPlan039_keys totalPlan039_ok

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
