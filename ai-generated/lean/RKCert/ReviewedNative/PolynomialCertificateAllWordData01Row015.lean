module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData01
public import RKCert.ReviewedNative.PolynomialCertificateAllWordSeparatedCheck

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan015_00 : GroupPortPlan :=
  [(markWords00, [⟨⟨[0, 1, 2, 3], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 4, 1, true⟩, true⟩]),
   (markWords01, [⟨⟨[0, 1, 2, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 3, 1, true⟩, true⟩]),
   (markWords02, [⟨⟨[0, 1, 2, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 3, 1, true⟩, true⟩]),
   (markWords03, [⟨⟨[0, 1, 2, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 3, 1, true⟩, false⟩]),
   (markWords04, [⟨⟨[0, 1, 2, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 3, 1, true⟩, false⟩])]
theorem groupPlan015_00_ok : groupChecks row015 groupPlan015_00 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_01 : GroupPortPlan :=
  [(markWords05, [⟨⟨[0, 1, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 2, 1, true⟩, true⟩]),
   (markWords06, [⟨⟨[0, 1, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 2, 1, true⟩, true⟩]),
   (markWords07, [⟨⟨[0, 1, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩]),
   (markWords08, [⟨⟨[0, 1, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 2, 1, true⟩, false⟩]),
   (markWords09, [⟨⟨[0, 1, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 2, 1, true⟩, true⟩])]
theorem groupPlan015_01_ok : groupChecks row015 groupPlan015_01 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_02 : GroupPortPlan :=
  [(markWords10, [⟨⟨[0, 1, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 2, 1, true⟩, false⟩]),
   (markWords11, [⟨⟨[0, 1, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords12, [⟨⟨[0, 1, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords13, [⟨⟨[0, 1, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 7], 4, 2, true⟩, true⟩]),
   (markWords14, [⟨⟨[0, 1, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 6, 7], 2, 1, true⟩, true⟩])]
theorem groupPlan015_02_ok : groupChecks row015 groupPlan015_02 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_03 : GroupPortPlan :=
  [(markWords15, [⟨⟨[0, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 1, 1, true⟩, true⟩]),
   (markWords16, [⟨⟨[0, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 1, 1, true⟩, true⟩]),
   (markWords17, [⟨⟨[0, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩]),
   (markWords18, [⟨⟨[0, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 1, 1, true⟩, false⟩]),
   (markWords19, [⟨⟨[0, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 1, 1, true⟩, true⟩])]
theorem groupPlan015_03_ok : groupChecks row015 groupPlan015_03 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_04 : GroupPortPlan :=
  [(markWords20, [⟨⟨[0, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 1, 1, true⟩, false⟩]),
   (markWords21, [⟨⟨[0, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords22, [⟨⟨[0, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords23, [⟨⟨[0, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 5, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩]),
   (markWords24, [⟨⟨[0, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 1, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 5, 1, true⟩, true⟩])]
theorem groupPlan015_04_ok : groupChecks row015 groupPlan015_04 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_05 : GroupPortPlan :=
  [(markWords25, [⟨⟨[0, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords26, [⟨⟨[0, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 1, 1, true⟩, false⟩]),
   (markWords27, [⟨⟨[0, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords28, [⟨⟨[0, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords29, [⟨⟨[0, 3, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 3, 5, 7], 1, 1, true⟩, true⟩])]
theorem groupPlan015_05_ok : groupChecks row015 groupPlan015_05 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_06 : GroupPortPlan :=
  [(markWords30, [⟨⟨[0, 3, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 2, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 1, 1, true⟩, true⟩, ⟨⟨[0, 3, 6, 7], 5, 1, true⟩, true⟩]),
   (markWords31, [⟨⟨[0, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 4, 5, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 3, 2, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 2, 2, true⟩, false⟩]),
   (markWords32, [⟨⟨[0, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords33, [⟨⟨[0, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords34, [⟨⟨[0, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 1, 1, false⟩, false⟩])]
theorem groupPlan015_06_ok : groupChecks row015 groupPlan015_06 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_07 : GroupPortPlan :=
  [(markWords35, [⟨⟨[1, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 0, 1, true⟩, true⟩]),
   (markWords36, [⟨⟨[1, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 0, 1, true⟩, true⟩]),
   (markWords37, [⟨⟨[1, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 0, 1, true⟩, false⟩]),
   (markWords38, [⟨⟨[1, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 0, 1, true⟩, false⟩]),
   (markWords39, [⟨⟨[1, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 0, 1, true⟩, true⟩])]
theorem groupPlan015_07_ok : groupChecks row015 groupPlan015_07 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_08 : GroupPortPlan :=
  [(markWords40, [⟨⟨[1, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords41, [⟨⟨[1, 2, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 3, 1, false⟩, true⟩]),
   (markWords42, [⟨⟨[1, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩]),
   (markWords43, [⟨⟨[1, 2, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords44, [⟨⟨[1, 2, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan015_08_ok : groupChecks row015 groupPlan015_08 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_09 : GroupPortPlan :=
  [(markWords45, [⟨⟨[1, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 2, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 0, 1, true⟩, true⟩]),
   (markWords46, [⟨⟨[1, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords47, [⟨⟨[1, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 2, 1, false⟩, true⟩]),
   (markWords48, [⟨⟨[1, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[1, 3, 5, 6], 2, 1, true⟩, true⟩]),
   (markWords49, [⟨⟨[1, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan015_09_ok : groupChecks row015 groupPlan015_09 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_10 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 1, false⟩, true⟩]),
   (markWords51, [⟨⟨[1, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords52, [⟨⟨[1, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords53, [⟨⟨[1, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 4, 2, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 2, 1, false⟩, true⟩])]
theorem groupPlan015_10_ok : groupChecks row015 groupPlan015_10 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_11 : GroupPortPlan :=
  [(markWords55, [⟨⟨[2, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords56, [⟨⟨[2, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[2, 3, 4, 6], 0, 2, true⟩, true⟩, ⟨⟨[2, 3, 4, 6], 1, 1, true⟩, false⟩]),
   (markWords57, [⟨⟨[2, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 5, 2, false⟩, false⟩]),
   (markWords58, [⟨⟨[2, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords59, [⟨⟨[2, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan015_11_ok : groupChecks row015 groupPlan015_11 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_12 : GroupPortPlan :=
  [(markWords60, [⟨⟨[2, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords61, [⟨⟨[2, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords62, [⟨⟨[2, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords63, [⟨⟨[2, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords64, [⟨⟨[2, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 4, 1, false⟩, true⟩])]
theorem groupPlan015_12_ok : groupChecks row015 groupPlan015_12 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def groupPlan015_13 : GroupPortPlan :=
  [(markWords65, [⟨⟨[3, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords66, [⟨⟨[3, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 6, 2, false⟩, false⟩]),
   (markWords67, [⟨⟨[3, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords68, [⟨⟨[3, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords69, [⟨⟨[4, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 2, 1, false⟩, true⟩])]
theorem groupPlan015_13_ok : groupChecks row015 groupPlan015_13 = true := by
  rw [← SeparatedCheck.groupCheck_eq]
  decide +kernel

def totalPlan015 : GroupPortPlan :=
  groupPlan015_00 ++ groupPlan015_01 ++ groupPlan015_02 ++ groupPlan015_03 ++ groupPlan015_04 ++ groupPlan015_05 ++ groupPlan015_06 ++ groupPlan015_07 ++ groupPlan015_08 ++ groupPlan015_09 ++ groupPlan015_10 ++ groupPlan015_11 ++ groupPlan015_12 ++ groupPlan015_13

theorem totalPlan015_keys : totalPlan015.map Prod.fst = allMarkGroups := rfl

theorem totalPlan015_ok : groupChecks row015 totalPlan015 = true := by
  simp only [totalPlan015, groupChecks_append, groupPlan015_00_ok, groupPlan015_01_ok, groupPlan015_02_ok, groupPlan015_03_ok, groupPlan015_04_ok, groupPlan015_05_ok, groupPlan015_06_ok, groupPlan015_07_ok, groupPlan015_08_ok, groupPlan015_09_ok, groupPlan015_10_ok, groupPlan015_11_ok, groupPlan015_12_ok, groupPlan015_13_ok, Bool.true_and]

theorem forces015 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row015 := allWordCage_of_plan totalPlan015_keys totalPlan015_ok

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
