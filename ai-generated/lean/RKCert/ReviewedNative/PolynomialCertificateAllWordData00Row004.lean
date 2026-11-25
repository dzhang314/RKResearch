module

public import RKCert.ReviewedNative.PolynomialCertificateAllMarkWords
public import RKCert.ReviewedNative.PolynomialCertificateWeakFiveCageData00

@[expose] public section

namespace RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

set_option maxRecDepth 48000
set_option maxHeartbeats 16000000

def groupPlan004_00 : GroupPortPlan :=
  [(markWords00, [⟨⟨[0, 1, 2, 3], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 3], 4, 1, true⟩, true⟩]),
   (markWords01, [⟨⟨[0, 1, 2, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 4], 3, 1, true⟩, true⟩]),
   (markWords02, [⟨⟨[0, 1, 2, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 5], 3, 1, true⟩, true⟩]),
   (markWords03, [⟨⟨[0, 1, 2, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 2, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 6], 5, 2, true⟩, false⟩]),
   (markWords04, [⟨⟨[0, 1, 2, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 2, 7], 6, 1, true⟩, false⟩])]
theorem groupPlan004_00_ok : groupChecks row004 groupPlan004_00 = true := by decide +kernel

def groupPlan004_01 : GroupPortPlan :=
  [(markWords05, [⟨⟨[0, 1, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 4], 2, 1, true⟩, true⟩]),
   (markWords06, [⟨⟨[0, 1, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 5], 2, 1, true⟩, true⟩]),
   (markWords07, [⟨⟨[0, 1, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 3, 6], 2, 1, true⟩, false⟩]),
   (markWords08, [⟨⟨[0, 1, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 3, 7], 2, 1, true⟩, false⟩]),
   (markWords09, [⟨⟨[0, 1, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 5], 2, 1, true⟩, true⟩])]
theorem groupPlan004_01_ok : groupChecks row004 groupPlan004_01 = true := by decide +kernel

def groupPlan004_02 : GroupPortPlan :=
  [(markWords10, [⟨⟨[0, 1, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 6], 2, 2, true⟩, true⟩]),
   (markWords11, [⟨⟨[0, 1, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 1, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords12, [⟨⟨[0, 1, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 2, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 1, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords13, [⟨⟨[0, 1, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 6, 1, false⟩, true⟩, ⟨⟨[0, 1, 5, 7], 2, 1, false⟩, true⟩]),
   (markWords14, [⟨⟨[0, 1, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[0, 1, 6, 7], 2, 1, false⟩, true⟩])]
theorem groupPlan004_02_ok : groupChecks row004 groupPlan004_02 = true := by decide +kernel

def groupPlan004_03 : GroupPortPlan :=
  [(markWords15, [⟨⟨[0, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 4], 1, 1, true⟩, true⟩]),
   (markWords16, [⟨⟨[0, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 5], 1, 1, true⟩, true⟩]),
   (markWords17, [⟨⟨[0, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 3, 6], 1, 1, true⟩, false⟩]),
   (markWords18, [⟨⟨[0, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 4, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 3, 7], 1, 1, true⟩, false⟩]),
   (markWords19, [⟨⟨[0, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 5], 1, 1, true⟩, true⟩])]
theorem groupPlan004_03_ok : groupChecks row004 groupPlan004_03 = true := by decide +kernel

def groupPlan004_04 : GroupPortPlan :=
  [(markWords20, [⟨⟨[0, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 6], 3, 1, true⟩, false⟩]),
   (markWords21, [⟨⟨[0, 2, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 3, 1, true⟩, false⟩, ⟨⟨[0, 2, 4, 7], 1, 1, true⟩, false⟩]),
   (markWords22, [⟨⟨[0, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 5, 6], 1, 1, true⟩, true⟩]),
   (markWords23, [⟨⟨[0, 2, 5, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 2, 5, 7], 3, 2, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 4, 2, true⟩, true⟩, ⟨⟨[0, 2, 5, 7], 1, 1, true⟩, true⟩]),
   (markWords24, [⟨⟨[0, 2, 6, 7], 3, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 4, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 5, 1, true⟩, true⟩, ⟨⟨[0, 2, 6, 7], 1, 1, true⟩, true⟩])]
theorem groupPlan004_04_ok : groupChecks row004 groupPlan004_04 = true := by decide +kernel

def groupPlan004_05 : GroupPortPlan :=
  [(markWords25, [⟨⟨[0, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 5], 1, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 5], 2, 1, true⟩, true⟩]),
   (markWords26, [⟨⟨[0, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 4, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[0, 3, 4, 6], 2, 1, true⟩, false⟩]),
   (markWords27, [⟨⟨[0, 3, 4, 7], 5, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 6, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 1, 1, true⟩, false⟩, ⟨⟨[0, 3, 4, 7], 2, 1, true⟩, false⟩]),
   (markWords28, [⟨⟨[0, 3, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 3, 5, 6], 4, 1, true⟩, true⟩, ⟨⟨[0, 3, 5, 6], 2, 2, true⟩, false⟩]),
   (markWords29, [⟨⟨[0, 3, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 3, 5, 7], 6, 1, false⟩, false⟩])]
theorem groupPlan004_05_ok : groupChecks row004 groupPlan004_05 = true := by decide +kernel

def groupPlan004_06 : GroupPortPlan :=
  [(markWords30, [⟨⟨[0, 3, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 3, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords31, [⟨⟨[0, 4, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[0, 4, 5, 6], 1, 1, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 2, 2, true⟩, false⟩, ⟨⟨[0, 4, 5, 6], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 6], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 6], 7, 1, false⟩, false⟩]),
   (markWords32, [⟨⟨[0, 4, 5, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords33, [⟨⟨[0, 4, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 1, 1, false⟩, false⟩, ⟨⟨[0, 4, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords34, [⟨⟨[0, 5, 6, 7], 2, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[0, 5, 6, 7], 1, 1, false⟩, false⟩])]
theorem groupPlan004_06_ok : groupChecks row004 groupPlan004_06 = true := by decide +kernel

def groupPlan004_07 : GroupPortPlan :=
  [(markWords35, [⟨⟨[1, 2, 3, 4], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 5, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 4], 0, 1, true⟩, true⟩]),
   (markWords36, [⟨⟨[1, 2, 3, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 4, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 5], 0, 1, true⟩, true⟩]),
   (markWords37, [⟨⟨[1, 2, 3, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 3, 6], 4, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 3, 6], 0, 2, true⟩, true⟩]),
   (markWords38, [⟨⟨[1, 2, 3, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 3, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 3, 7], 5, 1, false⟩, false⟩, ⟨⟨[1, 2, 3, 7], 5, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 6, 1, true⟩, false⟩, ⟨⟨[1, 2, 3, 7], 0, 1, true⟩, false⟩]),
   (markWords39, [⟨⟨[1, 2, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 5], 0, 1, true⟩, true⟩])]
theorem groupPlan004_07_ok : groupChecks row004 groupPlan004_07 = true := by decide +kernel

def groupPlan004_08 : GroupPortPlan :=
  [(markWords40, [⟨⟨[1, 2, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 2, 4, 6], 0, 2, true⟩, true⟩, ⟨⟨[1, 2, 4, 6], 3, 1, true⟩, false⟩]),
   (markWords41, [⟨⟨[1, 2, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 5, 2, false⟩, false⟩, ⟨⟨[1, 2, 4, 7], 3, 1, false⟩, true⟩]),
   (markWords42, [⟨⟨[1, 2, 5, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 3, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 0, 1, true⟩, true⟩, ⟨⟨[1, 2, 5, 6], 4, 1, true⟩, true⟩]),
   (markWords43, [⟨⟨[1, 2, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[1, 2, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords44, [⟨⟨[1, 2, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 5, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[1, 2, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan004_08_ok : groupChecks row004 groupPlan004_08 = true := by decide +kernel

def groupPlan004_09 : GroupPortPlan :=
  [(markWords45, [⟨⟨[1, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 5], 2, 1, true⟩, true⟩]),
   (markWords46, [⟨⟨[1, 3, 4, 6], 7, 1, true⟩, true⟩, ⟨⟨[1, 3, 4, 6], 5, 2, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 2, 1, true⟩, false⟩, ⟨⟨[1, 3, 4, 6], 0, 2, true⟩, true⟩]),
   (markWords47, [⟨⟨[1, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 4, 7], 6, 1, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 2, 2, false⟩, false⟩, ⟨⟨[1, 3, 4, 7], 5, 1, false⟩, false⟩]),
   (markWords48, [⟨⟨[1, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 6], 2, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 6], 7, 2, false⟩, true⟩, ⟨⟨[1, 3, 5, 6], 4, 2, false⟩, false⟩]),
   (markWords49, [⟨⟨[1, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 5, 7], 2, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 7], 6, 2, false⟩, false⟩, ⟨⟨[1, 3, 5, 7], 4, 1, false⟩, false⟩])]
theorem groupPlan004_09_ok : groupChecks row004 groupPlan004_09 = true := by decide +kernel

def groupPlan004_10 : GroupPortPlan :=
  [(markWords50, [⟨⟨[1, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 2, 2, false⟩, false⟩, ⟨⟨[1, 3, 6, 7], 5, 2, false⟩, true⟩, ⟨⟨[1, 3, 6, 7], 4, 1, false⟩, false⟩]),
   (markWords51, [⟨⟨[1, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 6], 3, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 6], 2, 2, false⟩, false⟩, ⟨⟨[1, 4, 5, 6], 7, 2, false⟩, true⟩]),
   (markWords52, [⟨⟨[1, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 5, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 4, 5, 7], 2, 2, false⟩, false⟩, ⟨⟨[1, 4, 5, 7], 6, 1, false⟩, false⟩]),
   (markWords53, [⟨⟨[1, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 4, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 4, 6, 7], 2, 2, false⟩, false⟩, ⟨⟨[1, 4, 6, 7], 5, 1, false⟩, false⟩]),
   (markWords54, [⟨⟨[1, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[1, 5, 6, 7], 3, 1, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 4, 1, false⟩, false⟩, ⟨⟨[1, 5, 6, 7], 2, 2, false⟩, false⟩])]
theorem groupPlan004_10_ok : groupChecks row004 groupPlan004_10 = true := by decide +kernel

def groupPlan004_11 : GroupPortPlan :=
  [(markWords55, [⟨⟨[2, 3, 4, 5], 7, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 6, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 0, 1, true⟩, true⟩, ⟨⟨[2, 3, 4, 5], 1, 1, true⟩, true⟩]),
   (markWords56, [⟨⟨[2, 3, 4, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 7, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 6], 5, 1, false⟩, true⟩]),
   (markWords57, [⟨⟨[2, 3, 4, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 4, 7], 6, 2, false⟩, false⟩, ⟨⟨[2, 3, 4, 7], 5, 1, false⟩, true⟩]),
   (markWords58, [⟨⟨[2, 3, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords59, [⟨⟨[2, 3, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 5, 7], 6, 1, false⟩, true⟩])]
theorem groupPlan004_11_ok : groupChecks row004 groupPlan004_11 = true := by decide +kernel

def groupPlan004_12 : GroupPortPlan :=
  [(markWords60, [⟨⟨[2, 3, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 4, 1, false⟩, true⟩, ⟨⟨[2, 3, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords61, [⟨⟨[2, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords62, [⟨⟨[2, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords63, [⟨⟨[2, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords64, [⟨⟨[2, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 3, 1, false⟩, true⟩, ⟨⟨[2, 5, 6, 7], 4, 1, false⟩, true⟩])]
theorem groupPlan004_12_ok : groupChecks row004 groupPlan004_12 = true := by decide +kernel

def groupPlan004_13 : GroupPortPlan :=
  [(markWords65, [⟨⟨[3, 4, 5, 6], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 6], 7, 1, false⟩, true⟩]),
   (markWords66, [⟨⟨[3, 4, 5, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 5, 7], 6, 1, false⟩, true⟩]),
   (markWords67, [⟨⟨[3, 4, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 4, 6, 7], 5, 1, false⟩, true⟩]),
   (markWords68, [⟨⟨[3, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[3, 5, 6, 7], 4, 1, false⟩, true⟩]),
   (markWords69, [⟨⟨[4, 5, 6, 7], 0, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 1, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 2, 1, false⟩, true⟩, ⟨⟨[4, 5, 6, 7], 3, 1, false⟩, true⟩])]
theorem groupPlan004_13_ok : groupChecks row004 groupPlan004_13 = true := by decide +kernel

def totalPlan004 : GroupPortPlan :=
  groupPlan004_00 ++ groupPlan004_01 ++ groupPlan004_02 ++ groupPlan004_03 ++ groupPlan004_04 ++ groupPlan004_05 ++ groupPlan004_06 ++ groupPlan004_07 ++ groupPlan004_08 ++ groupPlan004_09 ++ groupPlan004_10 ++ groupPlan004_11 ++ groupPlan004_12 ++ groupPlan004_13

theorem totalPlan004_keys : totalPlan004.map Prod.fst = allMarkGroups := rfl

theorem totalPlan004_ok : groupChecks row004 totalPlan004 = true := by
  simp only [totalPlan004, groupChecks_append, groupPlan004_00_ok, groupPlan004_01_ok, groupPlan004_02_ok, groupPlan004_03_ok, groupPlan004_04_ok, groupPlan004_05_ok, groupPlan004_06_ok, groupPlan004_07_ok, groupPlan004_08_ok, groupPlan004_09_ok, groupPlan004_10_ok, groupPlan004_11_ok, groupPlan004_12_ok, groupPlan004_13_ok, Bool.true_and]

theorem forces004 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    AllWordCage K allMarkGroups row004 := allWordCage_of_plan totalPlan004_keys totalPlan004_ok

end RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
