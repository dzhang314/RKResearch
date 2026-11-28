module

public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Core
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join0
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join1
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join2
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join3
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join4
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join5
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join6
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join7
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join8
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join9
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join10
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join11
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join12
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join13
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join14
public import RKCert.ReviewedNative.ERK10FifteenZ29Pow11Join15

@[expose] public section

namespace RKResearch.Certified.ERK10FifteenZ29Pow11

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin0 : block joinOK ActCount 0 8 = true := by
  change ([tag 0, tag 1, tag 2, tag 3, tag 4, tag 5, tag 6, tag 7].all joinOK) = true
  simp only [List.all_cons,List.all_nil,Bool.and_self,join0,join1,join2,join3,join4,join5,join6,join7]

theorem blockJoin1 : block joinOK ActCount 1 8 = true := by
  change ([tag 8, tag 9, tag 10, tag 11, tag 12, tag 13, tag 14, tag 15].all joinOK) = true
  simp only [List.all_cons,List.all_nil,Bool.and_self,join8,join9,join10,join11,join12,join13,join14,join15]

theorem blockJoin2 : block joinOK ActCount 2 8 = true := by decide +kernel

theorem blockJoin3 : block joinOK ActCount 3 8 = true := by decide +kernel

end RKResearch.Certified.ERK10FifteenZ29Pow11
