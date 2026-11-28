module

public import RKCert.ReviewedNative.ERK10SixteenF13Core
public import RKCert.ReviewedNative.ERK10SixteenF13Join0
public import RKCert.ReviewedNative.ERK10SixteenF13Join1
public import RKCert.ReviewedNative.ERK10SixteenF13Join2
public import RKCert.ReviewedNative.ERK10SixteenF13Join3
public import RKCert.ReviewedNative.ERK10SixteenF13Join4
public import RKCert.ReviewedNative.ERK10SixteenF13Join5
public import RKCert.ReviewedNative.ERK10SixteenF13Join6
public import RKCert.ReviewedNative.ERK10SixteenF13Join7
public import RKCert.ReviewedNative.ERK10SixteenF13Join8
public import RKCert.ReviewedNative.ERK10SixteenF13Join9
public import RKCert.ReviewedNative.ERK10SixteenF13Join10
public import RKCert.ReviewedNative.ERK10SixteenF13Join11
public import RKCert.ReviewedNative.ERK10SixteenF13Join12

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF13

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem blockJoin0 : block joinOK ActCount 0 8 = true := by
  change ([tag 0, tag 1, tag 2, tag 3, tag 4, tag 5, tag 6, tag 7].all joinOK) = true
  simp only [List.all_cons,List.all_nil,Bool.and_self,join0,join1,join2,join3,join4,join5,join6,join7]

theorem blockJoin1 : block joinOK ActCount 1 8 = true := by
  change ([tag 8, tag 9, tag 10, tag 11, tag 12, tag 13, tag 14, tag 15].all joinOK) = true
  have join13 : joinOK (tag 13) = true := by decide +kernel
  have join14 : joinOK (tag 14) = true := by decide +kernel
  have join15 : joinOK (tag 15) = true := by decide +kernel
  simp only [List.all_cons,List.all_nil,Bool.and_self,join8,join9,join10,join11,join12,join13,join14,join15]

theorem blockJoin2 : block joinOK ActCount 2 8 = true := by decide +kernel

theorem blockJoin3 : block joinOK ActCount 3 8 = true := by decide +kernel

end RKResearch.Certified.ERK10SixteenF13
