module

public import RKCert.ReviewedNative.ERK10SixteenF17ChecksGrade0
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksGrade4
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin0
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin4
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin8
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin12
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin16
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin20
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksJoin24
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct0
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct3
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct6
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct9
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct12
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct15
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct18
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksAct21
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay0
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay4
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay8
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay12
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay16
public import RKCert.ReviewedNative.ERK10SixteenF17ChecksPay20
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.ERK10SixteenF17

set_option maxHeartbeats 0
set_option maxRecDepth 40000

theorem allGrade (i : ℕ) (hi : i<8) : block gradeOK Count i 64=true := by
  interval_cases i
  · exact blockGrade0
  · exact blockGrade1
  · exact blockGrade2
  · exact blockGrade3
  · exact blockGrade4
  · exact blockGrade5
  · exact blockGrade6
  · exact blockGrade7

theorem allJoin (i : ℕ) (hi : i<28) : block joinOK ActCount i 8=true := by
  interval_cases i
  · exact blockJoin0
  · exact blockJoin1
  · exact blockJoin2
  · exact blockJoin3
  · exact blockJoin4
  · exact blockJoin5
  · exact blockJoin6
  · exact blockJoin7
  · exact blockJoin8
  · exact blockJoin9
  · exact blockJoin10
  · exact blockJoin11
  · exact blockJoin12
  · exact blockJoin13
  · exact blockJoin14
  · exact blockJoin15
  · exact blockJoin16
  · exact blockJoin17
  · exact blockJoin18
  · exact blockJoin19
  · exact blockJoin20
  · exact blockJoin21
  · exact blockJoin22
  · exact blockJoin23
  · exact blockJoin24
  · exact blockJoin25
  · exact blockJoin26
  · exact blockJoin27

theorem allAct (i : ℕ) (hi : i<23) : block actOK ActCount i 10=true := by
  interval_cases i
  · exact blockAct0
  · exact blockAct1
  · exact blockAct2
  · exact blockAct3
  · exact blockAct4
  · exact blockAct5
  · exact blockAct6
  · exact blockAct7
  · exact blockAct8
  · exact blockAct9
  · exact blockAct10
  · exact blockAct11
  · exact blockAct12
  · exact blockAct13
  · exact blockAct14
  · exact blockAct15
  · exact blockAct16
  · exact blockAct17
  · exact blockAct18
  · exact blockAct19
  · exact blockAct20
  · exact blockAct21
  · exact blockAct22

theorem allPay (i : ℕ) (hi : i<21) : block payOK Count i 24=true := by
  interval_cases i
  · exact blockPay0
  · exact blockPay1
  · exact blockPay2
  · exact blockPay3
  · exact blockPay4
  · exact blockPay5
  · exact blockPay6
  · exact blockPay7
  · exact blockPay8
  · exact blockPay9
  · exact blockPay10
  · exact blockPay11
  · exact blockPay12
  · exact blockPay13
  · exact blockPay14
  · exact blockPay15
  · exact blockPay16
  · exact blockPay17
  · exact blockPay18
  · exact blockPay19
  · exact blockPay20

theorem receipts : Receipts where
  grade i := block_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := block_covers (by decide) (by decide) allJoin i hi
  act i hi := block_covers (by decide) (by decide) allAct i hi
  pay i := block_covers (by decide) (by decide) allPay i i.isLt

end RKResearch.Certified.ERK10SixteenF17
