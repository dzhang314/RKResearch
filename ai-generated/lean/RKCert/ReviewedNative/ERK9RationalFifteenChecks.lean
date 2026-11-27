module

public import RKCert.ReviewedNative.ERK9RationalFifteenCheckGrade0
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckJoin0
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckAction0
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay0
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckGrade4
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckJoin4
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckAction4
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay4
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckJoin8
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckAction8
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay8
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckJoin12
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckAction12
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay12
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckJoin16
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckAction16
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay16
public import RKCert.ReviewedNative.ERK9RationalFifteenCheckPay20
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK9RationalFifteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem allGrade (i : ℕ) (hi : i < 6) :
    checkBlock gradeOK Count i 64 = true := by
  interval_cases i
  · exact checkGrade0
  · exact checkGrade1
  · exact checkGrade2
  · exact checkGrade3
  · exact checkGrade4
  · exact checkGrade5

theorem allJoin (i : ℕ) (hi : i < 19) :
    checkBlock joinOK ActCount i 8 = true := by
  interval_cases i
  · exact checkJoin0
  · exact checkJoin1
  · exact checkJoin2
  · exact checkJoin3
  · exact checkJoin4
  · exact checkJoin5
  · exact checkJoin6
  · exact checkJoin7
  · exact checkJoin8
  · exact checkJoin9
  · exact checkJoin10
  · exact checkJoin11
  · exact checkJoin12
  · exact checkJoin13
  · exact checkJoin14
  · exact checkJoin15
  · exact checkJoin16
  · exact checkJoin17
  · exact checkJoin18

theorem allAction (i : ℕ) (hi : i < 19) :
    checkBlock actOK ActCount i 8 = true := by
  interval_cases i
  · exact checkAction0
  · exact checkAction1
  · exact checkAction2
  · exact checkAction3
  · exact checkAction4
  · exact checkAction5
  · exact checkAction6
  · exact checkAction7
  · exact checkAction8
  · exact checkAction9
  · exact checkAction10
  · exact checkAction11
  · exact checkAction12
  · exact checkAction13
  · exact checkAction14
  · exact checkAction15
  · exact checkAction16
  · exact checkAction17
  · exact checkAction18

theorem allPay (i : ℕ) (hi : i < 21) :
    checkBlock payOK Count i 16 = true := by
  interval_cases i
  · exact checkPay0
  · exact checkPay1
  · exact checkPay2
  · exact checkPay3
  · exact checkPay4
  · exact checkPay5
  · exact checkPay6
  · exact checkPay7
  · exact checkPay8
  · exact checkPay9
  · exact checkPay10
  · exact checkPay11
  · exact checkPay12
  · exact checkPay13
  · exact checkPay14
  · exact checkPay15
  · exact checkPay16
  · exact checkPay17
  · exact checkPay18
  · exact checkPay19
  · exact checkPay20


theorem receipts : Receipts where
  grade i := checkBlock_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := checkBlock_covers (by decide) (by decide) allJoin i hi
  act i hi := checkBlock_covers (by decide) (by decide) allAction i hi
  pay i := checkBlock_covers (by decide) (by decide) allPay i i.isLt


end RKResearch.Certified.ERK9RationalFifteen
