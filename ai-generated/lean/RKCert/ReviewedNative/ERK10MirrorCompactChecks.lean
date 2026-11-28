module

public import RKCert.ReviewedNative.ERK10MirrorCompactCheckGrade0
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin0
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction0
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay0
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckGrade4
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin2
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction3
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay4
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin4
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction6
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay8
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin6
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction9
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay12
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin8
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction12
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay16
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin10
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction15
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay20
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin12
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction18
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay24
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin14
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction21
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckPay28
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin16
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction24
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin18
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction27
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin20
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction30
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin22
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction33
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin24
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction36
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin26
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction39
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin28
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction42
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin30
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction45
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin32
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction48
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin34
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction51
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin36
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckAction54
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin38
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin40
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin42
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin44
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin46
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin48
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin50
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin52
public import RKCert.ReviewedNative.ERK10MirrorCompactCheckJoin54
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10MirrorCompact

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem allGrade (i : ℕ) (hi : i < 8) :
    checkBlock gradeOK Count i 64 = true := by
  interval_cases i
  · exact checkGrade0
  · exact checkGrade1
  · exact checkGrade2
  · exact checkGrade3
  · exact checkGrade4
  · exact checkGrade5
  · exact checkGrade6
  · exact checkGrade7

theorem allJoin (i : ℕ) (hi : i < 56) :
    checkBlock joinOK ActCount i 4 = true := by
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
  · exact checkJoin19
  · exact checkJoin20
  · exact checkJoin21
  · exact checkJoin22
  · exact checkJoin23
  · exact checkJoin24
  · exact checkJoin25
  · exact checkJoin26
  · exact checkJoin27
  · exact checkJoin28
  · exact checkJoin29
  · exact checkJoin30
  · exact checkJoin31
  · exact checkJoin32
  · exact checkJoin33
  · exact checkJoin34
  · exact checkJoin35
  · exact checkJoin36
  · exact checkJoin37
  · exact checkJoin38
  · exact checkJoin39
  · exact checkJoin40
  · exact checkJoin41
  · exact checkJoin42
  · exact checkJoin43
  · exact checkJoin44
  · exact checkJoin45
  · exact checkJoin46
  · exact checkJoin47
  · exact checkJoin48
  · exact checkJoin49
  · exact checkJoin50
  · exact checkJoin51
  · exact checkJoin52
  · exact checkJoin53
  · exact checkJoin54
  · exact checkJoin55

theorem allAction (i : ℕ) (hi : i < 56) :
    checkBlock actOK ActCount i 4 = true := by
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
  · exact checkAction19
  · exact checkAction20
  · exact checkAction21
  · exact checkAction22
  · exact checkAction23
  · exact checkAction24
  · exact checkAction25
  · exact checkAction26
  · exact checkAction27
  · exact checkAction28
  · exact checkAction29
  · exact checkAction30
  · exact checkAction31
  · exact checkAction32
  · exact checkAction33
  · exact checkAction34
  · exact checkAction35
  · exact checkAction36
  · exact checkAction37
  · exact checkAction38
  · exact checkAction39
  · exact checkAction40
  · exact checkAction41
  · exact checkAction42
  · exact checkAction43
  · exact checkAction44
  · exact checkAction45
  · exact checkAction46
  · exact checkAction47
  · exact checkAction48
  · exact checkAction49
  · exact checkAction50
  · exact checkAction51
  · exact checkAction52
  · exact checkAction53
  · exact checkAction54
  · exact checkAction55

theorem allPay (i : ℕ) (hi : i < 31) :
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
  · exact checkPay21
  · exact checkPay22
  · exact checkPay23
  · exact checkPay24
  · exact checkPay25
  · exact checkPay26
  · exact checkPay27
  · exact checkPay28
  · exact checkPay29
  · exact checkPay30


theorem receipts : Receipts where
  grade i := checkBlock_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := checkBlock_covers (by decide) (by decide) allJoin i hi
  act i hi := checkBlock_covers (by decide) (by decide) allAction i hi
  pay i := checkBlock_covers (by decide) (by decide) allPay i i.isLt


end RKResearch.Certified.ERK10MirrorCompact
