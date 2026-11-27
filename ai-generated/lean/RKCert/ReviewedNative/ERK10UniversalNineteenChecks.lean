module

public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckGrade0
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin0
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction0
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay0
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckGrade4
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin2
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction3
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay4
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckGrade8
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin4
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction6
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay8
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin6
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction9
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay12
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin8
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction12
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay16
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin10
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction15
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay20
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin12
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction18
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay24
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin14
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction21
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay28
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin16
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction24
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay32
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin18
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction27
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckPay36
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin20
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction30
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin22
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction33
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin24
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction36
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin26
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction39
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin28
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction42
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin30
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction45
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin32
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction48
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin34
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction51
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin36
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction54
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin38
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction57
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin40
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction60
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin42
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction63
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin44
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckAction66
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin46
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin48
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin50
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin52
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin54
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin56
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin58
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin60
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin62
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin64
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin66
public import RKCert.ReviewedNative.ERK10UniversalNineteenCheckJoin68
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Generated exact certificate; see the literal tableau and generator. -/

namespace RKResearch.Certified.ERK10UniversalNineteen

set_option maxHeartbeats 0
set_option maxRecDepth 50000

theorem allGrade (i : ℕ) (hi : i < 10) :
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
  · exact checkGrade8
  · exact checkGrade9

theorem allJoin (i : ℕ) (hi : i < 69) :
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
  · exact checkJoin56
  · exact checkJoin57
  · exact checkJoin58
  · exact checkJoin59
  · exact checkJoin60
  · exact checkJoin61
  · exact checkJoin62
  · exact checkJoin63
  · exact checkJoin64
  · exact checkJoin65
  · exact checkJoin66
  · exact checkJoin67
  · exact checkJoin68

theorem allAction (i : ℕ) (hi : i < 69) :
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
  · exact checkAction56
  · exact checkAction57
  · exact checkAction58
  · exact checkAction59
  · exact checkAction60
  · exact checkAction61
  · exact checkAction62
  · exact checkAction63
  · exact checkAction64
  · exact checkAction65
  · exact checkAction66
  · exact checkAction67
  · exact checkAction68

theorem allPay (i : ℕ) (hi : i < 37) :
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
  · exact checkPay31
  · exact checkPay32
  · exact checkPay33
  · exact checkPay34
  · exact checkPay35
  · exact checkPay36


theorem receipts : Receipts where
  grade i := checkBlock_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := checkBlock_covers (by decide) (by decide) allJoin i hi
  act i hi := checkBlock_covers (by decide) (by decide) allAction i hi
  pay i := checkBlock_covers (by decide) (by decide) allPay i i.isLt


end RKResearch.Certified.ERK10UniversalNineteen
