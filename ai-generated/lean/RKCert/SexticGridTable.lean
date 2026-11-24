module
public import RKCert.SexticTable0
public import RKCert.SexticTable1
public import RKCert.SexticTable2
public import RKCert.SexticTable3
public import RKCert.SexticTable4
public import RKCert.SexticTable5
@[expose] public section
namespace RKCert.Sextic
open RKCert.DirkQuintic
set_option maxRecDepth 150000
set_option maxHeartbeats 0
theorem table_checked : (integers10.sublistsLen 5).all checkQuint=true := by
  have part : integers10.sublistsLen 5=pack 0 ++ pack 1 ++ pack 2 ++ pack 3 ++ pack 4 ++ pack 5 ++ pack 6 ++ pack 7 ++ pack 8 ++ pack 9 ++ pack 10 ++ pack 11 ++ pack 12 ++ pack 13 ++ pack 14 ++ pack 15 ++ pack 16 ++ pack 17 ++ pack 18 ++ pack 19 ++ pack 20 ++ pack 21 ++ pack 22 ++ pack 23 ++ pack 24 ++ pack 25 ++ pack 26 ++ pack 27 ++ pack 28 ++ pack 29 ++ pack 30 ++ pack 31 ++ pack 32 ++ pack 33 ++ pack 34 ++ pack 35 ++ pack 36 ++ pack 37 ++ pack 38 ++ pack 39 ++ pack 40 ++ pack 41 := by decide +kernel
  rw [part]
  simp only [List.all_append,checked_0,checked_1,checked_2,checked_3,checked_4,checked_5,checked_6,checked_7,checked_8,checked_9,checked_10,checked_11,checked_12,checked_13,checked_14,checked_15,checked_16,checked_17,checked_18,checked_19,checked_20,checked_21,checked_22,checked_23,checked_24,checked_25,checked_26,checked_27,checked_28,checked_29,checked_30,checked_31,checked_32,checked_33,checked_34,checked_35,checked_36,checked_37,checked_38,checked_39,checked_40,checked_41,Bool.and_self]
end RKCert.Sextic
