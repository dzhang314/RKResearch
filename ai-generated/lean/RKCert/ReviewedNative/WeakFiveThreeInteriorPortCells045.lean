module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets045

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1080_port_checked : checkPortRow packet1080.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1081_port_checked : checkPortRow packet1081.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1082_port_checked : checkPortRow packet1082.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1083_port_checked : checkPortRow packet1083.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1084_port_checked : checkPortRow packet1084.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1085_port_checked : checkPortRow packet1085.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1086_port_checked : checkPortRow packet1086.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1087_port_checked : checkPortRow packet1087.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1088_port_checked : checkPortRow packet1088.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1089_port_checked : checkPortRow packet1089.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1090_port_checked : checkPortRow packet1090.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1091_port_checked : checkPortRow packet1091.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1092_port_checked : checkPortRow packet1092.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1093_port_checked : checkPortRow packet1093.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1094_port_checked : checkPortRow packet1094.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1095_port_checked : checkPortRow packet1095.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1096_port_checked : checkPortRow packet1096.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1097_port_checked : checkPortRow packet1097.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1098_port_checked : checkPortRow packet1098.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1099_port_checked : checkPortRow packet1099.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1100_port_checked : checkPortRow packet1100.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1101_port_checked : checkPortRow packet1101.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1102_port_checked : checkPortRow packet1102.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1103_port_checked : checkPortRow packet1103.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets045_ports_checked :
    packets045.all (fun q => checkPortRow q.row) = true := by
  simp only [packets045,List.all_cons,List.all_nil,Bool.true_and,
    packet1080_port_checked, packet1081_port_checked, packet1082_port_checked, packet1083_port_checked,
    packet1084_port_checked, packet1085_port_checked, packet1086_port_checked, packet1087_port_checked,
    packet1088_port_checked, packet1089_port_checked, packet1090_port_checked, packet1091_port_checked,
    packet1092_port_checked, packet1093_port_checked, packet1094_port_checked, packet1095_port_checked,
    packet1096_port_checked, packet1097_port_checked, packet1098_port_checked, packet1099_port_checked,
    packet1100_port_checked, packet1101_port_checked, packet1102_port_checked, packet1103_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
