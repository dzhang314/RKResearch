module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets044

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1056_port_checked : checkPortRow packet1056.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1057_port_checked : checkPortRow packet1057.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1058_port_checked : checkPortRow packet1058.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1059_port_checked : checkPortRow packet1059.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1060_port_checked : checkPortRow packet1060.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1061_port_checked : checkPortRow packet1061.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1062_port_checked : checkPortRow packet1062.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1063_port_checked : checkPortRow packet1063.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1064_port_checked : checkPortRow packet1064.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1065_port_checked : checkPortRow packet1065.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1066_port_checked : checkPortRow packet1066.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1067_port_checked : checkPortRow packet1067.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1068_port_checked : checkPortRow packet1068.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1069_port_checked : checkPortRow packet1069.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1070_port_checked : checkPortRow packet1070.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1071_port_checked : checkPortRow packet1071.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1072_port_checked : checkPortRow packet1072.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1073_port_checked : checkPortRow packet1073.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1074_port_checked : checkPortRow packet1074.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1075_port_checked : checkPortRow packet1075.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1076_port_checked : checkPortRow packet1076.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1077_port_checked : checkPortRow packet1077.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1078_port_checked : checkPortRow packet1078.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1079_port_checked : checkPortRow packet1079.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets044_ports_checked :
    packets044.all (fun q => checkPortRow q.row) = true := by
  simp only [packets044,List.all_cons,List.all_nil,Bool.true_and,
    packet1056_port_checked, packet1057_port_checked, packet1058_port_checked, packet1059_port_checked,
    packet1060_port_checked, packet1061_port_checked, packet1062_port_checked, packet1063_port_checked,
    packet1064_port_checked, packet1065_port_checked, packet1066_port_checked, packet1067_port_checked,
    packet1068_port_checked, packet1069_port_checked, packet1070_port_checked, packet1071_port_checked,
    packet1072_port_checked, packet1073_port_checked, packet1074_port_checked, packet1075_port_checked,
    packet1076_port_checked, packet1077_port_checked, packet1078_port_checked, packet1079_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
