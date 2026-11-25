module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets043

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1032_port_checked : checkPortRow packet1032.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1033_port_checked : checkPortRow packet1033.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1034_port_checked : checkPortRow packet1034.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1035_port_checked : checkPortRow packet1035.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1036_port_checked : checkPortRow packet1036.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1037_port_checked : checkPortRow packet1037.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1038_port_checked : checkPortRow packet1038.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1039_port_checked : checkPortRow packet1039.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1040_port_checked : checkPortRow packet1040.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1041_port_checked : checkPortRow packet1041.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1042_port_checked : checkPortRow packet1042.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1043_port_checked : checkPortRow packet1043.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1044_port_checked : checkPortRow packet1044.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1045_port_checked : checkPortRow packet1045.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1046_port_checked : checkPortRow packet1046.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1047_port_checked : checkPortRow packet1047.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1048_port_checked : checkPortRow packet1048.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1049_port_checked : checkPortRow packet1049.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1050_port_checked : checkPortRow packet1050.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1051_port_checked : checkPortRow packet1051.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1052_port_checked : checkPortRow packet1052.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1053_port_checked : checkPortRow packet1053.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1054_port_checked : checkPortRow packet1054.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1055_port_checked : checkPortRow packet1055.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets043_ports_checked :
    packets043.all (fun q => checkPortRow q.row) = true := by
  simp only [packets043,List.all_cons,List.all_nil,Bool.true_and,
    packet1032_port_checked, packet1033_port_checked, packet1034_port_checked, packet1035_port_checked,
    packet1036_port_checked, packet1037_port_checked, packet1038_port_checked, packet1039_port_checked,
    packet1040_port_checked, packet1041_port_checked, packet1042_port_checked, packet1043_port_checked,
    packet1044_port_checked, packet1045_port_checked, packet1046_port_checked, packet1047_port_checked,
    packet1048_port_checked, packet1049_port_checked, packet1050_port_checked, packet1051_port_checked,
    packet1052_port_checked, packet1053_port_checked, packet1054_port_checked, packet1055_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
