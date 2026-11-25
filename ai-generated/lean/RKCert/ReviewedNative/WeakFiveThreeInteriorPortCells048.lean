module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets048

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1152_port_checked : checkPortRow packet1152.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1153_port_checked : checkPortRow packet1153.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1154_port_checked : checkPortRow packet1154.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1155_port_checked : checkPortRow packet1155.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1156_port_checked : checkPortRow packet1156.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1157_port_checked : checkPortRow packet1157.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1158_port_checked : checkPortRow packet1158.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1159_port_checked : checkPortRow packet1159.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1160_port_checked : checkPortRow packet1160.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1161_port_checked : checkPortRow packet1161.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1162_port_checked : checkPortRow packet1162.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1163_port_checked : checkPortRow packet1163.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1164_port_checked : checkPortRow packet1164.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1165_port_checked : checkPortRow packet1165.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1166_port_checked : checkPortRow packet1166.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1167_port_checked : checkPortRow packet1167.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1168_port_checked : checkPortRow packet1168.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1169_port_checked : checkPortRow packet1169.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1170_port_checked : checkPortRow packet1170.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1171_port_checked : checkPortRow packet1171.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1172_port_checked : checkPortRow packet1172.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1173_port_checked : checkPortRow packet1173.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1174_port_checked : checkPortRow packet1174.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1175_port_checked : checkPortRow packet1175.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets048_ports_checked :
    packets048.all (fun q => checkPortRow q.row) = true := by
  simp only [packets048,List.all_cons,List.all_nil,Bool.true_and,
    packet1152_port_checked, packet1153_port_checked, packet1154_port_checked, packet1155_port_checked,
    packet1156_port_checked, packet1157_port_checked, packet1158_port_checked, packet1159_port_checked,
    packet1160_port_checked, packet1161_port_checked, packet1162_port_checked, packet1163_port_checked,
    packet1164_port_checked, packet1165_port_checked, packet1166_port_checked, packet1167_port_checked,
    packet1168_port_checked, packet1169_port_checked, packet1170_port_checked, packet1171_port_checked,
    packet1172_port_checked, packet1173_port_checked, packet1174_port_checked, packet1175_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
