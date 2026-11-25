module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets050

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet1200_port_checked : checkPortRow packet1200.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1201_port_checked : checkPortRow packet1201.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1202_port_checked : checkPortRow packet1202.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1203_port_checked : checkPortRow packet1203.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1204_port_checked : checkPortRow packet1204.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1205_port_checked : checkPortRow packet1205.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1206_port_checked : checkPortRow packet1206.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1207_port_checked : checkPortRow packet1207.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1208_port_checked : checkPortRow packet1208.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1209_port_checked : checkPortRow packet1209.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1210_port_checked : checkPortRow packet1210.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet1211_port_checked : checkPortRow packet1211.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets050_ports_checked :
    packets050.all (fun q => checkPortRow q.row) = true := by
  simp only [packets050,List.all_cons,List.all_nil,Bool.true_and,
    packet1200_port_checked, packet1201_port_checked, packet1202_port_checked, packet1203_port_checked,
    packet1204_port_checked, packet1205_port_checked, packet1206_port_checked, packet1207_port_checked,
    packet1208_port_checked, packet1209_port_checked, packet1210_port_checked, packet1211_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
