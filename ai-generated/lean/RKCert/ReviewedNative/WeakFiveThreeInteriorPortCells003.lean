module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets003

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0072_port_checked : checkPortRow packet0072.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0073_port_checked : checkPortRow packet0073.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0074_port_checked : checkPortRow packet0074.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0075_port_checked : checkPortRow packet0075.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0076_port_checked : checkPortRow packet0076.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0077_port_checked : checkPortRow packet0077.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0078_port_checked : checkPortRow packet0078.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0079_port_checked : checkPortRow packet0079.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0080_port_checked : checkPortRow packet0080.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0081_port_checked : checkPortRow packet0081.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0082_port_checked : checkPortRow packet0082.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0083_port_checked : checkPortRow packet0083.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0084_port_checked : checkPortRow packet0084.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0085_port_checked : checkPortRow packet0085.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0086_port_checked : checkPortRow packet0086.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0087_port_checked : checkPortRow packet0087.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0088_port_checked : checkPortRow packet0088.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0089_port_checked : checkPortRow packet0089.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0090_port_checked : checkPortRow packet0090.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0091_port_checked : checkPortRow packet0091.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0092_port_checked : checkPortRow packet0092.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0093_port_checked : checkPortRow packet0093.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0094_port_checked : checkPortRow packet0094.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0095_port_checked : checkPortRow packet0095.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets003_ports_checked :
    packets003.all (fun q => checkPortRow q.row) = true := by
  simp only [packets003,List.all_cons,List.all_nil,Bool.true_and,
    packet0072_port_checked, packet0073_port_checked, packet0074_port_checked, packet0075_port_checked,
    packet0076_port_checked, packet0077_port_checked, packet0078_port_checked, packet0079_port_checked,
    packet0080_port_checked, packet0081_port_checked, packet0082_port_checked, packet0083_port_checked,
    packet0084_port_checked, packet0085_port_checked, packet0086_port_checked, packet0087_port_checked,
    packet0088_port_checked, packet0089_port_checked, packet0090_port_checked, packet0091_port_checked,
    packet0092_port_checked, packet0093_port_checked, packet0094_port_checked, packet0095_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
