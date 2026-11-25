module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets004

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0096_port_checked : checkPortRow packet0096.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0097_port_checked : checkPortRow packet0097.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0098_port_checked : checkPortRow packet0098.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0099_port_checked : checkPortRow packet0099.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0100_port_checked : checkPortRow packet0100.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0101_port_checked : checkPortRow packet0101.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0102_port_checked : checkPortRow packet0102.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0103_port_checked : checkPortRow packet0103.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0104_port_checked : checkPortRow packet0104.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0105_port_checked : checkPortRow packet0105.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0106_port_checked : checkPortRow packet0106.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0107_port_checked : checkPortRow packet0107.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0108_port_checked : checkPortRow packet0108.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0109_port_checked : checkPortRow packet0109.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0110_port_checked : checkPortRow packet0110.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0111_port_checked : checkPortRow packet0111.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0112_port_checked : checkPortRow packet0112.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0113_port_checked : checkPortRow packet0113.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0114_port_checked : checkPortRow packet0114.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0115_port_checked : checkPortRow packet0115.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0116_port_checked : checkPortRow packet0116.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0117_port_checked : checkPortRow packet0117.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0118_port_checked : checkPortRow packet0118.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0119_port_checked : checkPortRow packet0119.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets004_ports_checked :
    packets004.all (fun q => checkPortRow q.row) = true := by
  simp only [packets004,List.all_cons,List.all_nil,Bool.true_and,
    packet0096_port_checked, packet0097_port_checked, packet0098_port_checked, packet0099_port_checked,
    packet0100_port_checked, packet0101_port_checked, packet0102_port_checked, packet0103_port_checked,
    packet0104_port_checked, packet0105_port_checked, packet0106_port_checked, packet0107_port_checked,
    packet0108_port_checked, packet0109_port_checked, packet0110_port_checked, packet0111_port_checked,
    packet0112_port_checked, packet0113_port_checked, packet0114_port_checked, packet0115_port_checked,
    packet0116_port_checked, packet0117_port_checked, packet0118_port_checked, packet0119_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
