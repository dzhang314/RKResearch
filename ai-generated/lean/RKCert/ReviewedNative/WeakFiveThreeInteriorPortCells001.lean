module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets001

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0024_port_checked : checkPortRow packet0024.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0025_port_checked : checkPortRow packet0025.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0026_port_checked : checkPortRow packet0026.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0027_port_checked : checkPortRow packet0027.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0028_port_checked : checkPortRow packet0028.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0029_port_checked : checkPortRow packet0029.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0030_port_checked : checkPortRow packet0030.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0031_port_checked : checkPortRow packet0031.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0032_port_checked : checkPortRow packet0032.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0033_port_checked : checkPortRow packet0033.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0034_port_checked : checkPortRow packet0034.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0035_port_checked : checkPortRow packet0035.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0036_port_checked : checkPortRow packet0036.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0037_port_checked : checkPortRow packet0037.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0038_port_checked : checkPortRow packet0038.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0039_port_checked : checkPortRow packet0039.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0040_port_checked : checkPortRow packet0040.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0041_port_checked : checkPortRow packet0041.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0042_port_checked : checkPortRow packet0042.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0043_port_checked : checkPortRow packet0043.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0044_port_checked : checkPortRow packet0044.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0045_port_checked : checkPortRow packet0045.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0046_port_checked : checkPortRow packet0046.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0047_port_checked : checkPortRow packet0047.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets001_ports_checked :
    packets001.all (fun q => checkPortRow q.row) = true := by
  simp only [packets001,List.all_cons,List.all_nil,Bool.true_and,
    packet0024_port_checked, packet0025_port_checked, packet0026_port_checked, packet0027_port_checked,
    packet0028_port_checked, packet0029_port_checked, packet0030_port_checked, packet0031_port_checked,
    packet0032_port_checked, packet0033_port_checked, packet0034_port_checked, packet0035_port_checked,
    packet0036_port_checked, packet0037_port_checked, packet0038_port_checked, packet0039_port_checked,
    packet0040_port_checked, packet0041_port_checked, packet0042_port_checked, packet0043_port_checked,
    packet0044_port_checked, packet0045_port_checked, packet0046_port_checked, packet0047_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
