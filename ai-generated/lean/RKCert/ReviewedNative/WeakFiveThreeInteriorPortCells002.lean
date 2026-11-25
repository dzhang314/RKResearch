module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets002

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0048_port_checked : checkPortRow packet0048.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0049_port_checked : checkPortRow packet0049.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0050_port_checked : checkPortRow packet0050.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0051_port_checked : checkPortRow packet0051.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0052_port_checked : checkPortRow packet0052.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0053_port_checked : checkPortRow packet0053.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0054_port_checked : checkPortRow packet0054.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0055_port_checked : checkPortRow packet0055.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0056_port_checked : checkPortRow packet0056.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0057_port_checked : checkPortRow packet0057.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0058_port_checked : checkPortRow packet0058.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0059_port_checked : checkPortRow packet0059.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0060_port_checked : checkPortRow packet0060.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0061_port_checked : checkPortRow packet0061.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0062_port_checked : checkPortRow packet0062.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0063_port_checked : checkPortRow packet0063.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0064_port_checked : checkPortRow packet0064.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0065_port_checked : checkPortRow packet0065.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0066_port_checked : checkPortRow packet0066.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0067_port_checked : checkPortRow packet0067.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0068_port_checked : checkPortRow packet0068.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0069_port_checked : checkPortRow packet0069.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0070_port_checked : checkPortRow packet0070.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0071_port_checked : checkPortRow packet0071.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets002_ports_checked :
    packets002.all (fun q => checkPortRow q.row) = true := by
  simp only [packets002,List.all_cons,List.all_nil,Bool.true_and,
    packet0048_port_checked, packet0049_port_checked, packet0050_port_checked, packet0051_port_checked,
    packet0052_port_checked, packet0053_port_checked, packet0054_port_checked, packet0055_port_checked,
    packet0056_port_checked, packet0057_port_checked, packet0058_port_checked, packet0059_port_checked,
    packet0060_port_checked, packet0061_port_checked, packet0062_port_checked, packet0063_port_checked,
    packet0064_port_checked, packet0065_port_checked, packet0066_port_checked, packet0067_port_checked,
    packet0068_port_checked, packet0069_port_checked, packet0070_port_checked, packet0071_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
