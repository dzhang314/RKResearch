module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets005

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0120_port_checked : checkPortRow packet0120.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0121_port_checked : checkPortRow packet0121.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0122_port_checked : checkPortRow packet0122.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0123_port_checked : checkPortRow packet0123.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0124_port_checked : checkPortRow packet0124.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0125_port_checked : checkPortRow packet0125.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0126_port_checked : checkPortRow packet0126.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0127_port_checked : checkPortRow packet0127.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0128_port_checked : checkPortRow packet0128.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0129_port_checked : checkPortRow packet0129.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0130_port_checked : checkPortRow packet0130.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0131_port_checked : checkPortRow packet0131.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0132_port_checked : checkPortRow packet0132.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0133_port_checked : checkPortRow packet0133.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0134_port_checked : checkPortRow packet0134.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0135_port_checked : checkPortRow packet0135.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0136_port_checked : checkPortRow packet0136.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0137_port_checked : checkPortRow packet0137.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0138_port_checked : checkPortRow packet0138.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0139_port_checked : checkPortRow packet0139.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0140_port_checked : checkPortRow packet0140.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0141_port_checked : checkPortRow packet0141.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0142_port_checked : checkPortRow packet0142.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0143_port_checked : checkPortRow packet0143.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets005_ports_checked :
    packets005.all (fun q => checkPortRow q.row) = true := by
  simp only [packets005,List.all_cons,List.all_nil,Bool.true_and,
    packet0120_port_checked, packet0121_port_checked, packet0122_port_checked, packet0123_port_checked,
    packet0124_port_checked, packet0125_port_checked, packet0126_port_checked, packet0127_port_checked,
    packet0128_port_checked, packet0129_port_checked, packet0130_port_checked, packet0131_port_checked,
    packet0132_port_checked, packet0133_port_checked, packet0134_port_checked, packet0135_port_checked,
    packet0136_port_checked, packet0137_port_checked, packet0138_port_checked, packet0139_port_checked,
    packet0140_port_checked, packet0141_port_checked, packet0142_port_checked, packet0143_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
