module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets034

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0816_port_checked : checkPortRow packet0816.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0817_port_checked : checkPortRow packet0817.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0818_port_checked : checkPortRow packet0818.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0819_port_checked : checkPortRow packet0819.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0820_port_checked : checkPortRow packet0820.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0821_port_checked : checkPortRow packet0821.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0822_port_checked : checkPortRow packet0822.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0823_port_checked : checkPortRow packet0823.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0824_port_checked : checkPortRow packet0824.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0825_port_checked : checkPortRow packet0825.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0826_port_checked : checkPortRow packet0826.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0827_port_checked : checkPortRow packet0827.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0828_port_checked : checkPortRow packet0828.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0829_port_checked : checkPortRow packet0829.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0830_port_checked : checkPortRow packet0830.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0831_port_checked : checkPortRow packet0831.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0832_port_checked : checkPortRow packet0832.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0833_port_checked : checkPortRow packet0833.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0834_port_checked : checkPortRow packet0834.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0835_port_checked : checkPortRow packet0835.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0836_port_checked : checkPortRow packet0836.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0837_port_checked : checkPortRow packet0837.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0838_port_checked : checkPortRow packet0838.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0839_port_checked : checkPortRow packet0839.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets034_ports_checked :
    packets034.all (fun q => checkPortRow q.row) = true := by
  simp only [packets034,List.all_cons,List.all_nil,Bool.true_and,
    packet0816_port_checked, packet0817_port_checked, packet0818_port_checked, packet0819_port_checked,
    packet0820_port_checked, packet0821_port_checked, packet0822_port_checked, packet0823_port_checked,
    packet0824_port_checked, packet0825_port_checked, packet0826_port_checked, packet0827_port_checked,
    packet0828_port_checked, packet0829_port_checked, packet0830_port_checked, packet0831_port_checked,
    packet0832_port_checked, packet0833_port_checked, packet0834_port_checked, packet0835_port_checked,
    packet0836_port_checked, packet0837_port_checked, packet0838_port_checked, packet0839_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
