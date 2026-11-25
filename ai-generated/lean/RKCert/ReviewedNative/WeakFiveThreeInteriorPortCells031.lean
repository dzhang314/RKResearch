module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets031

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0744_port_checked : checkPortRow packet0744.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0745_port_checked : checkPortRow packet0745.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0746_port_checked : checkPortRow packet0746.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0747_port_checked : checkPortRow packet0747.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0748_port_checked : checkPortRow packet0748.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0749_port_checked : checkPortRow packet0749.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0750_port_checked : checkPortRow packet0750.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0751_port_checked : checkPortRow packet0751.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0752_port_checked : checkPortRow packet0752.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0753_port_checked : checkPortRow packet0753.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0754_port_checked : checkPortRow packet0754.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0755_port_checked : checkPortRow packet0755.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0756_port_checked : checkPortRow packet0756.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0757_port_checked : checkPortRow packet0757.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0758_port_checked : checkPortRow packet0758.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0759_port_checked : checkPortRow packet0759.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0760_port_checked : checkPortRow packet0760.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0761_port_checked : checkPortRow packet0761.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0762_port_checked : checkPortRow packet0762.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0763_port_checked : checkPortRow packet0763.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0764_port_checked : checkPortRow packet0764.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0765_port_checked : checkPortRow packet0765.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0766_port_checked : checkPortRow packet0766.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0767_port_checked : checkPortRow packet0767.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets031_ports_checked :
    packets031.all (fun q => checkPortRow q.row) = true := by
  simp only [packets031,List.all_cons,List.all_nil,Bool.true_and,
    packet0744_port_checked, packet0745_port_checked, packet0746_port_checked, packet0747_port_checked,
    packet0748_port_checked, packet0749_port_checked, packet0750_port_checked, packet0751_port_checked,
    packet0752_port_checked, packet0753_port_checked, packet0754_port_checked, packet0755_port_checked,
    packet0756_port_checked, packet0757_port_checked, packet0758_port_checked, packet0759_port_checked,
    packet0760_port_checked, packet0761_port_checked, packet0762_port_checked, packet0763_port_checked,
    packet0764_port_checked, packet0765_port_checked, packet0766_port_checked, packet0767_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
