module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets025

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0600_port_checked : checkPortRow packet0600.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0601_port_checked : checkPortRow packet0601.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0602_port_checked : checkPortRow packet0602.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0603_port_checked : checkPortRow packet0603.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0604_port_checked : checkPortRow packet0604.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0605_port_checked : checkPortRow packet0605.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0606_port_checked : checkPortRow packet0606.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0607_port_checked : checkPortRow packet0607.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0608_port_checked : checkPortRow packet0608.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0609_port_checked : checkPortRow packet0609.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0610_port_checked : checkPortRow packet0610.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0611_port_checked : checkPortRow packet0611.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0612_port_checked : checkPortRow packet0612.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0613_port_checked : checkPortRow packet0613.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0614_port_checked : checkPortRow packet0614.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0615_port_checked : checkPortRow packet0615.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0616_port_checked : checkPortRow packet0616.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0617_port_checked : checkPortRow packet0617.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0618_port_checked : checkPortRow packet0618.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0619_port_checked : checkPortRow packet0619.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0620_port_checked : checkPortRow packet0620.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0621_port_checked : checkPortRow packet0621.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0622_port_checked : checkPortRow packet0622.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0623_port_checked : checkPortRow packet0623.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets025_ports_checked :
    packets025.all (fun q => checkPortRow q.row) = true := by
  simp only [packets025,List.all_cons,List.all_nil,Bool.true_and,
    packet0600_port_checked, packet0601_port_checked, packet0602_port_checked, packet0603_port_checked,
    packet0604_port_checked, packet0605_port_checked, packet0606_port_checked, packet0607_port_checked,
    packet0608_port_checked, packet0609_port_checked, packet0610_port_checked, packet0611_port_checked,
    packet0612_port_checked, packet0613_port_checked, packet0614_port_checked, packet0615_port_checked,
    packet0616_port_checked, packet0617_port_checked, packet0618_port_checked, packet0619_port_checked,
    packet0620_port_checked, packet0621_port_checked, packet0622_port_checked, packet0623_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
