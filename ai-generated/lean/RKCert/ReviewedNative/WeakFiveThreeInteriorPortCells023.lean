module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets023

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0552_port_checked : checkPortRow packet0552.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0553_port_checked : checkPortRow packet0553.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0554_port_checked : checkPortRow packet0554.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0555_port_checked : checkPortRow packet0555.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0556_port_checked : checkPortRow packet0556.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0557_port_checked : checkPortRow packet0557.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0558_port_checked : checkPortRow packet0558.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0559_port_checked : checkPortRow packet0559.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0560_port_checked : checkPortRow packet0560.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0561_port_checked : checkPortRow packet0561.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0562_port_checked : checkPortRow packet0562.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0563_port_checked : checkPortRow packet0563.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0564_port_checked : checkPortRow packet0564.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0565_port_checked : checkPortRow packet0565.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0566_port_checked : checkPortRow packet0566.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0567_port_checked : checkPortRow packet0567.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0568_port_checked : checkPortRow packet0568.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0569_port_checked : checkPortRow packet0569.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0570_port_checked : checkPortRow packet0570.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0571_port_checked : checkPortRow packet0571.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0572_port_checked : checkPortRow packet0572.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0573_port_checked : checkPortRow packet0573.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0574_port_checked : checkPortRow packet0574.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0575_port_checked : checkPortRow packet0575.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets023_ports_checked :
    packets023.all (fun q => checkPortRow q.row) = true := by
  simp only [packets023,List.all_cons,List.all_nil,Bool.true_and,
    packet0552_port_checked, packet0553_port_checked, packet0554_port_checked, packet0555_port_checked,
    packet0556_port_checked, packet0557_port_checked, packet0558_port_checked, packet0559_port_checked,
    packet0560_port_checked, packet0561_port_checked, packet0562_port_checked, packet0563_port_checked,
    packet0564_port_checked, packet0565_port_checked, packet0566_port_checked, packet0567_port_checked,
    packet0568_port_checked, packet0569_port_checked, packet0570_port_checked, packet0571_port_checked,
    packet0572_port_checked, packet0573_port_checked, packet0574_port_checked, packet0575_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
