module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets024

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0576_port_checked : checkPortRow packet0576.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0577_port_checked : checkPortRow packet0577.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0578_port_checked : checkPortRow packet0578.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0579_port_checked : checkPortRow packet0579.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0580_port_checked : checkPortRow packet0580.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0581_port_checked : checkPortRow packet0581.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0582_port_checked : checkPortRow packet0582.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0583_port_checked : checkPortRow packet0583.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0584_port_checked : checkPortRow packet0584.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0585_port_checked : checkPortRow packet0585.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0586_port_checked : checkPortRow packet0586.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0587_port_checked : checkPortRow packet0587.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0588_port_checked : checkPortRow packet0588.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0589_port_checked : checkPortRow packet0589.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0590_port_checked : checkPortRow packet0590.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0591_port_checked : checkPortRow packet0591.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0592_port_checked : checkPortRow packet0592.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0593_port_checked : checkPortRow packet0593.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0594_port_checked : checkPortRow packet0594.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0595_port_checked : checkPortRow packet0595.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0596_port_checked : checkPortRow packet0596.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0597_port_checked : checkPortRow packet0597.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0598_port_checked : checkPortRow packet0598.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0599_port_checked : checkPortRow packet0599.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets024_ports_checked :
    packets024.all (fun q => checkPortRow q.row) = true := by
  simp only [packets024,List.all_cons,List.all_nil,Bool.true_and,
    packet0576_port_checked, packet0577_port_checked, packet0578_port_checked, packet0579_port_checked,
    packet0580_port_checked, packet0581_port_checked, packet0582_port_checked, packet0583_port_checked,
    packet0584_port_checked, packet0585_port_checked, packet0586_port_checked, packet0587_port_checked,
    packet0588_port_checked, packet0589_port_checked, packet0590_port_checked, packet0591_port_checked,
    packet0592_port_checked, packet0593_port_checked, packet0594_port_checked, packet0595_port_checked,
    packet0596_port_checked, packet0597_port_checked, packet0598_port_checked, packet0599_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
