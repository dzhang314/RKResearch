module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets020

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0480_port_checked : checkPortRow packet0480.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0481_port_checked : checkPortRow packet0481.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0482_port_checked : checkPortRow packet0482.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0483_port_checked : checkPortRow packet0483.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0484_port_checked : checkPortRow packet0484.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0485_port_checked : checkPortRow packet0485.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0486_port_checked : checkPortRow packet0486.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0487_port_checked : checkPortRow packet0487.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0488_port_checked : checkPortRow packet0488.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0489_port_checked : checkPortRow packet0489.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0490_port_checked : checkPortRow packet0490.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0491_port_checked : checkPortRow packet0491.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0492_port_checked : checkPortRow packet0492.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0493_port_checked : checkPortRow packet0493.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0494_port_checked : checkPortRow packet0494.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0495_port_checked : checkPortRow packet0495.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0496_port_checked : checkPortRow packet0496.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0497_port_checked : checkPortRow packet0497.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0498_port_checked : checkPortRow packet0498.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0499_port_checked : checkPortRow packet0499.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0500_port_checked : checkPortRow packet0500.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0501_port_checked : checkPortRow packet0501.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0502_port_checked : checkPortRow packet0502.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0503_port_checked : checkPortRow packet0503.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets020_ports_checked :
    packets020.all (fun q => checkPortRow q.row) = true := by
  simp only [packets020,List.all_cons,List.all_nil,Bool.true_and,
    packet0480_port_checked, packet0481_port_checked, packet0482_port_checked, packet0483_port_checked,
    packet0484_port_checked, packet0485_port_checked, packet0486_port_checked, packet0487_port_checked,
    packet0488_port_checked, packet0489_port_checked, packet0490_port_checked, packet0491_port_checked,
    packet0492_port_checked, packet0493_port_checked, packet0494_port_checked, packet0495_port_checked,
    packet0496_port_checked, packet0497_port_checked, packet0498_port_checked, packet0499_port_checked,
    packet0500_port_checked, packet0501_port_checked, packet0502_port_checked, packet0503_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
