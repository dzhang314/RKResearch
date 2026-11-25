module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets012

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0288_port_checked : checkPortRow packet0288.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0289_port_checked : checkPortRow packet0289.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0290_port_checked : checkPortRow packet0290.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0291_port_checked : checkPortRow packet0291.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0292_port_checked : checkPortRow packet0292.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0293_port_checked : checkPortRow packet0293.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0294_port_checked : checkPortRow packet0294.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0295_port_checked : checkPortRow packet0295.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0296_port_checked : checkPortRow packet0296.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0297_port_checked : checkPortRow packet0297.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0298_port_checked : checkPortRow packet0298.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0299_port_checked : checkPortRow packet0299.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0300_port_checked : checkPortRow packet0300.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0301_port_checked : checkPortRow packet0301.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0302_port_checked : checkPortRow packet0302.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0303_port_checked : checkPortRow packet0303.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0304_port_checked : checkPortRow packet0304.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0305_port_checked : checkPortRow packet0305.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0306_port_checked : checkPortRow packet0306.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0307_port_checked : checkPortRow packet0307.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0308_port_checked : checkPortRow packet0308.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0309_port_checked : checkPortRow packet0309.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0310_port_checked : checkPortRow packet0310.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0311_port_checked : checkPortRow packet0311.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets012_ports_checked :
    packets012.all (fun q => checkPortRow q.row) = true := by
  simp only [packets012,List.all_cons,List.all_nil,Bool.true_and,
    packet0288_port_checked, packet0289_port_checked, packet0290_port_checked, packet0291_port_checked,
    packet0292_port_checked, packet0293_port_checked, packet0294_port_checked, packet0295_port_checked,
    packet0296_port_checked, packet0297_port_checked, packet0298_port_checked, packet0299_port_checked,
    packet0300_port_checked, packet0301_port_checked, packet0302_port_checked, packet0303_port_checked,
    packet0304_port_checked, packet0305_port_checked, packet0306_port_checked, packet0307_port_checked,
    packet0308_port_checked, packet0309_port_checked, packet0310_port_checked, packet0311_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
