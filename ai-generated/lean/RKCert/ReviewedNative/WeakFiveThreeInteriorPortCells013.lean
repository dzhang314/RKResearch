module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets013

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0312_port_checked : checkPortRow packet0312.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0313_port_checked : checkPortRow packet0313.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0314_port_checked : checkPortRow packet0314.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0315_port_checked : checkPortRow packet0315.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0316_port_checked : checkPortRow packet0316.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0317_port_checked : checkPortRow packet0317.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0318_port_checked : checkPortRow packet0318.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0319_port_checked : checkPortRow packet0319.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0320_port_checked : checkPortRow packet0320.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0321_port_checked : checkPortRow packet0321.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0322_port_checked : checkPortRow packet0322.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0323_port_checked : checkPortRow packet0323.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0324_port_checked : checkPortRow packet0324.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0325_port_checked : checkPortRow packet0325.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0326_port_checked : checkPortRow packet0326.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0327_port_checked : checkPortRow packet0327.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0328_port_checked : checkPortRow packet0328.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0329_port_checked : checkPortRow packet0329.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0330_port_checked : checkPortRow packet0330.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0331_port_checked : checkPortRow packet0331.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0332_port_checked : checkPortRow packet0332.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0333_port_checked : checkPortRow packet0333.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0334_port_checked : checkPortRow packet0334.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0335_port_checked : checkPortRow packet0335.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets013_ports_checked :
    packets013.all (fun q => checkPortRow q.row) = true := by
  simp only [packets013,List.all_cons,List.all_nil,Bool.true_and,
    packet0312_port_checked, packet0313_port_checked, packet0314_port_checked, packet0315_port_checked,
    packet0316_port_checked, packet0317_port_checked, packet0318_port_checked, packet0319_port_checked,
    packet0320_port_checked, packet0321_port_checked, packet0322_port_checked, packet0323_port_checked,
    packet0324_port_checked, packet0325_port_checked, packet0326_port_checked, packet0327_port_checked,
    packet0328_port_checked, packet0329_port_checked, packet0330_port_checked, packet0331_port_checked,
    packet0332_port_checked, packet0333_port_checked, packet0334_port_checked, packet0335_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
