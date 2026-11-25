module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets014

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0336_port_checked : checkPortRow packet0336.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0337_port_checked : checkPortRow packet0337.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0338_port_checked : checkPortRow packet0338.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0339_port_checked : checkPortRow packet0339.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0340_port_checked : checkPortRow packet0340.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0341_port_checked : checkPortRow packet0341.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0342_port_checked : checkPortRow packet0342.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0343_port_checked : checkPortRow packet0343.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0344_port_checked : checkPortRow packet0344.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0345_port_checked : checkPortRow packet0345.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0346_port_checked : checkPortRow packet0346.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0347_port_checked : checkPortRow packet0347.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0348_port_checked : checkPortRow packet0348.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0349_port_checked : checkPortRow packet0349.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0350_port_checked : checkPortRow packet0350.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0351_port_checked : checkPortRow packet0351.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0352_port_checked : checkPortRow packet0352.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0353_port_checked : checkPortRow packet0353.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0354_port_checked : checkPortRow packet0354.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0355_port_checked : checkPortRow packet0355.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0356_port_checked : checkPortRow packet0356.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0357_port_checked : checkPortRow packet0357.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0358_port_checked : checkPortRow packet0358.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0359_port_checked : checkPortRow packet0359.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets014_ports_checked :
    packets014.all (fun q => checkPortRow q.row) = true := by
  simp only [packets014,List.all_cons,List.all_nil,Bool.true_and,
    packet0336_port_checked, packet0337_port_checked, packet0338_port_checked, packet0339_port_checked,
    packet0340_port_checked, packet0341_port_checked, packet0342_port_checked, packet0343_port_checked,
    packet0344_port_checked, packet0345_port_checked, packet0346_port_checked, packet0347_port_checked,
    packet0348_port_checked, packet0349_port_checked, packet0350_port_checked, packet0351_port_checked,
    packet0352_port_checked, packet0353_port_checked, packet0354_port_checked, packet0355_port_checked,
    packet0356_port_checked, packet0357_port_checked, packet0358_port_checked, packet0359_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
