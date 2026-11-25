module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets011

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0264_port_checked : checkPortRow packet0264.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0265_port_checked : checkPortRow packet0265.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0266_port_checked : checkPortRow packet0266.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0267_port_checked : checkPortRow packet0267.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0268_port_checked : checkPortRow packet0268.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0269_port_checked : checkPortRow packet0269.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0270_port_checked : checkPortRow packet0270.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0271_port_checked : checkPortRow packet0271.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0272_port_checked : checkPortRow packet0272.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0273_port_checked : checkPortRow packet0273.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0274_port_checked : checkPortRow packet0274.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0275_port_checked : checkPortRow packet0275.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0276_port_checked : checkPortRow packet0276.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0277_port_checked : checkPortRow packet0277.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0278_port_checked : checkPortRow packet0278.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0279_port_checked : checkPortRow packet0279.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0280_port_checked : checkPortRow packet0280.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0281_port_checked : checkPortRow packet0281.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0282_port_checked : checkPortRow packet0282.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0283_port_checked : checkPortRow packet0283.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0284_port_checked : checkPortRow packet0284.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0285_port_checked : checkPortRow packet0285.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0286_port_checked : checkPortRow packet0286.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0287_port_checked : checkPortRow packet0287.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets011_ports_checked :
    packets011.all (fun q => checkPortRow q.row) = true := by
  simp only [packets011,List.all_cons,List.all_nil,Bool.true_and,
    packet0264_port_checked, packet0265_port_checked, packet0266_port_checked, packet0267_port_checked,
    packet0268_port_checked, packet0269_port_checked, packet0270_port_checked, packet0271_port_checked,
    packet0272_port_checked, packet0273_port_checked, packet0274_port_checked, packet0275_port_checked,
    packet0276_port_checked, packet0277_port_checked, packet0278_port_checked, packet0279_port_checked,
    packet0280_port_checked, packet0281_port_checked, packet0282_port_checked, packet0283_port_checked,
    packet0284_port_checked, packet0285_port_checked, packet0286_port_checked, packet0287_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
