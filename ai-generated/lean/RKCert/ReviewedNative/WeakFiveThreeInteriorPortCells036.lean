module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets036

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0864_port_checked : checkPortRow packet0864.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0865_port_checked : checkPortRow packet0865.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0866_port_checked : checkPortRow packet0866.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0867_port_checked : checkPortRow packet0867.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0868_port_checked : checkPortRow packet0868.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0869_port_checked : checkPortRow packet0869.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0870_port_checked : checkPortRow packet0870.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0871_port_checked : checkPortRow packet0871.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0872_port_checked : checkPortRow packet0872.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0873_port_checked : checkPortRow packet0873.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0874_port_checked : checkPortRow packet0874.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0875_port_checked : checkPortRow packet0875.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0876_port_checked : checkPortRow packet0876.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0877_port_checked : checkPortRow packet0877.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0878_port_checked : checkPortRow packet0878.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0879_port_checked : checkPortRow packet0879.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0880_port_checked : checkPortRow packet0880.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0881_port_checked : checkPortRow packet0881.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0882_port_checked : checkPortRow packet0882.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0883_port_checked : checkPortRow packet0883.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0884_port_checked : checkPortRow packet0884.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0885_port_checked : checkPortRow packet0885.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0886_port_checked : checkPortRow packet0886.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0887_port_checked : checkPortRow packet0887.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets036_ports_checked :
    packets036.all (fun q => checkPortRow q.row) = true := by
  simp only [packets036,List.all_cons,List.all_nil,Bool.true_and,
    packet0864_port_checked, packet0865_port_checked, packet0866_port_checked, packet0867_port_checked,
    packet0868_port_checked, packet0869_port_checked, packet0870_port_checked, packet0871_port_checked,
    packet0872_port_checked, packet0873_port_checked, packet0874_port_checked, packet0875_port_checked,
    packet0876_port_checked, packet0877_port_checked, packet0878_port_checked, packet0879_port_checked,
    packet0880_port_checked, packet0881_port_checked, packet0882_port_checked, packet0883_port_checked,
    packet0884_port_checked, packet0885_port_checked, packet0886_port_checked, packet0887_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
