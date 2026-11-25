module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets016

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0384_port_checked : checkPortRow packet0384.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0385_port_checked : checkPortRow packet0385.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0386_port_checked : checkPortRow packet0386.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0387_port_checked : checkPortRow packet0387.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0388_port_checked : checkPortRow packet0388.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0389_port_checked : checkPortRow packet0389.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0390_port_checked : checkPortRow packet0390.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0391_port_checked : checkPortRow packet0391.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0392_port_checked : checkPortRow packet0392.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0393_port_checked : checkPortRow packet0393.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0394_port_checked : checkPortRow packet0394.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0395_port_checked : checkPortRow packet0395.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0396_port_checked : checkPortRow packet0396.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0397_port_checked : checkPortRow packet0397.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0398_port_checked : checkPortRow packet0398.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0399_port_checked : checkPortRow packet0399.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0400_port_checked : checkPortRow packet0400.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0401_port_checked : checkPortRow packet0401.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0402_port_checked : checkPortRow packet0402.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0403_port_checked : checkPortRow packet0403.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0404_port_checked : checkPortRow packet0404.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0405_port_checked : checkPortRow packet0405.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0406_port_checked : checkPortRow packet0406.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0407_port_checked : checkPortRow packet0407.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets016_ports_checked :
    packets016.all (fun q => checkPortRow q.row) = true := by
  simp only [packets016,List.all_cons,List.all_nil,Bool.true_and,
    packet0384_port_checked, packet0385_port_checked, packet0386_port_checked, packet0387_port_checked,
    packet0388_port_checked, packet0389_port_checked, packet0390_port_checked, packet0391_port_checked,
    packet0392_port_checked, packet0393_port_checked, packet0394_port_checked, packet0395_port_checked,
    packet0396_port_checked, packet0397_port_checked, packet0398_port_checked, packet0399_port_checked,
    packet0400_port_checked, packet0401_port_checked, packet0402_port_checked, packet0403_port_checked,
    packet0404_port_checked, packet0405_port_checked, packet0406_port_checked, packet0407_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
