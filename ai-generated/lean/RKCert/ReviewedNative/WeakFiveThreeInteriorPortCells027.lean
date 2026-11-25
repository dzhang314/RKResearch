module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets027

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0648_port_checked : checkPortRow packet0648.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0649_port_checked : checkPortRow packet0649.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0650_port_checked : checkPortRow packet0650.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0651_port_checked : checkPortRow packet0651.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0652_port_checked : checkPortRow packet0652.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0653_port_checked : checkPortRow packet0653.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0654_port_checked : checkPortRow packet0654.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0655_port_checked : checkPortRow packet0655.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0656_port_checked : checkPortRow packet0656.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0657_port_checked : checkPortRow packet0657.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0658_port_checked : checkPortRow packet0658.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0659_port_checked : checkPortRow packet0659.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0660_port_checked : checkPortRow packet0660.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0661_port_checked : checkPortRow packet0661.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0662_port_checked : checkPortRow packet0662.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0663_port_checked : checkPortRow packet0663.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0664_port_checked : checkPortRow packet0664.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0665_port_checked : checkPortRow packet0665.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0666_port_checked : checkPortRow packet0666.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0667_port_checked : checkPortRow packet0667.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0668_port_checked : checkPortRow packet0668.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0669_port_checked : checkPortRow packet0669.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0670_port_checked : checkPortRow packet0670.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0671_port_checked : checkPortRow packet0671.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets027_ports_checked :
    packets027.all (fun q => checkPortRow q.row) = true := by
  simp only [packets027,List.all_cons,List.all_nil,Bool.true_and,
    packet0648_port_checked, packet0649_port_checked, packet0650_port_checked, packet0651_port_checked,
    packet0652_port_checked, packet0653_port_checked, packet0654_port_checked, packet0655_port_checked,
    packet0656_port_checked, packet0657_port_checked, packet0658_port_checked, packet0659_port_checked,
    packet0660_port_checked, packet0661_port_checked, packet0662_port_checked, packet0663_port_checked,
    packet0664_port_checked, packet0665_port_checked, packet0666_port_checked, packet0667_port_checked,
    packet0668_port_checked, packet0669_port_checked, packet0670_port_checked, packet0671_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
