module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets028

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0672_port_checked : checkPortRow packet0672.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0673_port_checked : checkPortRow packet0673.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0674_port_checked : checkPortRow packet0674.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0675_port_checked : checkPortRow packet0675.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0676_port_checked : checkPortRow packet0676.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0677_port_checked : checkPortRow packet0677.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0678_port_checked : checkPortRow packet0678.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0679_port_checked : checkPortRow packet0679.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0680_port_checked : checkPortRow packet0680.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0681_port_checked : checkPortRow packet0681.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0682_port_checked : checkPortRow packet0682.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0683_port_checked : checkPortRow packet0683.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0684_port_checked : checkPortRow packet0684.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0685_port_checked : checkPortRow packet0685.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0686_port_checked : checkPortRow packet0686.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0687_port_checked : checkPortRow packet0687.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0688_port_checked : checkPortRow packet0688.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0689_port_checked : checkPortRow packet0689.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0690_port_checked : checkPortRow packet0690.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0691_port_checked : checkPortRow packet0691.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0692_port_checked : checkPortRow packet0692.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0693_port_checked : checkPortRow packet0693.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0694_port_checked : checkPortRow packet0694.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0695_port_checked : checkPortRow packet0695.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets028_ports_checked :
    packets028.all (fun q => checkPortRow q.row) = true := by
  simp only [packets028,List.all_cons,List.all_nil,Bool.true_and,
    packet0672_port_checked, packet0673_port_checked, packet0674_port_checked, packet0675_port_checked,
    packet0676_port_checked, packet0677_port_checked, packet0678_port_checked, packet0679_port_checked,
    packet0680_port_checked, packet0681_port_checked, packet0682_port_checked, packet0683_port_checked,
    packet0684_port_checked, packet0685_port_checked, packet0686_port_checked, packet0687_port_checked,
    packet0688_port_checked, packet0689_port_checked, packet0690_port_checked, packet0691_port_checked,
    packet0692_port_checked, packet0693_port_checked, packet0694_port_checked, packet0695_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
