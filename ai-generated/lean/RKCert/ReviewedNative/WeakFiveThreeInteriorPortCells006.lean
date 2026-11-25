module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets006

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0144_port_checked : checkPortRow packet0144.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0145_port_checked : checkPortRow packet0145.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0146_port_checked : checkPortRow packet0146.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0147_port_checked : checkPortRow packet0147.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0148_port_checked : checkPortRow packet0148.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0149_port_checked : checkPortRow packet0149.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0150_port_checked : checkPortRow packet0150.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0151_port_checked : checkPortRow packet0151.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0152_port_checked : checkPortRow packet0152.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0153_port_checked : checkPortRow packet0153.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0154_port_checked : checkPortRow packet0154.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0155_port_checked : checkPortRow packet0155.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0156_port_checked : checkPortRow packet0156.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0157_port_checked : checkPortRow packet0157.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0158_port_checked : checkPortRow packet0158.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0159_port_checked : checkPortRow packet0159.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0160_port_checked : checkPortRow packet0160.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0161_port_checked : checkPortRow packet0161.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0162_port_checked : checkPortRow packet0162.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0163_port_checked : checkPortRow packet0163.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0164_port_checked : checkPortRow packet0164.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0165_port_checked : checkPortRow packet0165.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0166_port_checked : checkPortRow packet0166.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0167_port_checked : checkPortRow packet0167.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets006_ports_checked :
    packets006.all (fun q => checkPortRow q.row) = true := by
  simp only [packets006,List.all_cons,List.all_nil,Bool.true_and,
    packet0144_port_checked, packet0145_port_checked, packet0146_port_checked, packet0147_port_checked,
    packet0148_port_checked, packet0149_port_checked, packet0150_port_checked, packet0151_port_checked,
    packet0152_port_checked, packet0153_port_checked, packet0154_port_checked, packet0155_port_checked,
    packet0156_port_checked, packet0157_port_checked, packet0158_port_checked, packet0159_port_checked,
    packet0160_port_checked, packet0161_port_checked, packet0162_port_checked, packet0163_port_checked,
    packet0164_port_checked, packet0165_port_checked, packet0166_port_checked, packet0167_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
