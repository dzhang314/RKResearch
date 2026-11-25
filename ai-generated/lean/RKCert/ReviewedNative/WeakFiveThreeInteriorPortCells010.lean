module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets010

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0240_port_checked : checkPortRow packet0240.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0241_port_checked : checkPortRow packet0241.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0242_port_checked : checkPortRow packet0242.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0243_port_checked : checkPortRow packet0243.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0244_port_checked : checkPortRow packet0244.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0245_port_checked : checkPortRow packet0245.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0246_port_checked : checkPortRow packet0246.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0247_port_checked : checkPortRow packet0247.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0248_port_checked : checkPortRow packet0248.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0249_port_checked : checkPortRow packet0249.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0250_port_checked : checkPortRow packet0250.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0251_port_checked : checkPortRow packet0251.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0252_port_checked : checkPortRow packet0252.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0253_port_checked : checkPortRow packet0253.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0254_port_checked : checkPortRow packet0254.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0255_port_checked : checkPortRow packet0255.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0256_port_checked : checkPortRow packet0256.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0257_port_checked : checkPortRow packet0257.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0258_port_checked : checkPortRow packet0258.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0259_port_checked : checkPortRow packet0259.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0260_port_checked : checkPortRow packet0260.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0261_port_checked : checkPortRow packet0261.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0262_port_checked : checkPortRow packet0262.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0263_port_checked : checkPortRow packet0263.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets010_ports_checked :
    packets010.all (fun q => checkPortRow q.row) = true := by
  simp only [packets010,List.all_cons,List.all_nil,Bool.true_and,
    packet0240_port_checked, packet0241_port_checked, packet0242_port_checked, packet0243_port_checked,
    packet0244_port_checked, packet0245_port_checked, packet0246_port_checked, packet0247_port_checked,
    packet0248_port_checked, packet0249_port_checked, packet0250_port_checked, packet0251_port_checked,
    packet0252_port_checked, packet0253_port_checked, packet0254_port_checked, packet0255_port_checked,
    packet0256_port_checked, packet0257_port_checked, packet0258_port_checked, packet0259_port_checked,
    packet0260_port_checked, packet0261_port_checked, packet0262_port_checked, packet0263_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
