module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets009

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0216_port_checked : checkPortRow packet0216.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0217_port_checked : checkPortRow packet0217.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0218_port_checked : checkPortRow packet0218.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0219_port_checked : checkPortRow packet0219.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0220_port_checked : checkPortRow packet0220.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0221_port_checked : checkPortRow packet0221.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0222_port_checked : checkPortRow packet0222.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0223_port_checked : checkPortRow packet0223.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0224_port_checked : checkPortRow packet0224.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0225_port_checked : checkPortRow packet0225.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0226_port_checked : checkPortRow packet0226.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0227_port_checked : checkPortRow packet0227.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0228_port_checked : checkPortRow packet0228.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0229_port_checked : checkPortRow packet0229.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0230_port_checked : checkPortRow packet0230.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0231_port_checked : checkPortRow packet0231.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0232_port_checked : checkPortRow packet0232.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0233_port_checked : checkPortRow packet0233.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0234_port_checked : checkPortRow packet0234.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0235_port_checked : checkPortRow packet0235.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0236_port_checked : checkPortRow packet0236.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0237_port_checked : checkPortRow packet0237.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0238_port_checked : checkPortRow packet0238.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0239_port_checked : checkPortRow packet0239.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets009_ports_checked :
    packets009.all (fun q => checkPortRow q.row) = true := by
  simp only [packets009,List.all_cons,List.all_nil,Bool.true_and,
    packet0216_port_checked, packet0217_port_checked, packet0218_port_checked, packet0219_port_checked,
    packet0220_port_checked, packet0221_port_checked, packet0222_port_checked, packet0223_port_checked,
    packet0224_port_checked, packet0225_port_checked, packet0226_port_checked, packet0227_port_checked,
    packet0228_port_checked, packet0229_port_checked, packet0230_port_checked, packet0231_port_checked,
    packet0232_port_checked, packet0233_port_checked, packet0234_port_checked, packet0235_port_checked,
    packet0236_port_checked, packet0237_port_checked, packet0238_port_checked, packet0239_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
