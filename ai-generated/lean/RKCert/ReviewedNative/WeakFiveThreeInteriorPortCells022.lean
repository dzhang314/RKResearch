module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets022

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0528_port_checked : checkPortRow packet0528.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0529_port_checked : checkPortRow packet0529.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0530_port_checked : checkPortRow packet0530.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0531_port_checked : checkPortRow packet0531.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0532_port_checked : checkPortRow packet0532.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0533_port_checked : checkPortRow packet0533.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0534_port_checked : checkPortRow packet0534.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0535_port_checked : checkPortRow packet0535.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0536_port_checked : checkPortRow packet0536.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0537_port_checked : checkPortRow packet0537.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0538_port_checked : checkPortRow packet0538.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0539_port_checked : checkPortRow packet0539.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0540_port_checked : checkPortRow packet0540.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0541_port_checked : checkPortRow packet0541.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0542_port_checked : checkPortRow packet0542.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0543_port_checked : checkPortRow packet0543.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0544_port_checked : checkPortRow packet0544.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0545_port_checked : checkPortRow packet0545.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0546_port_checked : checkPortRow packet0546.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0547_port_checked : checkPortRow packet0547.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0548_port_checked : checkPortRow packet0548.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0549_port_checked : checkPortRow packet0549.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0550_port_checked : checkPortRow packet0550.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0551_port_checked : checkPortRow packet0551.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets022_ports_checked :
    packets022.all (fun q => checkPortRow q.row) = true := by
  simp only [packets022,List.all_cons,List.all_nil,Bool.true_and,
    packet0528_port_checked, packet0529_port_checked, packet0530_port_checked, packet0531_port_checked,
    packet0532_port_checked, packet0533_port_checked, packet0534_port_checked, packet0535_port_checked,
    packet0536_port_checked, packet0537_port_checked, packet0538_port_checked, packet0539_port_checked,
    packet0540_port_checked, packet0541_port_checked, packet0542_port_checked, packet0543_port_checked,
    packet0544_port_checked, packet0545_port_checked, packet0546_port_checked, packet0547_port_checked,
    packet0548_port_checked, packet0549_port_checked, packet0550_port_checked, packet0551_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
