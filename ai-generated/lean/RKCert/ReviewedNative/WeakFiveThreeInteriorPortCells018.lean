module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets018

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0432_port_checked : checkPortRow packet0432.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0433_port_checked : checkPortRow packet0433.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0434_port_checked : checkPortRow packet0434.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0435_port_checked : checkPortRow packet0435.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0436_port_checked : checkPortRow packet0436.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0437_port_checked : checkPortRow packet0437.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0438_port_checked : checkPortRow packet0438.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0439_port_checked : checkPortRow packet0439.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0440_port_checked : checkPortRow packet0440.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0441_port_checked : checkPortRow packet0441.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0442_port_checked : checkPortRow packet0442.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0443_port_checked : checkPortRow packet0443.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0444_port_checked : checkPortRow packet0444.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0445_port_checked : checkPortRow packet0445.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0446_port_checked : checkPortRow packet0446.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0447_port_checked : checkPortRow packet0447.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0448_port_checked : checkPortRow packet0448.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0449_port_checked : checkPortRow packet0449.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0450_port_checked : checkPortRow packet0450.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0451_port_checked : checkPortRow packet0451.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0452_port_checked : checkPortRow packet0452.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0453_port_checked : checkPortRow packet0453.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0454_port_checked : checkPortRow packet0454.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0455_port_checked : checkPortRow packet0455.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets018_ports_checked :
    packets018.all (fun q => checkPortRow q.row) = true := by
  simp only [packets018,List.all_cons,List.all_nil,Bool.true_and,
    packet0432_port_checked, packet0433_port_checked, packet0434_port_checked, packet0435_port_checked,
    packet0436_port_checked, packet0437_port_checked, packet0438_port_checked, packet0439_port_checked,
    packet0440_port_checked, packet0441_port_checked, packet0442_port_checked, packet0443_port_checked,
    packet0444_port_checked, packet0445_port_checked, packet0446_port_checked, packet0447_port_checked,
    packet0448_port_checked, packet0449_port_checked, packet0450_port_checked, packet0451_port_checked,
    packet0452_port_checked, packet0453_port_checked, packet0454_port_checked, packet0455_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
