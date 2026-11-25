module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets040

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0960_port_checked : checkPortRow packet0960.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0961_port_checked : checkPortRow packet0961.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0962_port_checked : checkPortRow packet0962.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0963_port_checked : checkPortRow packet0963.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0964_port_checked : checkPortRow packet0964.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0965_port_checked : checkPortRow packet0965.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0966_port_checked : checkPortRow packet0966.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0967_port_checked : checkPortRow packet0967.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0968_port_checked : checkPortRow packet0968.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0969_port_checked : checkPortRow packet0969.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0970_port_checked : checkPortRow packet0970.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0971_port_checked : checkPortRow packet0971.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0972_port_checked : checkPortRow packet0972.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0973_port_checked : checkPortRow packet0973.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0974_port_checked : checkPortRow packet0974.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0975_port_checked : checkPortRow packet0975.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0976_port_checked : checkPortRow packet0976.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0977_port_checked : checkPortRow packet0977.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0978_port_checked : checkPortRow packet0978.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0979_port_checked : checkPortRow packet0979.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0980_port_checked : checkPortRow packet0980.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0981_port_checked : checkPortRow packet0981.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0982_port_checked : checkPortRow packet0982.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0983_port_checked : checkPortRow packet0983.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets040_ports_checked :
    packets040.all (fun q => checkPortRow q.row) = true := by
  simp only [packets040,List.all_cons,List.all_nil,Bool.true_and,
    packet0960_port_checked, packet0961_port_checked, packet0962_port_checked, packet0963_port_checked,
    packet0964_port_checked, packet0965_port_checked, packet0966_port_checked, packet0967_port_checked,
    packet0968_port_checked, packet0969_port_checked, packet0970_port_checked, packet0971_port_checked,
    packet0972_port_checked, packet0973_port_checked, packet0974_port_checked, packet0975_port_checked,
    packet0976_port_checked, packet0977_port_checked, packet0978_port_checked, packet0979_port_checked,
    packet0980_port_checked, packet0981_port_checked, packet0982_port_checked, packet0983_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
