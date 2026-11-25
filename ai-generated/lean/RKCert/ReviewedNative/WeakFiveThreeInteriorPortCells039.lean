module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets039

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0936_port_checked : checkPortRow packet0936.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0937_port_checked : checkPortRow packet0937.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0938_port_checked : checkPortRow packet0938.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0939_port_checked : checkPortRow packet0939.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0940_port_checked : checkPortRow packet0940.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0941_port_checked : checkPortRow packet0941.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0942_port_checked : checkPortRow packet0942.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0943_port_checked : checkPortRow packet0943.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0944_port_checked : checkPortRow packet0944.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0945_port_checked : checkPortRow packet0945.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0946_port_checked : checkPortRow packet0946.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0947_port_checked : checkPortRow packet0947.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0948_port_checked : checkPortRow packet0948.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0949_port_checked : checkPortRow packet0949.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0950_port_checked : checkPortRow packet0950.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0951_port_checked : checkPortRow packet0951.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0952_port_checked : checkPortRow packet0952.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0953_port_checked : checkPortRow packet0953.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0954_port_checked : checkPortRow packet0954.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0955_port_checked : checkPortRow packet0955.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0956_port_checked : checkPortRow packet0956.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0957_port_checked : checkPortRow packet0957.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0958_port_checked : checkPortRow packet0958.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0959_port_checked : checkPortRow packet0959.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets039_ports_checked :
    packets039.all (fun q => checkPortRow q.row) = true := by
  simp only [packets039,List.all_cons,List.all_nil,Bool.true_and,
    packet0936_port_checked, packet0937_port_checked, packet0938_port_checked, packet0939_port_checked,
    packet0940_port_checked, packet0941_port_checked, packet0942_port_checked, packet0943_port_checked,
    packet0944_port_checked, packet0945_port_checked, packet0946_port_checked, packet0947_port_checked,
    packet0948_port_checked, packet0949_port_checked, packet0950_port_checked, packet0951_port_checked,
    packet0952_port_checked, packet0953_port_checked, packet0954_port_checked, packet0955_port_checked,
    packet0956_port_checked, packet0957_port_checked, packet0958_port_checked, packet0959_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
