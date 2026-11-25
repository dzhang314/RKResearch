module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets038

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0912_port_checked : checkPortRow packet0912.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0913_port_checked : checkPortRow packet0913.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0914_port_checked : checkPortRow packet0914.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0915_port_checked : checkPortRow packet0915.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0916_port_checked : checkPortRow packet0916.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0917_port_checked : checkPortRow packet0917.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0918_port_checked : checkPortRow packet0918.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0919_port_checked : checkPortRow packet0919.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0920_port_checked : checkPortRow packet0920.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0921_port_checked : checkPortRow packet0921.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0922_port_checked : checkPortRow packet0922.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0923_port_checked : checkPortRow packet0923.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0924_port_checked : checkPortRow packet0924.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0925_port_checked : checkPortRow packet0925.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0926_port_checked : checkPortRow packet0926.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0927_port_checked : checkPortRow packet0927.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0928_port_checked : checkPortRow packet0928.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0929_port_checked : checkPortRow packet0929.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0930_port_checked : checkPortRow packet0930.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0931_port_checked : checkPortRow packet0931.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0932_port_checked : checkPortRow packet0932.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0933_port_checked : checkPortRow packet0933.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0934_port_checked : checkPortRow packet0934.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0935_port_checked : checkPortRow packet0935.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets038_ports_checked :
    packets038.all (fun q => checkPortRow q.row) = true := by
  simp only [packets038,List.all_cons,List.all_nil,Bool.true_and,
    packet0912_port_checked, packet0913_port_checked, packet0914_port_checked, packet0915_port_checked,
    packet0916_port_checked, packet0917_port_checked, packet0918_port_checked, packet0919_port_checked,
    packet0920_port_checked, packet0921_port_checked, packet0922_port_checked, packet0923_port_checked,
    packet0924_port_checked, packet0925_port_checked, packet0926_port_checked, packet0927_port_checked,
    packet0928_port_checked, packet0929_port_checked, packet0930_port_checked, packet0931_port_checked,
    packet0932_port_checked, packet0933_port_checked, packet0934_port_checked, packet0935_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
