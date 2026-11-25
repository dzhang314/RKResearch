module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets026

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0624_port_checked : checkPortRow packet0624.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0625_port_checked : checkPortRow packet0625.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0626_port_checked : checkPortRow packet0626.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0627_port_checked : checkPortRow packet0627.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0628_port_checked : checkPortRow packet0628.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0629_port_checked : checkPortRow packet0629.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0630_port_checked : checkPortRow packet0630.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0631_port_checked : checkPortRow packet0631.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0632_port_checked : checkPortRow packet0632.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0633_port_checked : checkPortRow packet0633.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0634_port_checked : checkPortRow packet0634.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0635_port_checked : checkPortRow packet0635.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0636_port_checked : checkPortRow packet0636.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0637_port_checked : checkPortRow packet0637.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0638_port_checked : checkPortRow packet0638.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0639_port_checked : checkPortRow packet0639.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0640_port_checked : checkPortRow packet0640.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0641_port_checked : checkPortRow packet0641.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0642_port_checked : checkPortRow packet0642.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0643_port_checked : checkPortRow packet0643.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0644_port_checked : checkPortRow packet0644.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0645_port_checked : checkPortRow packet0645.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0646_port_checked : checkPortRow packet0646.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0647_port_checked : checkPortRow packet0647.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets026_ports_checked :
    packets026.all (fun q => checkPortRow q.row) = true := by
  simp only [packets026,List.all_cons,List.all_nil,Bool.true_and,
    packet0624_port_checked, packet0625_port_checked, packet0626_port_checked, packet0627_port_checked,
    packet0628_port_checked, packet0629_port_checked, packet0630_port_checked, packet0631_port_checked,
    packet0632_port_checked, packet0633_port_checked, packet0634_port_checked, packet0635_port_checked,
    packet0636_port_checked, packet0637_port_checked, packet0638_port_checked, packet0639_port_checked,
    packet0640_port_checked, packet0641_port_checked, packet0642_port_checked, packet0643_port_checked,
    packet0644_port_checked, packet0645_port_checked, packet0646_port_checked, packet0647_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
