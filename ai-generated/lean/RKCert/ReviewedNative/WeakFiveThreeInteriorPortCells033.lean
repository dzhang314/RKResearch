module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets033

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0792_port_checked : checkPortRow packet0792.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0793_port_checked : checkPortRow packet0793.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0794_port_checked : checkPortRow packet0794.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0795_port_checked : checkPortRow packet0795.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0796_port_checked : checkPortRow packet0796.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0797_port_checked : checkPortRow packet0797.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0798_port_checked : checkPortRow packet0798.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0799_port_checked : checkPortRow packet0799.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0800_port_checked : checkPortRow packet0800.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0801_port_checked : checkPortRow packet0801.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0802_port_checked : checkPortRow packet0802.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0803_port_checked : checkPortRow packet0803.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0804_port_checked : checkPortRow packet0804.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0805_port_checked : checkPortRow packet0805.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0806_port_checked : checkPortRow packet0806.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0807_port_checked : checkPortRow packet0807.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0808_port_checked : checkPortRow packet0808.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0809_port_checked : checkPortRow packet0809.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0810_port_checked : checkPortRow packet0810.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0811_port_checked : checkPortRow packet0811.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0812_port_checked : checkPortRow packet0812.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0813_port_checked : checkPortRow packet0813.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0814_port_checked : checkPortRow packet0814.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0815_port_checked : checkPortRow packet0815.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets033_ports_checked :
    packets033.all (fun q => checkPortRow q.row) = true := by
  simp only [packets033,List.all_cons,List.all_nil,Bool.true_and,
    packet0792_port_checked, packet0793_port_checked, packet0794_port_checked, packet0795_port_checked,
    packet0796_port_checked, packet0797_port_checked, packet0798_port_checked, packet0799_port_checked,
    packet0800_port_checked, packet0801_port_checked, packet0802_port_checked, packet0803_port_checked,
    packet0804_port_checked, packet0805_port_checked, packet0806_port_checked, packet0807_port_checked,
    packet0808_port_checked, packet0809_port_checked, packet0810_port_checked, packet0811_port_checked,
    packet0812_port_checked, packet0813_port_checked, packet0814_port_checked, packet0815_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
