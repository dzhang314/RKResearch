module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets030

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0720_port_checked : checkPortRow packet0720.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0721_port_checked : checkPortRow packet0721.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0722_port_checked : checkPortRow packet0722.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0723_port_checked : checkPortRow packet0723.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0724_port_checked : checkPortRow packet0724.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0725_port_checked : checkPortRow packet0725.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0726_port_checked : checkPortRow packet0726.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0727_port_checked : checkPortRow packet0727.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0728_port_checked : checkPortRow packet0728.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0729_port_checked : checkPortRow packet0729.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0730_port_checked : checkPortRow packet0730.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0731_port_checked : checkPortRow packet0731.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0732_port_checked : checkPortRow packet0732.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0733_port_checked : checkPortRow packet0733.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0734_port_checked : checkPortRow packet0734.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0735_port_checked : checkPortRow packet0735.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0736_port_checked : checkPortRow packet0736.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0737_port_checked : checkPortRow packet0737.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0738_port_checked : checkPortRow packet0738.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0739_port_checked : checkPortRow packet0739.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0740_port_checked : checkPortRow packet0740.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0741_port_checked : checkPortRow packet0741.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0742_port_checked : checkPortRow packet0742.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0743_port_checked : checkPortRow packet0743.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets030_ports_checked :
    packets030.all (fun q => checkPortRow q.row) = true := by
  simp only [packets030,List.all_cons,List.all_nil,Bool.true_and,
    packet0720_port_checked, packet0721_port_checked, packet0722_port_checked, packet0723_port_checked,
    packet0724_port_checked, packet0725_port_checked, packet0726_port_checked, packet0727_port_checked,
    packet0728_port_checked, packet0729_port_checked, packet0730_port_checked, packet0731_port_checked,
    packet0732_port_checked, packet0733_port_checked, packet0734_port_checked, packet0735_port_checked,
    packet0736_port_checked, packet0737_port_checked, packet0738_port_checked, packet0739_port_checked,
    packet0740_port_checked, packet0741_port_checked, packet0742_port_checked, packet0743_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
