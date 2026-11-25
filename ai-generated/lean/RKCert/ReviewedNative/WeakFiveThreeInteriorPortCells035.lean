module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorPortCoordinates
public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripPackets035

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

private theorem packet0840_port_checked : checkPortRow packet0840.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0841_port_checked : checkPortRow packet0841.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0842_port_checked : checkPortRow packet0842.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0843_port_checked : checkPortRow packet0843.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0844_port_checked : checkPortRow packet0844.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0845_port_checked : checkPortRow packet0845.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0846_port_checked : checkPortRow packet0846.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0847_port_checked : checkPortRow packet0847.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0848_port_checked : checkPortRow packet0848.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0849_port_checked : checkPortRow packet0849.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0850_port_checked : checkPortRow packet0850.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0851_port_checked : checkPortRow packet0851.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0852_port_checked : checkPortRow packet0852.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0853_port_checked : checkPortRow packet0853.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0854_port_checked : checkPortRow packet0854.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0855_port_checked : checkPortRow packet0855.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0856_port_checked : checkPortRow packet0856.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0857_port_checked : checkPortRow packet0857.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0858_port_checked : checkPortRow packet0858.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0859_port_checked : checkPortRow packet0859.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0860_port_checked : checkPortRow packet0860.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0861_port_checked : checkPortRow packet0861.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0862_port_checked : checkPortRow packet0862.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

private theorem packet0863_port_checked : checkPortRow packet0863.row = true := by
  apply checkPortRow_intro
  intro w
  cases w <;> decide +kernel

theorem packets035_ports_checked :
    packets035.all (fun q => checkPortRow q.row) = true := by
  simp only [packets035,List.all_cons,List.all_nil,Bool.true_and,
    packet0840_port_checked, packet0841_port_checked, packet0842_port_checked, packet0843_port_checked,
    packet0844_port_checked, packet0845_port_checked, packet0846_port_checked, packet0847_port_checked,
    packet0848_port_checked, packet0849_port_checked, packet0850_port_checked, packet0851_port_checked,
    packet0852_port_checked, packet0853_port_checked, packet0854_port_checked, packet0855_port_checked,
    packet0856_port_checked, packet0857_port_checked, packet0858_port_checked, packet0859_port_checked,
    packet0860_port_checked, packet0861_port_checked, packet0862_port_checked, packet0863_port_checked]

end RKCert.ReviewedNative.ThreeInteriorPencil
