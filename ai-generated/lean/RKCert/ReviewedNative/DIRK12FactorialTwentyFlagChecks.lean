module

public import RKCert.ReviewedNative.DIRK12FactorialTwentyFlagData

@[expose] public section

namespace RKResearch.Certified.DIRK12FactorialTwentyFlag
open RKResearch ScaledIntegerFlagReplay FiniteRootedTree
open scoped Matrix
set_option maxRecDepth 50000
set_option maxHeartbeats 0
set_option Elab.async false

theorem check_D_pos : D ≠ 0 := by decide +kernel
theorem node_checked : checkNode packet=true := by decide +kernel

private theorem scales_checked :
    (List.range 12).all (fun k => decide (packet.spanScale k≠0))=true := by
  decide +kernel

theorem scale_nonzero (k : Nat) (h : k<12) : packet.spanScale k≠0 :=
  of_decide_eq_true (List.all_eq_true.mp scales_checked k (List.mem_range.mpr h))

private theorem s_checked : (List.range 12).all blockS=true := by decide +kernel
private theorem prim_checked : (List.range 11).all (checkPrimitive packet)=true := by decide +kernel
private theorem scalar_checked : (List.range 12).all (checkScalar packet)=true := by decide +kernel

theorem silent_checked (k : Nat) (h : k<12) (i : Fin (packet.size k)) :
    checkSilent packet k i=true :=
  List.all_eq_true.mp (List.all_eq_true.mp s_checked k (List.mem_range.mpr h))
    i (List.mem_finRange i)

theorem primitive_checked (k : Nat) (h : k+1<12) :
    checkPrimitive packet k=true :=
  List.all_eq_true.mp prim_checked k (List.mem_range.mpr (by omega))

theorem scalar_receipt (k : Nat) (h : k<12) :
    checkScalar packet k=true :=
  List.all_eq_true.mp scalar_checked k (List.mem_range.mpr h)

theorem raw_bush_checked :
    (161663040:ℤ)*((13:ℤ)*output packet (packet.clock^12)-D^13)=97351*D^13 := by
  decide +kernel

theorem raw_mixed_checked :
    (95800320:ℤ)*((117:ℤ)*output packet (packet.clock^3 * act packet (packet.clock^8))-
      D^13)=(-281923)*D^13 := by
  decide +kernel

theorem two_prime_products : (1642:ℤ)*97351+567*(-281923)=1 := by decide +kernel

theorem D_paid : D.toNat ∣ (Nat.factorial 12)^6 := by decide +kernel
theorem D_cast : (Int.ofNat D.toNat) = D := by decide +kernel

end RKResearch.Certified.DIRK12FactorialTwentyFlag
