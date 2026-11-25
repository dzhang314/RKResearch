module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart055

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e8250 : o3.add b3837 b5556=b1406 := @add_cons V2 _ o2 b3820 b5230 b451 (List.nil : V3) (List.nil : V3) (List.nil : V3) b1406 e8248 e8249 (by rfl)
theorem e8251 : o3.add b3835 b5815=b2614 := @add_cons V2 _ o2 b3809 b5219 b440 b3837 b5556 b1406 b2614 e8222 e8250 (by rfl)
theorem e8252 : o3.add b3833 b6067=b3675 := @add_cons V2 _ o2 b3797 b5207 b428 b3835 b5815 b2614 b3675 e8195 e8251 (by rfl)
theorem e8253 : o3.add b3831 b6330=b3660 := @add_cons V2 _ o2 b3784 b5194 b415 b3833 b6067 b3675 b3660 e8167 e8252 (by rfl)
theorem e8254 : o3.add b3829 b6604=b3646 := @add_cons V2 _ o2 b3770 b5180 b401 b3831 b6330 b3660 b3646 e8138 e8253 (by rfl)
theorem e8255 : o3.add b3827 b6889=b3633 := @add_cons V2 _ o2 b3755 b5165 b387 b3829 b6604 b3646 b3633 e8108 e8254 (by rfl)
theorem e8256 : o3.add b3825 b6985=b3621 := @add_cons V2 _ o2 b3739 b6952 b373 b3827 b6889 b3633 b3621 e8077 e8255 (by rfl)
theorem e8257 : o3.add b3823 b6969=b3610 := @add_cons V2 _ o2 b3723 b6936 b360 b3825 b6985 b3621 b3610 e8046 e8256 (by rfl)
theorem e8258 : o3.add b3821 b6953=b7003 := @add_cons V2 _ o2 b3707 b6920 b7002 b3823 b6969 b3610 b7003 e8015 e8257 (by rfl)
theorem e8259 : o1.add b0 b7001=(List.nil : V1) := by decide
theorem e8260 : o2.add (List.nil : V2) b2799=b2799 := by rfl
theorem e8261 : o2.add b1 b7002=b348 := @add_cons V1 _ o1 b0 b7001 (List.nil : V1) (List.nil : V2) b2799 b2799 b348 e8259 e8260 (by rfl)
theorem e8262 : o3.add (List.nil : V3) b3610=b3610 := by rfl
theorem e8263 : o3.add b2 b7003=b452 := @add_cons V2 _ o2 b1 b7002 b348 (List.nil : V3) b3610 b3610 b452 e8261 e8262 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
