module

public import RKCert.ReviewedNative.NativePencilCubicIntDAGPart003

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e300 : o2.mul (List.nil : V2) b29=(List.nil : V2) := by rfl
theorem e301 : o1.mul b310 b28=b311 := by decide
theorem e302 : o0.scale 0 b28=(List.nil : V1) := by decide
theorem e303 : o1.add (List.nil : V1) b309=b309 := by rfl
theorem e304 : o1.mul b308 b28=b309 := @mul_cons V0 _ o0 0 b310 b28 b311 (List.nil : V1) b309 b309 e301 e302 (by rfl) e303
theorem e305 : o1.add (List.nil : V1) b307=b307 := by rfl
theorem e306 : o1.mul b306 b28=b307 := @mul_cons V0 _ o0 0 b308 b28 b309 (List.nil : V1) b307 b307 e304 e302 (by rfl) e305
theorem e307 : o1.add (List.nil : V1) b305=b305 := by rfl
theorem e308 : o1.mul b304 b28=b305 := @mul_cons V0 _ o0 0 b306 b28 b307 (List.nil : V1) b305 b305 e306 e302 (by rfl) e307
theorem e309 : o1.add (List.nil : V1) b303=b303 := by rfl
theorem e310 : o1.mul b302 b28=b303 := @mul_cons V0 _ o0 0 b304 b28 b305 (List.nil : V1) b303 b303 e308 e302 (by rfl) e309
theorem e311 : o1.add (List.nil : V1) b301=b301 := by rfl
theorem e312 : o1.mul b300 b28=b301 := @mul_cons V0 _ o0 0 b302 b28 b303 (List.nil : V1) b301 b301 e310 e302 (by rfl) e311
theorem e313 : o1.add (List.nil : V1) b299=b299 := by rfl
theorem e314 : o1.mul b298 b28=b299 := @mul_cons V0 _ o0 0 b300 b28 b301 (List.nil : V1) b299 b299 e312 e302 (by rfl) e313
theorem e315 : o1.add (List.nil : V1) b297=b297 := by rfl
theorem e316 : o1.mul b296 b28=b297 := @mul_cons V0 _ o0 0 b298 b28 b299 (List.nil : V1) b297 b297 e314 e302 (by rfl) e315
theorem e317 : o1.add (List.nil : V1) b294=b294 := by rfl
theorem e318 : o1.mul b26 b28=b294 := @mul_cons V0 _ o0 0 b296 b28 b297 (List.nil : V1) b294 b294 e316 e302 (by rfl) e317
theorem e319 : o1.scale b26 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e320 : o1.scale b26 b29=b295 := @scale_cons V1 _ o1 b26 b28 b294 (List.nil : V2) (List.nil : V2) b295 e318 e319 (by rfl)
theorem e321 : o2.add b295 (List.nil : V2)=b295 := by rfl
theorem e322 : o2.mul b27 b29=b295 := @mul_cons V1 _ o1 b26 (List.nil : V2) b29 (List.nil : V2) b295 (List.nil : V2) b295 e300 e320 (by rfl) e321

end RKResearch.Certified.Graded.NativePencilCubicIntDAG
