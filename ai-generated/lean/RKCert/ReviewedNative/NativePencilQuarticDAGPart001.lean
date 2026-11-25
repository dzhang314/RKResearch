module

public import RKCert.ReviewedNative.NativePencilQuarticDAGData

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e0 : o3.mul (List.nil : V3) b34=(List.nil : V3) := by rfl
theorem e1 : o2.mul (List.nil : V2) b33=(List.nil : V2) := by rfl
theorem e2 : o1.mul b43 b18=b225 := by decide
theorem e3 : o1.mul b43 b19=b226 := by decide
theorem e4 : o1.mul b43 b20=b227 := by decide
theorem e5 : o1.mul b43 b21=b228 := by decide
theorem e6 : o1.mul b43 b22=b229 := by decide
theorem e7 : o1.mul b43 b23=b230 := by decide
theorem e8 : o1.mul b43 b24=b231 := by decide
theorem e9 : o1.mul b43 b25=b232 := by decide
theorem e10 : o1.mul b43 b26=b233 := by decide
theorem e11 : o1.mul b43 b27=b234 := by decide
theorem e12 : o1.mul b43 b28=b235 := by decide
theorem e13 : o1.mul b43 b29=b236 := by decide
theorem e14 : o1.mul b43 b30=b237 := by decide
theorem e15 : o1.mul b43 b31=b238 := by decide
theorem e16 : o1.mul b43 b32=b109 := by decide
theorem e17 : o1.scale b43 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e18 : o1.scale b43 b266=b267 := @scale_cons V1 _ o1 b43 b32 b109 (List.nil : V2) (List.nil : V2) b267 e16 e17 (by rfl)
theorem e19 : o1.scale b43 b264=b265 := @scale_cons V1 _ o1 b43 b31 b238 b266 b267 b265 e15 e18 (by rfl)
theorem e20 : o1.scale b43 b262=b263 := @scale_cons V1 _ o1 b43 b30 b237 b264 b265 b263 e14 e19 (by rfl)
theorem e21 : o1.scale b43 b260=b261 := @scale_cons V1 _ o1 b43 b29 b236 b262 b263 b261 e13 e20 (by rfl)
theorem e22 : o1.scale b43 b258=b259 := @scale_cons V1 _ o1 b43 b28 b235 b260 b261 b259 e12 e21 (by rfl)
theorem e23 : o1.scale b43 b256=b257 := @scale_cons V1 _ o1 b43 b27 b234 b258 b259 b257 e11 e22 (by rfl)
theorem e24 : o1.scale b43 b254=b255 := @scale_cons V1 _ o1 b43 b26 b233 b256 b257 b255 e10 e23 (by rfl)
theorem e25 : o1.scale b43 b252=b253 := @scale_cons V1 _ o1 b43 b25 b232 b254 b255 b253 e9 e24 (by rfl)
theorem e26 : o1.scale b43 b250=b251 := @scale_cons V1 _ o1 b43 b24 b231 b252 b253 b251 e8 e25 (by rfl)
theorem e27 : o1.scale b43 b248=b249 := @scale_cons V1 _ o1 b43 b23 b230 b250 b251 b249 e7 e26 (by rfl)
theorem e28 : o1.scale b43 b246=b247 := @scale_cons V1 _ o1 b43 b22 b229 b248 b249 b247 e6 e27 (by rfl)
theorem e29 : o1.scale b43 b244=b245 := @scale_cons V1 _ o1 b43 b21 b228 b246 b247 b245 e5 e28 (by rfl)
theorem e30 : o1.scale b43 b242=b243 := @scale_cons V1 _ o1 b43 b20 b227 b244 b245 b243 e4 e29 (by rfl)
theorem e31 : o1.scale b43 b240=b241 := @scale_cons V1 _ o1 b43 b19 b226 b242 b243 b241 e3 e30 (by rfl)
theorem e32 : o1.scale b43 b33=b239 := @scale_cons V1 _ o1 b43 b18 b225 b240 b241 b239 e2 e31 (by rfl)
theorem e33 : o2.add b239 (List.nil : V2)=b239 := by rfl
theorem e34 : o2.mul b224 b33=b239 := @mul_cons V1 _ o1 b43 (List.nil : V2) b33 (List.nil : V2) b239 (List.nil : V2) b239 e1 e32 (by rfl) e33
theorem e35 : o1.mul b42 b18=b209 := by decide
theorem e36 : o1.mul b42 b19=b268 := by decide
theorem e37 : o1.mul b42 b20=b269 := by decide
theorem e38 : o1.mul b42 b21=b270 := by decide
theorem e39 : o1.mul b42 b22=b271 := by decide
theorem e40 : o1.mul b42 b23=b272 := by decide
theorem e41 : o1.mul b42 b24=b273 := by decide
theorem e42 : o1.mul b42 b25=b274 := by decide
theorem e43 : o1.mul b42 b26=b275 := by decide
theorem e44 : o1.mul b42 b27=b276 := by decide
theorem e45 : o1.mul b42 b28=b277 := by decide
theorem e46 : o1.mul b42 b29=b278 := by decide
theorem e47 : o1.mul b42 b30=b279 := by decide
theorem e48 : o1.mul b42 b31=b280 := by decide
theorem e49 : o1.mul b42 b32=b281 := by decide
theorem e50 : o1.scale b42 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e51 : o1.scale b42 b266=b296 := @scale_cons V1 _ o1 b42 b32 b281 (List.nil : V2) (List.nil : V2) b296 e49 e50 (by rfl)
theorem e52 : o1.scale b42 b264=b295 := @scale_cons V1 _ o1 b42 b31 b280 b266 b296 b295 e48 e51 (by rfl)
theorem e53 : o1.scale b42 b262=b294 := @scale_cons V1 _ o1 b42 b30 b279 b264 b295 b294 e47 e52 (by rfl)
theorem e54 : o1.scale b42 b260=b293 := @scale_cons V1 _ o1 b42 b29 b278 b262 b294 b293 e46 e53 (by rfl)
theorem e55 : o1.scale b42 b258=b292 := @scale_cons V1 _ o1 b42 b28 b277 b260 b293 b292 e45 e54 (by rfl)
theorem e56 : o1.scale b42 b256=b291 := @scale_cons V1 _ o1 b42 b27 b276 b258 b292 b291 e44 e55 (by rfl)
theorem e57 : o1.scale b42 b254=b290 := @scale_cons V1 _ o1 b42 b26 b275 b256 b291 b290 e43 e56 (by rfl)
theorem e58 : o1.scale b42 b252=b289 := @scale_cons V1 _ o1 b42 b25 b274 b254 b290 b289 e42 e57 (by rfl)
theorem e59 : o1.scale b42 b250=b288 := @scale_cons V1 _ o1 b42 b24 b273 b252 b289 b288 e41 e58 (by rfl)
theorem e60 : o1.scale b42 b248=b287 := @scale_cons V1 _ o1 b42 b23 b272 b250 b288 b287 e40 e59 (by rfl)
theorem e61 : o1.scale b42 b246=b286 := @scale_cons V1 _ o1 b42 b22 b271 b248 b287 b286 e39 e60 (by rfl)
theorem e62 : o1.scale b42 b244=b285 := @scale_cons V1 _ o1 b42 b21 b270 b246 b286 b285 e38 e61 (by rfl)
theorem e63 : o1.scale b42 b242=b284 := @scale_cons V1 _ o1 b42 b20 b269 b244 b285 b284 e37 e62 (by rfl)
theorem e64 : o1.scale b42 b240=b283 := @scale_cons V1 _ o1 b42 b19 b268 b242 b284 b283 e36 e63 (by rfl)
theorem e65 : o1.scale b42 b33=b282 := @scale_cons V1 _ o1 b42 b18 b209 b240 b283 b282 e35 e64 (by rfl)
theorem e66 : o1.add b209 (List.nil : V1)=b209 := by rfl
theorem e67 : o1.add b268 b225=b210 := by decide
theorem e68 : o1.add b269 b226=b211 := by decide
theorem e69 : o1.add b270 b227=b212 := by decide
theorem e70 : o1.add b271 b228=b213 := by decide
theorem e71 : o1.add b272 b229=b214 := by decide
theorem e72 : o1.add b273 b230=b215 := by decide
theorem e73 : o1.add b274 b231=b216 := by decide
theorem e74 : o1.add b275 b232=b217 := by decide
theorem e75 : o1.add b276 b233=b218 := by decide
theorem e76 : o1.add b277 b234=b219 := by decide
theorem e77 : o1.add b278 b235=b220 := by decide
theorem e78 : o1.add b279 b236=b221 := by decide
theorem e79 : o1.add b280 b237=b222 := by decide
theorem e80 : o1.add b281 b238=b108 := by decide
theorem e81 : o2.add (List.nil : V2) b267=b267 := by rfl
theorem e82 : o2.add b296 b265=b311 := @add_cons V1 _ o1 b281 b238 b108 (List.nil : V2) b267 b267 b311 e80 e81 (by rfl)
theorem e83 : o2.add b295 b263=b310 := @add_cons V1 _ o1 b280 b237 b222 b296 b265 b311 b310 e79 e82 (by rfl)
theorem e84 : o2.add b294 b261=b309 := @add_cons V1 _ o1 b279 b236 b221 b295 b263 b310 b309 e78 e83 (by rfl)
theorem e85 : o2.add b293 b259=b308 := @add_cons V1 _ o1 b278 b235 b220 b294 b261 b309 b308 e77 e84 (by rfl)
theorem e86 : o2.add b292 b257=b307 := @add_cons V1 _ o1 b277 b234 b219 b293 b259 b308 b307 e76 e85 (by rfl)
theorem e87 : o2.add b291 b255=b306 := @add_cons V1 _ o1 b276 b233 b218 b292 b257 b307 b306 e75 e86 (by rfl)
theorem e88 : o2.add b290 b253=b305 := @add_cons V1 _ o1 b275 b232 b217 b291 b255 b306 b305 e74 e87 (by rfl)
theorem e89 : o2.add b289 b251=b304 := @add_cons V1 _ o1 b274 b231 b216 b290 b253 b305 b304 e73 e88 (by rfl)
theorem e90 : o2.add b288 b249=b303 := @add_cons V1 _ o1 b273 b230 b215 b289 b251 b304 b303 e72 e89 (by rfl)
theorem e91 : o2.add b287 b247=b302 := @add_cons V1 _ o1 b272 b229 b214 b288 b249 b303 b302 e71 e90 (by rfl)
theorem e92 : o2.add b286 b245=b301 := @add_cons V1 _ o1 b271 b228 b213 b287 b247 b302 b301 e70 e91 (by rfl)
theorem e93 : o2.add b285 b243=b300 := @add_cons V1 _ o1 b270 b227 b212 b286 b245 b301 b300 e69 e92 (by rfl)
theorem e94 : o2.add b284 b241=b299 := @add_cons V1 _ o1 b269 b226 b211 b285 b243 b300 b299 e68 e93 (by rfl)
theorem e95 : o2.add b283 b239=b298 := @add_cons V1 _ o1 b268 b225 b210 b284 b241 b299 b298 e67 e94 (by rfl)
theorem e96 : o2.add b282 b297=b223 := @add_cons V1 _ o1 b209 (List.nil : V1) b209 b283 b239 b298 b223 e66 e95 (by rfl)
theorem e97 : o2.mul b208 b33=b223 := @mul_cons V1 _ o1 b42 b224 b33 b239 b282 b297 b223 e34 e65 (by rfl) e96
theorem e98 : o1.mul b41 b18=b193 := by decide
theorem e99 : o1.mul b41 b19=b312 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
