module

public import RKCert.ReviewedNative.NativePencilCubicIntDAGPart002

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e200 : o1.add b225 b173=b167 := by decide
theorem e201 : o1.add b226 b174=b168 := by decide
theorem e202 : o1.add b227 b175=b169 := by decide
theorem e203 : o1.add b228 b176=b170 := by decide
theorem e204 : o1.add b229 b177=b154 := by decide
theorem e205 : o2.add (List.nil : V2) b224=b224 := by rfl
theorem e206 : o2.add b235 b223=b247 := @add_cons V1 _ o1 b229 b177 b154 (List.nil : V2) b224 b224 b247 e204 e205 (by rfl)
theorem e207 : o2.add b234 b222=b246 := @add_cons V1 _ o1 b228 b176 b170 b235 b223 b247 b246 e203 e206 (by rfl)
theorem e208 : o2.add b233 b221=b245 := @add_cons V1 _ o1 b227 b175 b169 b234 b222 b246 b245 e202 e207 (by rfl)
theorem e209 : o2.add b232 b220=b244 := @add_cons V1 _ o1 b226 b174 b168 b233 b221 b245 b244 e201 e208 (by rfl)
theorem e210 : o2.add b231 b178=b243 := @add_cons V1 _ o1 b225 b173 b167 b232 b220 b244 b243 e200 e209 (by rfl)
theorem e211 : o2.add b230 b242=b171 := @add_cons V1 _ o1 b166 (List.nil : V1) b166 b231 b178 b243 b171 e199 e210 (by rfl)
theorem e212 : o2.mul b165 b13=b171 := @mul_cons V1 _ o1 b22 b172 b13 b178 b230 b242 b171 e179 e198 (by rfl) e211
theorem e213 : o1.mul b21 b7=b159 := by decide
theorem e214 : o1.mul b21 b8=b248 := by decide
theorem e215 : o1.mul b21 b9=b249 := by decide
theorem e216 : o1.mul b21 b10=b250 := by decide
theorem e217 : o1.mul b21 b11=b251 := by decide
theorem e218 : o1.mul b263 b12=b264 := by decide
theorem e219 : o1.add (List.nil : V1) b262=b262 := by rfl
theorem e220 : o1.mul b261 b12=b262 := @mul_cons V0 _ o0 0 b263 b12 b264 (List.nil : V1) b262 b262 e218 e131 (by rfl) e219
theorem e221 : o1.add (List.nil : V1) b260=b260 := by rfl
theorem e222 : o1.mul b259 b12=b260 := @mul_cons V0 _ o0 0 b261 b12 b262 (List.nil : V1) b260 b260 e220 e131 (by rfl) e221
theorem e223 : o1.add (List.nil : V1) b252=b252 := by rfl
theorem e224 : o1.mul b21 b12=b252 := @mul_cons V0 _ o0 0 b259 b12 b260 (List.nil : V1) b252 b252 e222 e131 (by rfl) e223
theorem e225 : o1.scale b21 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e226 : o1.scale b21 b194=b258 := @scale_cons V1 _ o1 b21 b12 b252 (List.nil : V2) (List.nil : V2) b258 e224 e225 (by rfl)
theorem e227 : o1.scale b21 b192=b257 := @scale_cons V1 _ o1 b21 b11 b251 b194 b258 b257 e217 e226 (by rfl)
theorem e228 : o1.scale b21 b190=b256 := @scale_cons V1 _ o1 b21 b10 b250 b192 b257 b256 e216 e227 (by rfl)
theorem e229 : o1.scale b21 b188=b255 := @scale_cons V1 _ o1 b21 b9 b249 b190 b256 b255 e215 e228 (by rfl)
theorem e230 : o1.scale b21 b186=b254 := @scale_cons V1 _ o1 b21 b8 b248 b188 b255 b254 e214 e229 (by rfl)
theorem e231 : o1.scale b21 b13=b253 := @scale_cons V1 _ o1 b21 b7 b159 b186 b254 b253 e213 e230 (by rfl)
theorem e232 : o1.add b159 (List.nil : V1)=b159 := by rfl
theorem e233 : o1.add b248 b166=b160 := by decide
theorem e234 : o1.add b249 b167=b161 := by decide
theorem e235 : o1.add b250 b168=b162 := by decide
theorem e236 : o1.add b251 b169=b163 := by decide
theorem e237 : o1.add b252 b170=b153 := by decide
theorem e238 : o2.add (List.nil : V2) b247=b247 := by rfl
theorem e239 : o2.add b258 b246=b270 := @add_cons V1 _ o1 b252 b170 b153 (List.nil : V2) b247 b247 b270 e237 e238 (by rfl)
theorem e240 : o2.add b257 b245=b269 := @add_cons V1 _ o1 b251 b169 b163 b258 b246 b270 b269 e236 e239 (by rfl)
theorem e241 : o2.add b256 b244=b268 := @add_cons V1 _ o1 b250 b168 b162 b257 b245 b269 b268 e235 e240 (by rfl)
theorem e242 : o2.add b255 b243=b267 := @add_cons V1 _ o1 b249 b167 b161 b256 b244 b268 b267 e234 e241 (by rfl)
theorem e243 : o2.add b254 b171=b266 := @add_cons V1 _ o1 b248 b166 b160 b255 b243 b267 b266 e233 e242 (by rfl)
theorem e244 : o2.add b253 b265=b164 := @add_cons V1 _ o1 b159 (List.nil : V1) b159 b254 b171 b266 b164 e232 e243 (by rfl)
theorem e245 : o2.mul b158 b13=b164 := @mul_cons V1 _ o1 b21 b165 b13 b171 b253 b265 b164 e212 e231 (by rfl) e244
theorem e246 : o1.mul b20 b7=b147 := by decide
theorem e247 : o1.mul b20 b8=b271 := by decide
theorem e248 : o1.mul b20 b9=b272 := by decide
theorem e249 : o1.mul b20 b10=b273 := by decide
theorem e250 : o1.mul b20 b11=b274 := by decide
theorem e251 : o1.mul b286 b12=b287 := by decide
theorem e252 : o1.add (List.nil : V1) b285=b285 := by rfl
theorem e253 : o1.mul b284 b12=b285 := @mul_cons V0 _ o0 0 b286 b12 b287 (List.nil : V1) b285 b285 e251 e131 (by rfl) e252
theorem e254 : o1.add (List.nil : V1) b283=b283 := by rfl
theorem e255 : o1.mul b282 b12=b283 := @mul_cons V0 _ o0 0 b284 b12 b285 (List.nil : V1) b283 b283 e253 e131 (by rfl) e254
theorem e256 : o1.add (List.nil : V1) b275=b275 := by rfl
theorem e257 : o1.mul b20 b12=b275 := @mul_cons V0 _ o0 0 b282 b12 b283 (List.nil : V1) b275 b275 e255 e131 (by rfl) e256
theorem e258 : o1.scale b20 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e259 : o1.scale b20 b194=b281 := @scale_cons V1 _ o1 b20 b12 b275 (List.nil : V2) (List.nil : V2) b281 e257 e258 (by rfl)
theorem e260 : o1.scale b20 b192=b280 := @scale_cons V1 _ o1 b20 b11 b274 b194 b281 b280 e250 e259 (by rfl)
theorem e261 : o1.scale b20 b190=b279 := @scale_cons V1 _ o1 b20 b10 b273 b192 b280 b279 e249 e260 (by rfl)
theorem e262 : o1.scale b20 b188=b278 := @scale_cons V1 _ o1 b20 b9 b272 b190 b279 b278 e248 e261 (by rfl)
theorem e263 : o1.scale b20 b186=b277 := @scale_cons V1 _ o1 b20 b8 b271 b188 b278 b277 e247 e262 (by rfl)
theorem e264 : o1.scale b20 b13=b276 := @scale_cons V1 _ o1 b20 b7 b147 b186 b277 b276 e246 e263 (by rfl)
theorem e265 : o1.add b147 (List.nil : V1)=b147 := by rfl
theorem e266 : o1.add b271 b159=b148 := by decide
theorem e267 : o1.add b272 b160=b149 := by decide
theorem e268 : o1.add b273 b161=b150 := by decide
theorem e269 : o1.add b274 b162=b151 := by decide
theorem e270 : o1.add b275 b163=b152 := by decide
theorem e271 : o2.add (List.nil : V2) b270=b270 := by rfl
theorem e272 : o2.add b281 b269=b293 := @add_cons V1 _ o1 b275 b163 b152 (List.nil : V2) b270 b270 b293 e270 e271 (by rfl)
theorem e273 : o2.add b280 b268=b292 := @add_cons V1 _ o1 b274 b162 b151 b281 b269 b293 b292 e269 e272 (by rfl)
theorem e274 : o2.add b279 b267=b291 := @add_cons V1 _ o1 b273 b161 b150 b280 b268 b292 b291 e268 e273 (by rfl)
theorem e275 : o2.add b278 b266=b290 := @add_cons V1 _ o1 b272 b160 b149 b279 b267 b291 b290 e267 e274 (by rfl)
theorem e276 : o2.add b277 b164=b289 := @add_cons V1 _ o1 b271 b159 b148 b278 b266 b290 b289 e266 e275 (by rfl)
theorem e277 : o2.add b276 b288=b157 := @add_cons V1 _ o1 b147 (List.nil : V1) b147 b277 b164 b289 b157 e265 e276 (by rfl)
theorem e278 : o2.mul b25 b13=b157 := @mul_cons V1 _ o1 b20 b158 b13 b164 b276 b288 b157 e245 e264 (by rfl) e277
theorem e279 : o1.add b30 b147=b294 := by decide
theorem e280 : o1.add b31 b148=(List.nil : V1) := by decide
theorem e281 : o1.add b32 b149=(List.nil : V1) := by decide
theorem e282 : o1.add b33 b150=(List.nil : V1) := by decide
theorem e283 : o1.add b34 b151=(List.nil : V1) := by decide
theorem e284 : o1.add b35 b152=(List.nil : V1) := by decide
theorem e285 : o1.add b36 b153=(List.nil : V1) := by decide
theorem e286 : o1.add b37 b154=(List.nil : V1) := by decide
theorem e287 : o1.add b38 b155=(List.nil : V1) := by decide
theorem e288 : o1.add b39 b156=(List.nil : V1) := by decide
theorem e289 : o2.add (List.nil : V2) (List.nil : V2)=(List.nil : V2) := by rfl
theorem e290 : o2.add b78 b195=(List.nil : V2) := @add_cons V1 _ o1 b39 b156 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) (List.nil : V2) e288 e289 (by rfl)
theorem e291 : o2.add b95 b224=(List.nil : V2) := @add_cons V1 _ o1 b38 b155 (List.nil : V1) b78 b195 (List.nil : V2) (List.nil : V2) e287 e290 (by rfl)
theorem e292 : o2.add b112 b247=(List.nil : V2) := @add_cons V1 _ o1 b37 b154 (List.nil : V1) b95 b224 (List.nil : V2) (List.nil : V2) e286 e291 (by rfl)
theorem e293 : o2.add b129 b270=(List.nil : V2) := @add_cons V1 _ o1 b36 b153 (List.nil : V1) b112 b247 (List.nil : V2) (List.nil : V2) e285 e292 (by rfl)
theorem e294 : o2.add b146 b293=(List.nil : V2) := @add_cons V1 _ o1 b35 b152 (List.nil : V1) b129 b270 (List.nil : V2) (List.nil : V2) e284 e293 (by rfl)
theorem e295 : o2.add b145 b292=(List.nil : V2) := @add_cons V1 _ o1 b34 b151 (List.nil : V1) b146 b293 (List.nil : V2) (List.nil : V2) e283 e294 (by rfl)
theorem e296 : o2.add b144 b291=(List.nil : V2) := @add_cons V1 _ o1 b33 b150 (List.nil : V1) b145 b292 (List.nil : V2) (List.nil : V2) e282 e295 (by rfl)
theorem e297 : o2.add b143 b290=(List.nil : V2) := @add_cons V1 _ o1 b32 b149 (List.nil : V1) b144 b291 (List.nil : V2) (List.nil : V2) e281 e296 (by rfl)
theorem e298 : o2.add b142 b289=(List.nil : V2) := @add_cons V1 _ o1 b31 b148 (List.nil : V1) b143 b290 (List.nil : V2) (List.nil : V2) e280 e297 (by rfl)
theorem e299 : o2.add b40 b157=b295 := @add_cons V1 _ o1 b30 b147 b294 b142 b289 (List.nil : V2) b295 e279 e298 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicIntDAG
