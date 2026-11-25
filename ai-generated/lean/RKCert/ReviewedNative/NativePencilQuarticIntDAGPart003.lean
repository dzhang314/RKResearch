module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart002

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e200 : o1.mul b27 b4=b304 := by decide
theorem e201 : o1.mul b27 b5=b305 := by decide
theorem e202 : o1.mul b27 b6=b306 := by decide
theorem e203 : o1.mul b27 b7=b307 := by decide
theorem e204 : o1.mul b27 b8=b308 := by decide
theorem e205 : o1.mul b27 b9=b309 := by decide
theorem e206 : o1.scale b27 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e207 : o1.scale b27 b183=b319 := @scale_cons V1 _ o1 b27 b9 b309 (List.nil : V2) (List.nil : V2) b319 e205 e206 (by rfl)
theorem e208 : o1.scale b27 b181=b318 := @scale_cons V1 _ o1 b27 b8 b308 b183 b319 b318 e204 e207 (by rfl)
theorem e209 : o1.scale b27 b179=b317 := @scale_cons V1 _ o1 b27 b7 b307 b181 b318 b317 e203 e208 (by rfl)
theorem e210 : o1.scale b27 b177=b316 := @scale_cons V1 _ o1 b27 b6 b306 b179 b317 b316 e202 e209 (by rfl)
theorem e211 : o1.scale b27 b175=b315 := @scale_cons V1 _ o1 b27 b5 b305 b177 b316 b315 e201 e210 (by rfl)
theorem e212 : o1.scale b27 b173=b314 := @scale_cons V1 _ o1 b27 b4 b304 b175 b315 b314 e200 e211 (by rfl)
theorem e213 : o1.scale b27 b171=b313 := @scale_cons V1 _ o1 b27 b3 b303 b173 b314 b313 e199 e212 (by rfl)
theorem e214 : o1.scale b27 b169=b312 := @scale_cons V1 _ o1 b27 b2 b302 b171 b313 b312 e198 e213 (by rfl)
theorem e215 : o1.scale b27 b167=b311 := @scale_cons V1 _ o1 b27 b1 b301 b169 b312 b311 e197 e214 (by rfl)
theorem e216 : o1.scale b27 b10=b310 := @scale_cons V1 _ o1 b27 b0 b102 b167 b311 b310 e196 e215 (by rfl)
theorem e217 : o1.add b102 (List.nil : V1)=b102 := by rfl
theorem e218 : o1.add b301 b113=b103 := by decide
theorem e219 : o1.add b302 b114=b104 := by decide
theorem e220 : o1.add b303 b115=b105 := by decide
theorem e221 : o1.add b304 b116=b106 := by decide
theorem e222 : o1.add b305 b117=b107 := by decide
theorem e223 : o1.add b306 b118=b108 := by decide
theorem e224 : o1.add b307 b119=b109 := by decide
theorem e225 : o1.add b308 b120=b110 := by decide
theorem e226 : o1.add b309 b121=b61 := by decide
theorem e227 : o2.add (List.nil : V2) b300=b300 := by rfl
theorem e228 : o2.add b319 b299=b329 := @add_cons V1 _ o1 b309 b121 b61 (List.nil : V2) b300 b300 b329 e226 e227 (by rfl)
theorem e229 : o2.add b318 b298=b328 := @add_cons V1 _ o1 b308 b120 b110 b319 b299 b329 b328 e225 e228 (by rfl)
theorem e230 : o2.add b317 b297=b327 := @add_cons V1 _ o1 b307 b119 b109 b318 b298 b328 b327 e224 e229 (by rfl)
theorem e231 : o2.add b316 b296=b326 := @add_cons V1 _ o1 b306 b118 b108 b317 b297 b327 b326 e223 e230 (by rfl)
theorem e232 : o2.add b315 b295=b325 := @add_cons V1 _ o1 b305 b117 b107 b316 b296 b326 b325 e222 e231 (by rfl)
theorem e233 : o2.add b314 b294=b324 := @add_cons V1 _ o1 b304 b116 b106 b315 b295 b325 b324 e221 e232 (by rfl)
theorem e234 : o2.add b313 b293=b323 := @add_cons V1 _ o1 b303 b115 b105 b314 b294 b324 b323 e220 e233 (by rfl)
theorem e235 : o2.add b312 b292=b322 := @add_cons V1 _ o1 b302 b114 b104 b313 b293 b323 b322 e219 e234 (by rfl)
theorem e236 : o2.add b311 b122=b321 := @add_cons V1 _ o1 b301 b113 b103 b312 b292 b322 b321 e218 e235 (by rfl)
theorem e237 : o2.add b310 b320=b111 := @add_cons V1 _ o1 b102 (List.nil : V1) b102 b311 b122 b321 b111 e217 e236 (by rfl)
theorem e238 : o2.mul b101 b10=b111 := @mul_cons V1 _ o1 b27 b112 b10 b122 b310 b320 b111 e195 e216 (by rfl) e237
theorem e239 : o1.mul b26 b0=b91 := by decide
theorem e240 : o1.mul b26 b1=b330 := by decide
theorem e241 : o1.mul b26 b2=b331 := by decide
theorem e242 : o1.mul b26 b3=b332 := by decide
theorem e243 : o1.mul b26 b4=b333 := by decide
theorem e244 : o1.mul b26 b5=b334 := by decide
theorem e245 : o1.mul b26 b6=b335 := by decide
theorem e246 : o1.mul b26 b7=b336 := by decide
theorem e247 : o1.mul b26 b8=b337 := by decide
theorem e248 : o1.mul b26 b9=b338 := by decide
theorem e249 : o1.scale b26 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e250 : o1.scale b26 b183=b348 := @scale_cons V1 _ o1 b26 b9 b338 (List.nil : V2) (List.nil : V2) b348 e248 e249 (by rfl)
theorem e251 : o1.scale b26 b181=b347 := @scale_cons V1 _ o1 b26 b8 b337 b183 b348 b347 e247 e250 (by rfl)
theorem e252 : o1.scale b26 b179=b346 := @scale_cons V1 _ o1 b26 b7 b336 b181 b347 b346 e246 e251 (by rfl)
theorem e253 : o1.scale b26 b177=b345 := @scale_cons V1 _ o1 b26 b6 b335 b179 b346 b345 e245 e252 (by rfl)
theorem e254 : o1.scale b26 b175=b344 := @scale_cons V1 _ o1 b26 b5 b334 b177 b345 b344 e244 e253 (by rfl)
theorem e255 : o1.scale b26 b173=b343 := @scale_cons V1 _ o1 b26 b4 b333 b175 b344 b343 e243 e254 (by rfl)
theorem e256 : o1.scale b26 b171=b342 := @scale_cons V1 _ o1 b26 b3 b332 b173 b343 b342 e242 e255 (by rfl)
theorem e257 : o1.scale b26 b169=b341 := @scale_cons V1 _ o1 b26 b2 b331 b171 b342 b341 e241 e256 (by rfl)
theorem e258 : o1.scale b26 b167=b340 := @scale_cons V1 _ o1 b26 b1 b330 b169 b341 b340 e240 e257 (by rfl)
theorem e259 : o1.scale b26 b10=b339 := @scale_cons V1 _ o1 b26 b0 b91 b167 b340 b339 e239 e258 (by rfl)
theorem e260 : o1.add b91 (List.nil : V1)=b91 := by rfl
theorem e261 : o1.add b330 b102=b92 := by decide
theorem e262 : o1.add b331 b103=b93 := by decide
theorem e263 : o1.add b332 b104=b94 := by decide
theorem e264 : o1.add b333 b105=b95 := by decide
theorem e265 : o1.add b334 b106=b96 := by decide
theorem e266 : o1.add b335 b107=b97 := by decide
theorem e267 : o1.add b336 b108=b98 := by decide
theorem e268 : o1.add b337 b109=b99 := by decide
theorem e269 : o1.add b338 b110=b60 := by decide
theorem e270 : o2.add (List.nil : V2) b329=b329 := by rfl
theorem e271 : o2.add b348 b328=b358 := @add_cons V1 _ o1 b338 b110 b60 (List.nil : V2) b329 b329 b358 e269 e270 (by rfl)
theorem e272 : o2.add b347 b327=b357 := @add_cons V1 _ o1 b337 b109 b99 b348 b328 b358 b357 e268 e271 (by rfl)
theorem e273 : o2.add b346 b326=b356 := @add_cons V1 _ o1 b336 b108 b98 b347 b327 b357 b356 e267 e272 (by rfl)
theorem e274 : o2.add b345 b325=b355 := @add_cons V1 _ o1 b335 b107 b97 b346 b326 b356 b355 e266 e273 (by rfl)
theorem e275 : o2.add b344 b324=b354 := @add_cons V1 _ o1 b334 b106 b96 b345 b325 b355 b354 e265 e274 (by rfl)
theorem e276 : o2.add b343 b323=b353 := @add_cons V1 _ o1 b333 b105 b95 b344 b324 b354 b353 e264 e275 (by rfl)
theorem e277 : o2.add b342 b322=b352 := @add_cons V1 _ o1 b332 b104 b94 b343 b323 b353 b352 e263 e276 (by rfl)
theorem e278 : o2.add b341 b321=b351 := @add_cons V1 _ o1 b331 b103 b93 b342 b322 b352 b351 e262 e277 (by rfl)
theorem e279 : o2.add b340 b111=b350 := @add_cons V1 _ o1 b330 b102 b92 b341 b321 b351 b350 e261 e278 (by rfl)
theorem e280 : o2.add b339 b349=b100 := @add_cons V1 _ o1 b91 (List.nil : V1) b91 b340 b111 b350 b100 e260 e279 (by rfl)
theorem e281 : o2.mul b90 b10=b100 := @mul_cons V1 _ o1 b26 b101 b10 b111 b339 b349 b100 e238 e259 (by rfl) e280
theorem e282 : o1.mul b25 b0=b80 := by decide
theorem e283 : o1.mul b25 b1=b359 := by decide
theorem e284 : o1.mul b25 b2=b360 := by decide
theorem e285 : o1.mul b25 b3=b361 := by decide
theorem e286 : o1.mul b25 b4=b362 := by decide
theorem e287 : o1.mul b25 b5=b363 := by decide
theorem e288 : o1.mul b25 b6=b364 := by decide
theorem e289 : o1.mul b25 b7=b365 := by decide
theorem e290 : o1.mul b25 b8=b366 := by decide
theorem e291 : o1.mul b25 b9=b367 := by decide
theorem e292 : o1.scale b25 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e293 : o1.scale b25 b183=b377 := @scale_cons V1 _ o1 b25 b9 b367 (List.nil : V2) (List.nil : V2) b377 e291 e292 (by rfl)
theorem e294 : o1.scale b25 b181=b376 := @scale_cons V1 _ o1 b25 b8 b366 b183 b377 b376 e290 e293 (by rfl)
theorem e295 : o1.scale b25 b179=b375 := @scale_cons V1 _ o1 b25 b7 b365 b181 b376 b375 e289 e294 (by rfl)
theorem e296 : o1.scale b25 b177=b374 := @scale_cons V1 _ o1 b25 b6 b364 b179 b375 b374 e288 e295 (by rfl)
theorem e297 : o1.scale b25 b175=b373 := @scale_cons V1 _ o1 b25 b5 b363 b177 b374 b373 e287 e296 (by rfl)
theorem e298 : o1.scale b25 b173=b372 := @scale_cons V1 _ o1 b25 b4 b362 b175 b373 b372 e286 e297 (by rfl)
theorem e299 : o1.scale b25 b171=b371 := @scale_cons V1 _ o1 b25 b3 b361 b173 b372 b371 e285 e298 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
