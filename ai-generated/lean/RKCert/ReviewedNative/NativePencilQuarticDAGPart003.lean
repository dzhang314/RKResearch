module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart002

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e200 : o1.add b363 b200=b185 := by decide
theorem e201 : o1.add b364 b201=b186 := by decide
theorem e202 : o1.add b365 b202=b187 := by decide
theorem e203 : o1.add b366 b203=b188 := by decide
theorem e204 : o1.add b367 b204=b189 := by decide
theorem e205 : o1.add b368 b205=b190 := by decide
theorem e206 : o1.add b369 b206=b106 := by decide
theorem e207 : o2.add (List.nil : V2) b355=b355 := by rfl
theorem e208 : o2.add b384 b354=b399 := @add_cons V1 _ o1 b369 b206 b106 (List.nil : V2) b355 b355 b399 e206 e207 (by rfl)
theorem e209 : o2.add b383 b353=b398 := @add_cons V1 _ o1 b368 b205 b190 b384 b354 b399 b398 e205 e208 (by rfl)
theorem e210 : o2.add b382 b352=b397 := @add_cons V1 _ o1 b367 b204 b189 b383 b353 b398 b397 e204 e209 (by rfl)
theorem e211 : o2.add b381 b351=b396 := @add_cons V1 _ o1 b366 b203 b188 b382 b352 b397 b396 e203 e210 (by rfl)
theorem e212 : o2.add b380 b350=b395 := @add_cons V1 _ o1 b365 b202 b187 b381 b351 b396 b395 e202 e211 (by rfl)
theorem e213 : o2.add b379 b349=b394 := @add_cons V1 _ o1 b364 b201 b186 b380 b350 b395 b394 e201 e212 (by rfl)
theorem e214 : o2.add b378 b348=b393 := @add_cons V1 _ o1 b363 b200 b185 b379 b349 b394 b393 e200 e213 (by rfl)
theorem e215 : o2.add b377 b347=b392 := @add_cons V1 _ o1 b362 b199 b184 b378 b348 b393 b392 e199 e214 (by rfl)
theorem e216 : o2.add b376 b346=b391 := @add_cons V1 _ o1 b361 b198 b183 b377 b347 b392 b391 e198 e215 (by rfl)
theorem e217 : o2.add b375 b345=b390 := @add_cons V1 _ o1 b360 b197 b182 b376 b346 b391 b390 e197 e216 (by rfl)
theorem e218 : o2.add b374 b344=b389 := @add_cons V1 _ o1 b359 b196 b181 b375 b345 b390 b389 e196 e217 (by rfl)
theorem e219 : o2.add b373 b343=b388 := @add_cons V1 _ o1 b358 b195 b180 b374 b344 b389 b388 e195 e218 (by rfl)
theorem e220 : o2.add b372 b342=b387 := @add_cons V1 _ o1 b357 b194 b179 b373 b343 b388 b387 e194 e219 (by rfl)
theorem e221 : o2.add b371 b207=b386 := @add_cons V1 _ o1 b356 b193 b178 b372 b342 b387 b386 e193 e220 (by rfl)
theorem e222 : o2.add b370 b385=b191 := @add_cons V1 _ o1 b177 (List.nil : V1) b177 b371 b207 b386 b191 e192 e221 (by rfl)
theorem e223 : o2.mul b176 b33=b191 := @mul_cons V1 _ o1 b40 b192 b33 b207 b370 b385 b191 e160 e191 (by rfl) e222
theorem e224 : o1.mul b39 b18=b161 := by decide
theorem e225 : o1.mul b39 b19=b400 := by decide
theorem e226 : o1.mul b39 b20=b401 := by decide
theorem e227 : o1.mul b39 b21=b402 := by decide
theorem e228 : o1.mul b39 b22=b403 := by decide
theorem e229 : o1.mul b39 b23=b404 := by decide
theorem e230 : o1.mul b39 b24=b405 := by decide
theorem e231 : o1.mul b39 b25=b406 := by decide
theorem e232 : o1.mul b39 b26=b407 := by decide
theorem e233 : o1.mul b39 b27=b408 := by decide
theorem e234 : o1.mul b39 b28=b409 := by decide
theorem e235 : o1.mul b39 b29=b410 := by decide
theorem e236 : o1.mul b39 b30=b411 := by decide
theorem e237 : o1.mul b39 b31=b412 := by decide
theorem e238 : o1.mul b39 b32=b413 := by decide
theorem e239 : o1.scale b39 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e240 : o1.scale b39 b266=b428 := @scale_cons V1 _ o1 b39 b32 b413 (List.nil : V2) (List.nil : V2) b428 e238 e239 (by rfl)
theorem e241 : o1.scale b39 b264=b427 := @scale_cons V1 _ o1 b39 b31 b412 b266 b428 b427 e237 e240 (by rfl)
theorem e242 : o1.scale b39 b262=b426 := @scale_cons V1 _ o1 b39 b30 b411 b264 b427 b426 e236 e241 (by rfl)
theorem e243 : o1.scale b39 b260=b425 := @scale_cons V1 _ o1 b39 b29 b410 b262 b426 b425 e235 e242 (by rfl)
theorem e244 : o1.scale b39 b258=b424 := @scale_cons V1 _ o1 b39 b28 b409 b260 b425 b424 e234 e243 (by rfl)
theorem e245 : o1.scale b39 b256=b423 := @scale_cons V1 _ o1 b39 b27 b408 b258 b424 b423 e233 e244 (by rfl)
theorem e246 : o1.scale b39 b254=b422 := @scale_cons V1 _ o1 b39 b26 b407 b256 b423 b422 e232 e245 (by rfl)
theorem e247 : o1.scale b39 b252=b421 := @scale_cons V1 _ o1 b39 b25 b406 b254 b422 b421 e231 e246 (by rfl)
theorem e248 : o1.scale b39 b250=b420 := @scale_cons V1 _ o1 b39 b24 b405 b252 b421 b420 e230 e247 (by rfl)
theorem e249 : o1.scale b39 b248=b419 := @scale_cons V1 _ o1 b39 b23 b404 b250 b420 b419 e229 e248 (by rfl)
theorem e250 : o1.scale b39 b246=b418 := @scale_cons V1 _ o1 b39 b22 b403 b248 b419 b418 e228 e249 (by rfl)
theorem e251 : o1.scale b39 b244=b417 := @scale_cons V1 _ o1 b39 b21 b402 b246 b418 b417 e227 e250 (by rfl)
theorem e252 : o1.scale b39 b242=b416 := @scale_cons V1 _ o1 b39 b20 b401 b244 b417 b416 e226 e251 (by rfl)
theorem e253 : o1.scale b39 b240=b415 := @scale_cons V1 _ o1 b39 b19 b400 b242 b416 b415 e225 e252 (by rfl)
theorem e254 : o1.scale b39 b33=b414 := @scale_cons V1 _ o1 b39 b18 b161 b240 b415 b414 e224 e253 (by rfl)
theorem e255 : o1.add b161 (List.nil : V1)=b161 := by rfl
theorem e256 : o1.add b400 b177=b162 := by decide
theorem e257 : o1.add b401 b178=b163 := by decide
theorem e258 : o1.add b402 b179=b164 := by decide
theorem e259 : o1.add b403 b180=b165 := by decide
theorem e260 : o1.add b404 b181=b166 := by decide
theorem e261 : o1.add b405 b182=b167 := by decide
theorem e262 : o1.add b406 b183=b168 := by decide
theorem e263 : o1.add b407 b184=b169 := by decide
theorem e264 : o1.add b408 b185=b170 := by decide
theorem e265 : o1.add b409 b186=b171 := by decide
theorem e266 : o1.add b410 b187=b172 := by decide
theorem e267 : o1.add b411 b188=b173 := by decide
theorem e268 : o1.add b412 b189=b174 := by decide
theorem e269 : o1.add b413 b190=b105 := by decide
theorem e270 : o2.add (List.nil : V2) b399=b399 := by rfl
theorem e271 : o2.add b428 b398=b443 := @add_cons V1 _ o1 b413 b190 b105 (List.nil : V2) b399 b399 b443 e269 e270 (by rfl)
theorem e272 : o2.add b427 b397=b442 := @add_cons V1 _ o1 b412 b189 b174 b428 b398 b443 b442 e268 e271 (by rfl)
theorem e273 : o2.add b426 b396=b441 := @add_cons V1 _ o1 b411 b188 b173 b427 b397 b442 b441 e267 e272 (by rfl)
theorem e274 : o2.add b425 b395=b440 := @add_cons V1 _ o1 b410 b187 b172 b426 b396 b441 b440 e266 e273 (by rfl)
theorem e275 : o2.add b424 b394=b439 := @add_cons V1 _ o1 b409 b186 b171 b425 b395 b440 b439 e265 e274 (by rfl)
theorem e276 : o2.add b423 b393=b438 := @add_cons V1 _ o1 b408 b185 b170 b424 b394 b439 b438 e264 e275 (by rfl)
theorem e277 : o2.add b422 b392=b437 := @add_cons V1 _ o1 b407 b184 b169 b423 b393 b438 b437 e263 e276 (by rfl)
theorem e278 : o2.add b421 b391=b436 := @add_cons V1 _ o1 b406 b183 b168 b422 b392 b437 b436 e262 e277 (by rfl)
theorem e279 : o2.add b420 b390=b435 := @add_cons V1 _ o1 b405 b182 b167 b421 b391 b436 b435 e261 e278 (by rfl)
theorem e280 : o2.add b419 b389=b434 := @add_cons V1 _ o1 b404 b181 b166 b420 b390 b435 b434 e260 e279 (by rfl)
theorem e281 : o2.add b418 b388=b433 := @add_cons V1 _ o1 b403 b180 b165 b419 b389 b434 b433 e259 e280 (by rfl)
theorem e282 : o2.add b417 b387=b432 := @add_cons V1 _ o1 b402 b179 b164 b418 b388 b433 b432 e258 e281 (by rfl)
theorem e283 : o2.add b416 b386=b431 := @add_cons V1 _ o1 b401 b178 b163 b417 b387 b432 b431 e257 e282 (by rfl)
theorem e284 : o2.add b415 b191=b430 := @add_cons V1 _ o1 b400 b177 b162 b416 b386 b431 b430 e256 e283 (by rfl)
theorem e285 : o2.add b414 b429=b175 := @add_cons V1 _ o1 b161 (List.nil : V1) b161 b415 b191 b430 b175 e255 e284 (by rfl)
theorem e286 : o2.mul b160 b33=b175 := @mul_cons V1 _ o1 b39 b176 b33 b191 b414 b429 b175 e223 e254 (by rfl) e285
theorem e287 : o1.mul b38 b18=b145 := by decide
theorem e288 : o1.mul b38 b19=b444 := by decide
theorem e289 : o1.mul b38 b20=b445 := by decide
theorem e290 : o1.mul b38 b21=b446 := by decide
theorem e291 : o1.mul b38 b22=b447 := by decide
theorem e292 : o1.mul b38 b23=b448 := by decide
theorem e293 : o1.mul b38 b24=b449 := by decide
theorem e294 : o1.mul b38 b25=b450 := by decide
theorem e295 : o1.mul b38 b26=b451 := by decide
theorem e296 : o1.mul b38 b27=b452 := by decide
theorem e297 : o1.mul b38 b28=b453 := by decide
theorem e298 : o1.mul b38 b29=b454 := by decide
theorem e299 : o1.mul b38 b30=b455 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
