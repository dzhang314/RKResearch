module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart048

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e7200 : o2.add (List.nil : V2) b6493=b6493 := by rfl
theorem e7201 : o2.add b6521 b6522=b6492 := @add_cons V1 _ o1 b6362 (List.nil : V1) b6362 (List.nil : V2) b6493 b6493 b6492 e7199 e7200 (by rfl)
theorem e7202 : o2.mul b6397 b67=b6492 := @mul_cons V1 _ o1 b275 b6399 b67 b6493 b6521 b6522 b6492 e7196 e7198 (by rfl) e7201
theorem e7203 : o1.mul b274 b66=b6361 := by decide
theorem e7204 : o1.scale b274 b67=b6523 := @scale_cons V1 _ o1 b274 b66 b6361 (List.nil : V2) (List.nil : V2) b6523 e7203 e7029 (by rfl)
theorem e7205 : o1.add b6361 (List.nil : V1)=b6361 := by rfl
theorem e7206 : o2.add (List.nil : V2) b6492=b6492 := by rfl
theorem e7207 : o2.add b6523 b6524=b6491 := @add_cons V1 _ o1 b6361 (List.nil : V1) b6361 (List.nil : V2) b6492 b6492 b6491 e7205 e7206 (by rfl)
theorem e7208 : o2.mul b6395 b67=b6491 := @mul_cons V1 _ o1 b274 b6397 b67 b6492 b6523 b6524 b6491 e7202 e7204 (by rfl) e7207
theorem e7209 : o1.mul b273 b66=b6360 := by decide
theorem e7210 : o1.scale b273 b67=b6525 := @scale_cons V1 _ o1 b273 b66 b6360 (List.nil : V2) (List.nil : V2) b6525 e7209 e7036 (by rfl)
theorem e7211 : o1.add b6360 (List.nil : V1)=b6360 := by rfl
theorem e7212 : o2.add (List.nil : V2) b6491=b6491 := by rfl
theorem e7213 : o2.add b6525 b6526=b6490 := @add_cons V1 _ o1 b6360 (List.nil : V1) b6360 (List.nil : V2) b6491 b6491 b6490 e7211 e7212 (by rfl)
theorem e7214 : o2.mul b6393 b67=b6490 := @mul_cons V1 _ o1 b273 b6395 b67 b6491 b6525 b6526 b6490 e7208 e7210 (by rfl) e7213
theorem e7215 : o1.mul b272 b66=b5263 := by decide
theorem e7216 : o1.scale b272 b67=b6527 := @scale_cons V1 _ o1 b272 b66 b5263 (List.nil : V2) (List.nil : V2) b6527 e7215 e7043 (by rfl)
theorem e7217 : o1.add b5263 (List.nil : V1)=b5263 := by rfl
theorem e7218 : o2.add (List.nil : V2) b6490=b6490 := by rfl
theorem e7219 : o2.add b6527 b6528=b6489 := @add_cons V1 _ o1 b5263 (List.nil : V1) b5263 (List.nil : V2) b6490 b6490 b6489 e7217 e7218 (by rfl)
theorem e7220 : o2.mul b6391 b67=b6489 := @mul_cons V1 _ o1 b272 b6393 b67 b6490 b6527 b6528 b6489 e7214 e7216 (by rfl) e7219
theorem e7221 : o2.add (List.nil : V2) b6488=b6488 := by rfl
theorem e7222 : o2.mul b6389 b67=b6488 := @mul_cons V1 _ o1 (List.nil : V1) b6391 b67 b6489 (List.nil : V2) b6488 b6488 e7220 e5609 (by rfl) e7221
theorem e7223 : o2.add (List.nil : V2) b6373=b6373 := by rfl
theorem e7224 : o2.mul b286 b67=b6373 := @mul_cons V1 _ o1 (List.nil : V1) b6389 b67 b6488 (List.nil : V2) b6373 b6373 e7222 e5609 (by rfl) e7223
theorem e7225 : o1.mul b285 b68=b6386 := by decide
theorem e7226 : o1.scale b285 b69=b6544 := @scale_cons V1 _ o1 b285 b68 b6386 (List.nil : V2) (List.nil : V2) b6544 e7225 e6954 (by rfl)
theorem e7227 : o2.add b6544 (List.nil : V2)=b6544 := by rfl
theorem e7228 : o2.mul b6417 b69=b6544 := @mul_cons V1 _ o1 b285 (List.nil : V2) b69 (List.nil : V2) b6544 (List.nil : V2) b6544 e5622 e7226 (by rfl) e7227
theorem e7229 : o1.mul b284 b68=b6385 := by decide
theorem e7230 : o1.scale b284 b69=b6545 := @scale_cons V1 _ o1 b284 b68 b6385 (List.nil : V2) (List.nil : V2) b6545 e7229 e6959 (by rfl)
theorem e7231 : o1.add b6385 (List.nil : V1)=b6385 := by rfl
theorem e7232 : o2.add (List.nil : V2) b6544=b6544 := by rfl
theorem e7233 : o2.add b6545 b6546=b6543 := @add_cons V1 _ o1 b6385 (List.nil : V1) b6385 (List.nil : V2) b6544 b6544 b6543 e7231 e7232 (by rfl)
theorem e7234 : o2.mul b6415 b69=b6543 := @mul_cons V1 _ o1 b284 b6417 b69 b6544 b6545 b6546 b6543 e7228 e7230 (by rfl) e7233
theorem e7235 : o1.mul b283 b68=b6384 := by decide
theorem e7236 : o1.scale b283 b69=b6547 := @scale_cons V1 _ o1 b283 b68 b6384 (List.nil : V2) (List.nil : V2) b6547 e7235 e6966 (by rfl)
theorem e7237 : o1.add b6384 (List.nil : V1)=b6384 := by rfl
theorem e7238 : o2.add (List.nil : V2) b6543=b6543 := by rfl
theorem e7239 : o2.add b6547 b6548=b6542 := @add_cons V1 _ o1 b6384 (List.nil : V1) b6384 (List.nil : V2) b6543 b6543 b6542 e7237 e7238 (by rfl)
theorem e7240 : o2.mul b6413 b69=b6542 := @mul_cons V1 _ o1 b283 b6415 b69 b6543 b6547 b6548 b6542 e7234 e7236 (by rfl) e7239
theorem e7241 : o1.mul b282 b68=b6383 := by decide
theorem e7242 : o1.scale b282 b69=b6549 := @scale_cons V1 _ o1 b282 b68 b6383 (List.nil : V2) (List.nil : V2) b6549 e7241 e6973 (by rfl)
theorem e7243 : o1.add b6383 (List.nil : V1)=b6383 := by rfl
theorem e7244 : o2.add (List.nil : V2) b6542=b6542 := by rfl
theorem e7245 : o2.add b6549 b6550=b6541 := @add_cons V1 _ o1 b6383 (List.nil : V1) b6383 (List.nil : V2) b6542 b6542 b6541 e7243 e7244 (by rfl)
theorem e7246 : o2.mul b6411 b69=b6541 := @mul_cons V1 _ o1 b282 b6413 b69 b6542 b6549 b6550 b6541 e7240 e7242 (by rfl) e7245
theorem e7247 : o1.mul b281 b68=b6382 := by decide
theorem e7248 : o1.scale b281 b69=b6551 := @scale_cons V1 _ o1 b281 b68 b6382 (List.nil : V2) (List.nil : V2) b6551 e7247 e6980 (by rfl)
theorem e7249 : o1.add b6382 (List.nil : V1)=b6382 := by rfl
theorem e7250 : o2.add (List.nil : V2) b6541=b6541 := by rfl
theorem e7251 : o2.add b6551 b6552=b6540 := @add_cons V1 _ o1 b6382 (List.nil : V1) b6382 (List.nil : V2) b6541 b6541 b6540 e7249 e7250 (by rfl)
theorem e7252 : o2.mul b6409 b69=b6540 := @mul_cons V1 _ o1 b281 b6411 b69 b6541 b6551 b6552 b6540 e7246 e7248 (by rfl) e7251
theorem e7253 : o1.mul b280 b68=b6381 := by decide
theorem e7254 : o1.scale b280 b69=b6553 := @scale_cons V1 _ o1 b280 b68 b6381 (List.nil : V2) (List.nil : V2) b6553 e7253 e6987 (by rfl)
theorem e7255 : o1.add b6381 (List.nil : V1)=b6381 := by rfl
theorem e7256 : o2.add (List.nil : V2) b6540=b6540 := by rfl
theorem e7257 : o2.add b6553 b6554=b6539 := @add_cons V1 _ o1 b6381 (List.nil : V1) b6381 (List.nil : V2) b6540 b6540 b6539 e7255 e7256 (by rfl)
theorem e7258 : o2.mul b6407 b69=b6539 := @mul_cons V1 _ o1 b280 b6409 b69 b6540 b6553 b6554 b6539 e7252 e7254 (by rfl) e7257
theorem e7259 : o1.mul b279 b68=b6380 := by decide
theorem e7260 : o1.scale b279 b69=b6555 := @scale_cons V1 _ o1 b279 b68 b6380 (List.nil : V2) (List.nil : V2) b6555 e7259 e6994 (by rfl)
theorem e7261 : o1.add b6380 (List.nil : V1)=b6380 := by rfl
theorem e7262 : o2.add (List.nil : V2) b6539=b6539 := by rfl
theorem e7263 : o2.add b6555 b6556=b6538 := @add_cons V1 _ o1 b6380 (List.nil : V1) b6380 (List.nil : V2) b6539 b6539 b6538 e7261 e7262 (by rfl)
theorem e7264 : o2.mul b6405 b69=b6538 := @mul_cons V1 _ o1 b279 b6407 b69 b6539 b6555 b6556 b6538 e7258 e7260 (by rfl) e7263
theorem e7265 : o1.mul b278 b68=b6379 := by decide
theorem e7266 : o1.scale b278 b69=b6557 := @scale_cons V1 _ o1 b278 b68 b6379 (List.nil : V2) (List.nil : V2) b6557 e7265 e7001 (by rfl)
theorem e7267 : o1.add b6379 (List.nil : V1)=b6379 := by rfl
theorem e7268 : o2.add (List.nil : V2) b6538=b6538 := by rfl
theorem e7269 : o2.add b6557 b6558=b6537 := @add_cons V1 _ o1 b6379 (List.nil : V1) b6379 (List.nil : V2) b6538 b6538 b6537 e7267 e7268 (by rfl)
theorem e7270 : o2.mul b6403 b69=b6537 := @mul_cons V1 _ o1 b278 b6405 b69 b6538 b6557 b6558 b6537 e7264 e7266 (by rfl) e7269
theorem e7271 : o1.mul b277 b68=b6378 := by decide
theorem e7272 : o1.scale b277 b69=b6559 := @scale_cons V1 _ o1 b277 b68 b6378 (List.nil : V2) (List.nil : V2) b6559 e7271 e7008 (by rfl)
theorem e7273 : o1.add b6378 (List.nil : V1)=b6378 := by rfl
theorem e7274 : o2.add (List.nil : V2) b6537=b6537 := by rfl
theorem e7275 : o2.add b6559 b6560=b6536 := @add_cons V1 _ o1 b6378 (List.nil : V1) b6378 (List.nil : V2) b6537 b6537 b6536 e7273 e7274 (by rfl)
theorem e7276 : o2.mul b6401 b69=b6536 := @mul_cons V1 _ o1 b277 b6403 b69 b6537 b6559 b6560 b6536 e7270 e7272 (by rfl) e7275
theorem e7277 : o1.mul b276 b68=b6377 := by decide
theorem e7278 : o1.scale b276 b69=b6561 := @scale_cons V1 _ o1 b276 b68 b6377 (List.nil : V2) (List.nil : V2) b6561 e7277 e7015 (by rfl)
theorem e7279 : o1.add b6377 (List.nil : V1)=b6377 := by rfl
theorem e7280 : o2.add (List.nil : V2) b6536=b6536 := by rfl
theorem e7281 : o2.add b6561 b6562=b6535 := @add_cons V1 _ o1 b6377 (List.nil : V1) b6377 (List.nil : V2) b6536 b6536 b6535 e7279 e7280 (by rfl)
theorem e7282 : o2.mul b6399 b69=b6535 := @mul_cons V1 _ o1 b276 b6401 b69 b6536 b6561 b6562 b6535 e7276 e7278 (by rfl) e7281
theorem e7283 : o1.mul b275 b68=b6376 := by decide
theorem e7284 : o1.scale b275 b69=b6563 := @scale_cons V1 _ o1 b275 b68 b6376 (List.nil : V2) (List.nil : V2) b6563 e7283 e7022 (by rfl)
theorem e7285 : o1.add b6376 (List.nil : V1)=b6376 := by rfl
theorem e7286 : o2.add (List.nil : V2) b6535=b6535 := by rfl
theorem e7287 : o2.add b6563 b6564=b6534 := @add_cons V1 _ o1 b6376 (List.nil : V1) b6376 (List.nil : V2) b6535 b6535 b6534 e7285 e7286 (by rfl)
theorem e7288 : o2.mul b6397 b69=b6534 := @mul_cons V1 _ o1 b275 b6399 b69 b6535 b6563 b6564 b6534 e7282 e7284 (by rfl) e7287
theorem e7289 : o1.mul b274 b68=b6375 := by decide
theorem e7290 : o1.scale b274 b69=b6565 := @scale_cons V1 _ o1 b274 b68 b6375 (List.nil : V2) (List.nil : V2) b6565 e7289 e7029 (by rfl)
theorem e7291 : o1.add b6375 (List.nil : V1)=b6375 := by rfl
theorem e7292 : o2.add (List.nil : V2) b6534=b6534 := by rfl
theorem e7293 : o2.add b6565 b6566=b6533 := @add_cons V1 _ o1 b6375 (List.nil : V1) b6375 (List.nil : V2) b6534 b6534 b6533 e7291 e7292 (by rfl)
theorem e7294 : o2.mul b6395 b69=b6533 := @mul_cons V1 _ o1 b274 b6397 b69 b6534 b6565 b6566 b6533 e7288 e7290 (by rfl) e7293
theorem e7295 : o1.mul b273 b68=b6374 := by decide
theorem e7296 : o1.scale b273 b69=b6567 := @scale_cons V1 _ o1 b273 b68 b6374 (List.nil : V2) (List.nil : V2) b6567 e7295 e7036 (by rfl)
theorem e7297 : o1.add b6374 (List.nil : V1)=b6374 := by rfl
theorem e7298 : o2.add (List.nil : V2) b6533=b6533 := by rfl
theorem e7299 : o2.add b6567 b6568=b6532 := @add_cons V1 _ o1 b6374 (List.nil : V1) b6374 (List.nil : V2) b6533 b6533 b6532 e7297 e7298 (by rfl)
theorem e7300 : o2.mul b6393 b69=b6532 := @mul_cons V1 _ o1 b273 b6395 b69 b6533 b6567 b6568 b6532 e7294 e7296 (by rfl) e7299
theorem e7301 : o1.mul b272 b68=b5166 := by decide
theorem e7302 : o1.scale b272 b69=b6569 := @scale_cons V1 _ o1 b272 b68 b5166 (List.nil : V2) (List.nil : V2) b6569 e7301 e7043 (by rfl)
theorem e7303 : o1.add b5166 (List.nil : V1)=b5166 := by rfl
theorem e7304 : o2.add (List.nil : V2) b6532=b6532 := by rfl
theorem e7305 : o2.add b6569 b6570=b6531 := @add_cons V1 _ o1 b5166 (List.nil : V1) b5166 (List.nil : V2) b6532 b6532 b6531 e7303 e7304 (by rfl)
theorem e7306 : o2.mul b6391 b69=b6531 := @mul_cons V1 _ o1 b272 b6393 b69 b6532 b6569 b6570 b6531 e7300 e7302 (by rfl) e7305
theorem e7307 : o2.add (List.nil : V2) b6530=b6530 := by rfl
theorem e7308 : o2.mul b6389 b69=b6530 := @mul_cons V1 _ o1 (List.nil : V1) b6391 b69 b6531 (List.nil : V2) b6530 b6530 e7306 e5682 (by rfl) e7307
theorem e7309 : o2.add (List.nil : V2) b6387=b6387 := by rfl
theorem e7310 : o2.mul b286 b69=b6387 := @mul_cons V1 _ o1 (List.nil : V1) b6389 b69 b6530 (List.nil : V2) b6387 b6387 e7308 e5682 (by rfl) e7309
theorem e7311 : o2.scale b286 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e7312 : o2.scale b286 b5555=b6529 := @scale_cons V2 _ o2 b286 b69 b6387 (List.nil : V3) (List.nil : V3) b6529 e7310 e7311 (by rfl)
theorem e7313 : o2.scale b286 b5520=b6487 := @scale_cons V2 _ o2 b286 b67 b6373 b5555 b6529 b6487 e7224 e7312 (by rfl)
theorem e7314 : o2.scale b286 b5485=b6445 := @scale_cons V2 _ o2 b286 b65 b6359 b5520 b6487 b6445 e7138 e7313 (by rfl)
theorem e7315 : o2.scale b286 b70=b6388 := @scale_cons V2 _ o2 b286 b63 b5247 b5485 b6445 b6388 e7052 e7314 (by rfl)
theorem e7316 : o2.add b5247 (List.nil : V2)=b5247 := by rfl
theorem e7317 : o1.add b6346 b5280=b5249 := by decide
theorem e7318 : o1.add b6347 b5281=b5250 := by decide
theorem e7319 : o1.add b6348 b5282=b5251 := by decide
theorem e7320 : o1.add b6349 b5283=b5252 := by decide
theorem e7321 : o1.add b6350 b5284=b5253 := by decide
theorem e7322 : o1.add b6351 b5285=b5254 := by decide
theorem e7323 : o1.add b6352 b5286=b5255 := by decide
theorem e7324 : o1.add b6353 b5287=b5256 := by decide
theorem e7325 : o1.add b6354 b5288=b5257 := by decide
theorem e7326 : o1.add b6355 b5289=b5258 := by decide
theorem e7327 : o1.add b6356 b5290=b5259 := by decide
theorem e7328 : o1.add b6357 b5291=b5260 := by decide
theorem e7329 : o1.add b6358 b5292=b5261 := by decide
theorem e7330 : o2.add b6460 b6152=b6587 := @add_cons V1 _ o1 b6358 b5292 b5261 (List.nil : V2) (List.nil : V2) (List.nil : V2) b6587 e7329 e2341 (by rfl)
theorem e7331 : o2.add b6459 b6150=b6586 := @add_cons V1 _ o1 b6357 b5291 b5260 b6460 b6152 b6587 b6586 e7328 e7330 (by rfl)
theorem e7332 : o2.add b6458 b6148=b6585 := @add_cons V1 _ o1 b6356 b5290 b5259 b6459 b6150 b6586 b6585 e7327 e7331 (by rfl)
theorem e7333 : o2.add b6457 b6146=b6584 := @add_cons V1 _ o1 b6355 b5289 b5258 b6458 b6148 b6585 b6584 e7326 e7332 (by rfl)
theorem e7334 : o2.add b6456 b6144=b6583 := @add_cons V1 _ o1 b6354 b5288 b5257 b6457 b6146 b6584 b6583 e7325 e7333 (by rfl)
theorem e7335 : o2.add b6455 b6142=b6582 := @add_cons V1 _ o1 b6353 b5287 b5256 b6456 b6144 b6583 b6582 e7324 e7334 (by rfl)
theorem e7336 : o2.add b6454 b6140=b6581 := @add_cons V1 _ o1 b6352 b5286 b5255 b6455 b6142 b6582 b6581 e7323 e7335 (by rfl)
theorem e7337 : o2.add b6453 b6138=b6580 := @add_cons V1 _ o1 b6351 b5285 b5254 b6454 b6140 b6581 b6580 e7322 e7336 (by rfl)
theorem e7338 : o2.add b6452 b6136=b6579 := @add_cons V1 _ o1 b6350 b5284 b5253 b6453 b6138 b6580 b6579 e7321 e7337 (by rfl)
theorem e7339 : o2.add b6451 b6134=b6578 := @add_cons V1 _ o1 b6349 b5283 b5252 b6452 b6136 b6579 b6578 e7320 e7338 (by rfl)
theorem e7340 : o2.add b6450 b6132=b6577 := @add_cons V1 _ o1 b6348 b5282 b5251 b6451 b6134 b6578 b6577 e7319 e7339 (by rfl)
theorem e7341 : o2.add b6449 b6130=b6576 := @add_cons V1 _ o1 b6347 b5281 b5250 b6450 b6132 b6577 b6576 e7318 e7340 (by rfl)
theorem e7342 : o2.add b6448 b6128=b6575 := @add_cons V1 _ o1 b6346 b5280 b5249 b6449 b6130 b6576 b6575 e7317 e7341 (by rfl)
theorem e7343 : o2.add b6447 b6126=b6574 := @add_cons V1 _ o1 b5248 (List.nil : V1) b5248 b6448 b6128 b6575 b6574 e7131 e7342 (by rfl)
theorem e7344 : o2.add b6446 b6124=b6573 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6447 b6126 b6574 b6573 e34 e7343 (by rfl)
theorem e7345 : o2.add b6359 b5293=b5262 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6446 b6124 b6573 b5262 e34 e7344 (by rfl)
theorem e7346 : o1.add b6360 b5294=b5264 := by decide
theorem e7347 : o1.add b6361 b5295=b5265 := by decide
theorem e7348 : o1.add b6362 b5296=b5266 := by decide
theorem e7349 : o1.add b6363 b5297=b5267 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
