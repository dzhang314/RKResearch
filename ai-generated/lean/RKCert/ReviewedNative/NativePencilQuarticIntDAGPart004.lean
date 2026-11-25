module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart003

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e300 : o1.scale b25 b169=b370 := @scale_cons V1 _ o1 b25 b2 b360 b171 b371 b370 e284 e299 (by rfl)
theorem e301 : o1.scale b25 b167=b369 := @scale_cons V1 _ o1 b25 b1 b359 b169 b370 b369 e283 e300 (by rfl)
theorem e302 : o1.scale b25 b10=b368 := @scale_cons V1 _ o1 b25 b0 b80 b167 b369 b368 e282 e301 (by rfl)
theorem e303 : o1.add b80 (List.nil : V1)=b80 := by rfl
theorem e304 : o1.add b359 b91=b81 := by decide
theorem e305 : o1.add b360 b92=b82 := by decide
theorem e306 : o1.add b361 b93=b83 := by decide
theorem e307 : o1.add b362 b94=b84 := by decide
theorem e308 : o1.add b363 b95=b85 := by decide
theorem e309 : o1.add b364 b96=b86 := by decide
theorem e310 : o1.add b365 b97=b87 := by decide
theorem e311 : o1.add b366 b98=b88 := by decide
theorem e312 : o1.add b367 b99=b59 := by decide
theorem e313 : o2.add (List.nil : V2) b358=b358 := by rfl
theorem e314 : o2.add b377 b357=b387 := @add_cons V1 _ o1 b367 b99 b59 (List.nil : V2) b358 b358 b387 e312 e313 (by rfl)
theorem e315 : o2.add b376 b356=b386 := @add_cons V1 _ o1 b366 b98 b88 b377 b357 b387 b386 e311 e314 (by rfl)
theorem e316 : o2.add b375 b355=b385 := @add_cons V1 _ o1 b365 b97 b87 b376 b356 b386 b385 e310 e315 (by rfl)
theorem e317 : o2.add b374 b354=b384 := @add_cons V1 _ o1 b364 b96 b86 b375 b355 b385 b384 e309 e316 (by rfl)
theorem e318 : o2.add b373 b353=b383 := @add_cons V1 _ o1 b363 b95 b85 b374 b354 b384 b383 e308 e317 (by rfl)
theorem e319 : o2.add b372 b352=b382 := @add_cons V1 _ o1 b362 b94 b84 b373 b353 b383 b382 e307 e318 (by rfl)
theorem e320 : o2.add b371 b351=b381 := @add_cons V1 _ o1 b361 b93 b83 b372 b352 b382 b381 e306 e319 (by rfl)
theorem e321 : o2.add b370 b350=b380 := @add_cons V1 _ o1 b360 b92 b82 b371 b351 b381 b380 e305 e320 (by rfl)
theorem e322 : o2.add b369 b100=b379 := @add_cons V1 _ o1 b359 b91 b81 b370 b350 b380 b379 e304 e321 (by rfl)
theorem e323 : o2.add b368 b378=b89 := @add_cons V1 _ o1 b80 (List.nil : V1) b80 b369 b100 b379 b89 e303 e322 (by rfl)
theorem e324 : o2.mul b79 b10=b89 := @mul_cons V1 _ o1 b25 b90 b10 b100 b368 b378 b89 e281 e302 (by rfl) e323
theorem e325 : o1.mul b24 b0=b69 := by decide
theorem e326 : o1.mul b24 b1=b388 := by decide
theorem e327 : o1.mul b24 b2=b389 := by decide
theorem e328 : o1.mul b24 b3=b390 := by decide
theorem e329 : o1.mul b24 b4=b391 := by decide
theorem e330 : o1.mul b24 b5=b392 := by decide
theorem e331 : o1.mul b24 b6=b393 := by decide
theorem e332 : o1.mul b24 b7=b394 := by decide
theorem e333 : o1.mul b24 b8=b395 := by decide
theorem e334 : o1.mul b24 b9=b396 := by decide
theorem e335 : o1.scale b24 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e336 : o1.scale b24 b183=b406 := @scale_cons V1 _ o1 b24 b9 b396 (List.nil : V2) (List.nil : V2) b406 e334 e335 (by rfl)
theorem e337 : o1.scale b24 b181=b405 := @scale_cons V1 _ o1 b24 b8 b395 b183 b406 b405 e333 e336 (by rfl)
theorem e338 : o1.scale b24 b179=b404 := @scale_cons V1 _ o1 b24 b7 b394 b181 b405 b404 e332 e337 (by rfl)
theorem e339 : o1.scale b24 b177=b403 := @scale_cons V1 _ o1 b24 b6 b393 b179 b404 b403 e331 e338 (by rfl)
theorem e340 : o1.scale b24 b175=b402 := @scale_cons V1 _ o1 b24 b5 b392 b177 b403 b402 e330 e339 (by rfl)
theorem e341 : o1.scale b24 b173=b401 := @scale_cons V1 _ o1 b24 b4 b391 b175 b402 b401 e329 e340 (by rfl)
theorem e342 : o1.scale b24 b171=b400 := @scale_cons V1 _ o1 b24 b3 b390 b173 b401 b400 e328 e341 (by rfl)
theorem e343 : o1.scale b24 b169=b399 := @scale_cons V1 _ o1 b24 b2 b389 b171 b400 b399 e327 e342 (by rfl)
theorem e344 : o1.scale b24 b167=b398 := @scale_cons V1 _ o1 b24 b1 b388 b169 b399 b398 e326 e343 (by rfl)
theorem e345 : o1.scale b24 b10=b397 := @scale_cons V1 _ o1 b24 b0 b69 b167 b398 b397 e325 e344 (by rfl)
theorem e346 : o1.add b69 (List.nil : V1)=b69 := by rfl
theorem e347 : o1.add b388 b80=b70 := by decide
theorem e348 : o1.add b389 b81=b71 := by decide
theorem e349 : o1.add b390 b82=b72 := by decide
theorem e350 : o1.add b391 b83=b73 := by decide
theorem e351 : o1.add b392 b84=b74 := by decide
theorem e352 : o1.add b393 b85=b75 := by decide
theorem e353 : o1.add b394 b86=b76 := by decide
theorem e354 : o1.add b395 b87=b77 := by decide
theorem e355 : o1.add b396 b88=b58 := by decide
theorem e356 : o2.add (List.nil : V2) b387=b387 := by rfl
theorem e357 : o2.add b406 b386=b416 := @add_cons V1 _ o1 b396 b88 b58 (List.nil : V2) b387 b387 b416 e355 e356 (by rfl)
theorem e358 : o2.add b405 b385=b415 := @add_cons V1 _ o1 b395 b87 b77 b406 b386 b416 b415 e354 e357 (by rfl)
theorem e359 : o2.add b404 b384=b414 := @add_cons V1 _ o1 b394 b86 b76 b405 b385 b415 b414 e353 e358 (by rfl)
theorem e360 : o2.add b403 b383=b413 := @add_cons V1 _ o1 b393 b85 b75 b404 b384 b414 b413 e352 e359 (by rfl)
theorem e361 : o2.add b402 b382=b412 := @add_cons V1 _ o1 b392 b84 b74 b403 b383 b413 b412 e351 e360 (by rfl)
theorem e362 : o2.add b401 b381=b411 := @add_cons V1 _ o1 b391 b83 b73 b402 b382 b412 b411 e350 e361 (by rfl)
theorem e363 : o2.add b400 b380=b410 := @add_cons V1 _ o1 b390 b82 b72 b401 b381 b411 b410 e349 e362 (by rfl)
theorem e364 : o2.add b399 b379=b409 := @add_cons V1 _ o1 b389 b81 b71 b400 b380 b410 b409 e348 e363 (by rfl)
theorem e365 : o2.add b398 b89=b408 := @add_cons V1 _ o1 b388 b80 b70 b399 b379 b409 b408 e347 e364 (by rfl)
theorem e366 : o2.add b397 b407=b78 := @add_cons V1 _ o1 b69 (List.nil : V1) b69 b398 b89 b408 b78 e346 e365 (by rfl)
theorem e367 : o2.mul b68 b10=b78 := @mul_cons V1 _ o1 b24 b79 b10 b89 b397 b407 b78 e324 e345 (by rfl) e366
theorem e368 : o1.mul b23 b0=b48 := by decide
theorem e369 : o1.mul b23 b1=b417 := by decide
theorem e370 : o1.mul b23 b2=b418 := by decide
theorem e371 : o1.mul b23 b3=b419 := by decide
theorem e372 : o1.mul b23 b4=b420 := by decide
theorem e373 : o1.mul b23 b5=b421 := by decide
theorem e374 : o1.mul b23 b6=b422 := by decide
theorem e375 : o1.mul b23 b7=b423 := by decide
theorem e376 : o1.mul b23 b8=b424 := by decide
theorem e377 : o1.mul b23 b9=b425 := by decide
theorem e378 : o1.scale b23 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e379 : o1.scale b23 b183=b435 := @scale_cons V1 _ o1 b23 b9 b425 (List.nil : V2) (List.nil : V2) b435 e377 e378 (by rfl)
theorem e380 : o1.scale b23 b181=b434 := @scale_cons V1 _ o1 b23 b8 b424 b183 b435 b434 e376 e379 (by rfl)
theorem e381 : o1.scale b23 b179=b433 := @scale_cons V1 _ o1 b23 b7 b423 b181 b434 b433 e375 e380 (by rfl)
theorem e382 : o1.scale b23 b177=b432 := @scale_cons V1 _ o1 b23 b6 b422 b179 b433 b432 e374 e381 (by rfl)
theorem e383 : o1.scale b23 b175=b431 := @scale_cons V1 _ o1 b23 b5 b421 b177 b432 b431 e373 e382 (by rfl)
theorem e384 : o1.scale b23 b173=b430 := @scale_cons V1 _ o1 b23 b4 b420 b175 b431 b430 e372 e383 (by rfl)
theorem e385 : o1.scale b23 b171=b429 := @scale_cons V1 _ o1 b23 b3 b419 b173 b430 b429 e371 e384 (by rfl)
theorem e386 : o1.scale b23 b169=b428 := @scale_cons V1 _ o1 b23 b2 b418 b171 b429 b428 e370 e385 (by rfl)
theorem e387 : o1.scale b23 b167=b427 := @scale_cons V1 _ o1 b23 b1 b417 b169 b428 b427 e369 e386 (by rfl)
theorem e388 : o1.scale b23 b10=b426 := @scale_cons V1 _ o1 b23 b0 b48 b167 b427 b426 e368 e387 (by rfl)
theorem e389 : o1.add b48 (List.nil : V1)=b48 := by rfl
theorem e390 : o1.add b417 b69=b49 := by decide
theorem e391 : o1.add b418 b70=b50 := by decide
theorem e392 : o1.add b419 b71=b51 := by decide
theorem e393 : o1.add b420 b72=b52 := by decide
theorem e394 : o1.add b421 b73=b53 := by decide
theorem e395 : o1.add b422 b74=b54 := by decide
theorem e396 : o1.add b423 b75=b55 := by decide
theorem e397 : o1.add b424 b76=b56 := by decide
theorem e398 : o1.add b425 b77=b57 := by decide
theorem e399 : o2.add (List.nil : V2) b416=b416 := by rfl

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
