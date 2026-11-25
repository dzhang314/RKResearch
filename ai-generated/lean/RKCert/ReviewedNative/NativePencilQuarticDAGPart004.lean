module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart003

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e300 : o1.mul b38 b31=b456 := by decide
theorem e301 : o1.mul b38 b32=b457 := by decide
theorem e302 : o1.scale b38 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e303 : o1.scale b38 b266=b472 := @scale_cons V1 _ o1 b38 b32 b457 (List.nil : V2) (List.nil : V2) b472 e301 e302 (by rfl)
theorem e304 : o1.scale b38 b264=b471 := @scale_cons V1 _ o1 b38 b31 b456 b266 b472 b471 e300 e303 (by rfl)
theorem e305 : o1.scale b38 b262=b470 := @scale_cons V1 _ o1 b38 b30 b455 b264 b471 b470 e299 e304 (by rfl)
theorem e306 : o1.scale b38 b260=b469 := @scale_cons V1 _ o1 b38 b29 b454 b262 b470 b469 e298 e305 (by rfl)
theorem e307 : o1.scale b38 b258=b468 := @scale_cons V1 _ o1 b38 b28 b453 b260 b469 b468 e297 e306 (by rfl)
theorem e308 : o1.scale b38 b256=b467 := @scale_cons V1 _ o1 b38 b27 b452 b258 b468 b467 e296 e307 (by rfl)
theorem e309 : o1.scale b38 b254=b466 := @scale_cons V1 _ o1 b38 b26 b451 b256 b467 b466 e295 e308 (by rfl)
theorem e310 : o1.scale b38 b252=b465 := @scale_cons V1 _ o1 b38 b25 b450 b254 b466 b465 e294 e309 (by rfl)
theorem e311 : o1.scale b38 b250=b464 := @scale_cons V1 _ o1 b38 b24 b449 b252 b465 b464 e293 e310 (by rfl)
theorem e312 : o1.scale b38 b248=b463 := @scale_cons V1 _ o1 b38 b23 b448 b250 b464 b463 e292 e311 (by rfl)
theorem e313 : o1.scale b38 b246=b462 := @scale_cons V1 _ o1 b38 b22 b447 b248 b463 b462 e291 e312 (by rfl)
theorem e314 : o1.scale b38 b244=b461 := @scale_cons V1 _ o1 b38 b21 b446 b246 b462 b461 e290 e313 (by rfl)
theorem e315 : o1.scale b38 b242=b460 := @scale_cons V1 _ o1 b38 b20 b445 b244 b461 b460 e289 e314 (by rfl)
theorem e316 : o1.scale b38 b240=b459 := @scale_cons V1 _ o1 b38 b19 b444 b242 b460 b459 e288 e315 (by rfl)
theorem e317 : o1.scale b38 b33=b458 := @scale_cons V1 _ o1 b38 b18 b145 b240 b459 b458 e287 e316 (by rfl)
theorem e318 : o1.add b145 (List.nil : V1)=b145 := by rfl
theorem e319 : o1.add b444 b161=b146 := by decide
theorem e320 : o1.add b445 b162=b147 := by decide
theorem e321 : o1.add b446 b163=b148 := by decide
theorem e322 : o1.add b447 b164=b149 := by decide
theorem e323 : o1.add b448 b165=b150 := by decide
theorem e324 : o1.add b449 b166=b151 := by decide
theorem e325 : o1.add b450 b167=b152 := by decide
theorem e326 : o1.add b451 b168=b153 := by decide
theorem e327 : o1.add b452 b169=b154 := by decide
theorem e328 : o1.add b453 b170=b155 := by decide
theorem e329 : o1.add b454 b171=b156 := by decide
theorem e330 : o1.add b455 b172=b157 := by decide
theorem e331 : o1.add b456 b173=b158 := by decide
theorem e332 : o1.add b457 b174=b104 := by decide
theorem e333 : o2.add (List.nil : V2) b443=b443 := by rfl
theorem e334 : o2.add b472 b442=b487 := @add_cons V1 _ o1 b457 b174 b104 (List.nil : V2) b443 b443 b487 e332 e333 (by rfl)
theorem e335 : o2.add b471 b441=b486 := @add_cons V1 _ o1 b456 b173 b158 b472 b442 b487 b486 e331 e334 (by rfl)
theorem e336 : o2.add b470 b440=b485 := @add_cons V1 _ o1 b455 b172 b157 b471 b441 b486 b485 e330 e335 (by rfl)
theorem e337 : o2.add b469 b439=b484 := @add_cons V1 _ o1 b454 b171 b156 b470 b440 b485 b484 e329 e336 (by rfl)
theorem e338 : o2.add b468 b438=b483 := @add_cons V1 _ o1 b453 b170 b155 b469 b439 b484 b483 e328 e337 (by rfl)
theorem e339 : o2.add b467 b437=b482 := @add_cons V1 _ o1 b452 b169 b154 b468 b438 b483 b482 e327 e338 (by rfl)
theorem e340 : o2.add b466 b436=b481 := @add_cons V1 _ o1 b451 b168 b153 b467 b437 b482 b481 e326 e339 (by rfl)
theorem e341 : o2.add b465 b435=b480 := @add_cons V1 _ o1 b450 b167 b152 b466 b436 b481 b480 e325 e340 (by rfl)
theorem e342 : o2.add b464 b434=b479 := @add_cons V1 _ o1 b449 b166 b151 b465 b435 b480 b479 e324 e341 (by rfl)
theorem e343 : o2.add b463 b433=b478 := @add_cons V1 _ o1 b448 b165 b150 b464 b434 b479 b478 e323 e342 (by rfl)
theorem e344 : o2.add b462 b432=b477 := @add_cons V1 _ o1 b447 b164 b149 b463 b433 b478 b477 e322 e343 (by rfl)
theorem e345 : o2.add b461 b431=b476 := @add_cons V1 _ o1 b446 b163 b148 b462 b432 b477 b476 e321 e344 (by rfl)
theorem e346 : o2.add b460 b430=b475 := @add_cons V1 _ o1 b445 b162 b147 b461 b431 b476 b475 e320 e345 (by rfl)
theorem e347 : o2.add b459 b175=b474 := @add_cons V1 _ o1 b444 b161 b146 b460 b430 b475 b474 e319 e346 (by rfl)
theorem e348 : o2.add b458 b473=b159 := @add_cons V1 _ o1 b145 (List.nil : V1) b145 b459 b175 b474 b159 e318 e347 (by rfl)
theorem e349 : o2.mul b144 b33=b159 := @mul_cons V1 _ o1 b38 b160 b33 b175 b458 b473 b159 e286 e317 (by rfl) e348
theorem e350 : o1.mul b37 b18=b129 := by decide
theorem e351 : o1.mul b37 b19=b488 := by decide
theorem e352 : o1.mul b37 b20=b489 := by decide
theorem e353 : o1.mul b37 b21=b490 := by decide
theorem e354 : o1.mul b37 b22=b491 := by decide
theorem e355 : o1.mul b37 b23=b492 := by decide
theorem e356 : o1.mul b37 b24=b493 := by decide
theorem e357 : o1.mul b37 b25=b494 := by decide
theorem e358 : o1.mul b37 b26=b495 := by decide
theorem e359 : o1.mul b37 b27=b496 := by decide
theorem e360 : o1.mul b37 b28=b497 := by decide
theorem e361 : o1.mul b37 b29=b498 := by decide
theorem e362 : o1.mul b37 b30=b499 := by decide
theorem e363 : o1.mul b37 b31=b500 := by decide
theorem e364 : o1.mul b37 b32=b501 := by decide
theorem e365 : o1.scale b37 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e366 : o1.scale b37 b266=b516 := @scale_cons V1 _ o1 b37 b32 b501 (List.nil : V2) (List.nil : V2) b516 e364 e365 (by rfl)
theorem e367 : o1.scale b37 b264=b515 := @scale_cons V1 _ o1 b37 b31 b500 b266 b516 b515 e363 e366 (by rfl)
theorem e368 : o1.scale b37 b262=b514 := @scale_cons V1 _ o1 b37 b30 b499 b264 b515 b514 e362 e367 (by rfl)
theorem e369 : o1.scale b37 b260=b513 := @scale_cons V1 _ o1 b37 b29 b498 b262 b514 b513 e361 e368 (by rfl)
theorem e370 : o1.scale b37 b258=b512 := @scale_cons V1 _ o1 b37 b28 b497 b260 b513 b512 e360 e369 (by rfl)
theorem e371 : o1.scale b37 b256=b511 := @scale_cons V1 _ o1 b37 b27 b496 b258 b512 b511 e359 e370 (by rfl)
theorem e372 : o1.scale b37 b254=b510 := @scale_cons V1 _ o1 b37 b26 b495 b256 b511 b510 e358 e371 (by rfl)
theorem e373 : o1.scale b37 b252=b509 := @scale_cons V1 _ o1 b37 b25 b494 b254 b510 b509 e357 e372 (by rfl)
theorem e374 : o1.scale b37 b250=b508 := @scale_cons V1 _ o1 b37 b24 b493 b252 b509 b508 e356 e373 (by rfl)
theorem e375 : o1.scale b37 b248=b507 := @scale_cons V1 _ o1 b37 b23 b492 b250 b508 b507 e355 e374 (by rfl)
theorem e376 : o1.scale b37 b246=b506 := @scale_cons V1 _ o1 b37 b22 b491 b248 b507 b506 e354 e375 (by rfl)
theorem e377 : o1.scale b37 b244=b505 := @scale_cons V1 _ o1 b37 b21 b490 b246 b506 b505 e353 e376 (by rfl)
theorem e378 : o1.scale b37 b242=b504 := @scale_cons V1 _ o1 b37 b20 b489 b244 b505 b504 e352 e377 (by rfl)
theorem e379 : o1.scale b37 b240=b503 := @scale_cons V1 _ o1 b37 b19 b488 b242 b504 b503 e351 e378 (by rfl)
theorem e380 : o1.scale b37 b33=b502 := @scale_cons V1 _ o1 b37 b18 b129 b240 b503 b502 e350 e379 (by rfl)
theorem e381 : o1.add b129 (List.nil : V1)=b129 := by rfl
theorem e382 : o1.add b488 b145=b130 := by decide
theorem e383 : o1.add b489 b146=b131 := by decide
theorem e384 : o1.add b490 b147=b132 := by decide
theorem e385 : o1.add b491 b148=b133 := by decide
theorem e386 : o1.add b492 b149=b134 := by decide
theorem e387 : o1.add b493 b150=b135 := by decide
theorem e388 : o1.add b494 b151=b136 := by decide
theorem e389 : o1.add b495 b152=b137 := by decide
theorem e390 : o1.add b496 b153=b138 := by decide
theorem e391 : o1.add b497 b154=b139 := by decide
theorem e392 : o1.add b498 b155=b140 := by decide
theorem e393 : o1.add b499 b156=b141 := by decide
theorem e394 : o1.add b500 b157=b142 := by decide
theorem e395 : o1.add b501 b158=b103 := by decide
theorem e396 : o2.add (List.nil : V2) b487=b487 := by rfl
theorem e397 : o2.add b516 b486=b531 := @add_cons V1 _ o1 b501 b158 b103 (List.nil : V2) b487 b487 b531 e395 e396 (by rfl)
theorem e398 : o2.add b515 b485=b530 := @add_cons V1 _ o1 b500 b157 b142 b516 b486 b531 b530 e394 e397 (by rfl)
theorem e399 : o2.add b514 b484=b529 := @add_cons V1 _ o1 b499 b156 b141 b515 b485 b530 b529 e393 e398 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticDAG
