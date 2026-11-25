module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart004

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e400 : o2.add b513 b483=b528 := @add_cons V1 _ o1 b498 b155 b140 b514 b484 b529 b528 e392 e399 (by rfl)
theorem e401 : o2.add b512 b482=b527 := @add_cons V1 _ o1 b497 b154 b139 b513 b483 b528 b527 e391 e400 (by rfl)
theorem e402 : o2.add b511 b481=b526 := @add_cons V1 _ o1 b496 b153 b138 b512 b482 b527 b526 e390 e401 (by rfl)
theorem e403 : o2.add b510 b480=b525 := @add_cons V1 _ o1 b495 b152 b137 b511 b481 b526 b525 e389 e402 (by rfl)
theorem e404 : o2.add b509 b479=b524 := @add_cons V1 _ o1 b494 b151 b136 b510 b480 b525 b524 e388 e403 (by rfl)
theorem e405 : o2.add b508 b478=b523 := @add_cons V1 _ o1 b493 b150 b135 b509 b479 b524 b523 e387 e404 (by rfl)
theorem e406 : o2.add b507 b477=b522 := @add_cons V1 _ o1 b492 b149 b134 b508 b478 b523 b522 e386 e405 (by rfl)
theorem e407 : o2.add b506 b476=b521 := @add_cons V1 _ o1 b491 b148 b133 b507 b477 b522 b521 e385 e406 (by rfl)
theorem e408 : o2.add b505 b475=b520 := @add_cons V1 _ o1 b490 b147 b132 b506 b476 b521 b520 e384 e407 (by rfl)
theorem e409 : o2.add b504 b474=b519 := @add_cons V1 _ o1 b489 b146 b131 b505 b475 b520 b519 e383 e408 (by rfl)
theorem e410 : o2.add b503 b159=b518 := @add_cons V1 _ o1 b488 b145 b130 b504 b474 b519 b518 e382 e409 (by rfl)
theorem e411 : o2.add b502 b517=b143 := @add_cons V1 _ o1 b129 (List.nil : V1) b129 b503 b159 b518 b143 e381 e410 (by rfl)
theorem e412 : o2.mul b128 b33=b143 := @mul_cons V1 _ o1 b37 b144 b33 b159 b502 b517 b143 e349 e380 (by rfl) e411
theorem e413 : o1.mul b36 b18=b113 := by decide
theorem e414 : o1.mul b36 b19=b532 := by decide
theorem e415 : o1.mul b36 b20=b533 := by decide
theorem e416 : o1.mul b36 b21=b534 := by decide
theorem e417 : o1.mul b36 b22=b535 := by decide
theorem e418 : o1.mul b36 b23=b536 := by decide
theorem e419 : o1.mul b36 b24=b537 := by decide
theorem e420 : o1.mul b36 b25=b538 := by decide
theorem e421 : o1.mul b36 b26=b539 := by decide
theorem e422 : o1.mul b36 b27=b540 := by decide
theorem e423 : o1.mul b36 b28=b541 := by decide
theorem e424 : o1.mul b36 b29=b542 := by decide
theorem e425 : o1.mul b36 b30=b543 := by decide
theorem e426 : o1.mul b36 b31=b544 := by decide
theorem e427 : o1.mul b36 b32=b545 := by decide
theorem e428 : o1.scale b36 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e429 : o1.scale b36 b266=b560 := @scale_cons V1 _ o1 b36 b32 b545 (List.nil : V2) (List.nil : V2) b560 e427 e428 (by rfl)
theorem e430 : o1.scale b36 b264=b559 := @scale_cons V1 _ o1 b36 b31 b544 b266 b560 b559 e426 e429 (by rfl)
theorem e431 : o1.scale b36 b262=b558 := @scale_cons V1 _ o1 b36 b30 b543 b264 b559 b558 e425 e430 (by rfl)
theorem e432 : o1.scale b36 b260=b557 := @scale_cons V1 _ o1 b36 b29 b542 b262 b558 b557 e424 e431 (by rfl)
theorem e433 : o1.scale b36 b258=b556 := @scale_cons V1 _ o1 b36 b28 b541 b260 b557 b556 e423 e432 (by rfl)
theorem e434 : o1.scale b36 b256=b555 := @scale_cons V1 _ o1 b36 b27 b540 b258 b556 b555 e422 e433 (by rfl)
theorem e435 : o1.scale b36 b254=b554 := @scale_cons V1 _ o1 b36 b26 b539 b256 b555 b554 e421 e434 (by rfl)
theorem e436 : o1.scale b36 b252=b553 := @scale_cons V1 _ o1 b36 b25 b538 b254 b554 b553 e420 e435 (by rfl)
theorem e437 : o1.scale b36 b250=b552 := @scale_cons V1 _ o1 b36 b24 b537 b252 b553 b552 e419 e436 (by rfl)
theorem e438 : o1.scale b36 b248=b551 := @scale_cons V1 _ o1 b36 b23 b536 b250 b552 b551 e418 e437 (by rfl)
theorem e439 : o1.scale b36 b246=b550 := @scale_cons V1 _ o1 b36 b22 b535 b248 b551 b550 e417 e438 (by rfl)
theorem e440 : o1.scale b36 b244=b549 := @scale_cons V1 _ o1 b36 b21 b534 b246 b550 b549 e416 e439 (by rfl)
theorem e441 : o1.scale b36 b242=b548 := @scale_cons V1 _ o1 b36 b20 b533 b244 b549 b548 e415 e440 (by rfl)
theorem e442 : o1.scale b36 b240=b547 := @scale_cons V1 _ o1 b36 b19 b532 b242 b548 b547 e414 e441 (by rfl)
theorem e443 : o1.scale b36 b33=b546 := @scale_cons V1 _ o1 b36 b18 b113 b240 b547 b546 e413 e442 (by rfl)
theorem e444 : o1.add b113 (List.nil : V1)=b113 := by rfl
theorem e445 : o1.add b532 b129=b114 := by decide
theorem e446 : o1.add b533 b130=b115 := by decide
theorem e447 : o1.add b534 b131=b116 := by decide
theorem e448 : o1.add b535 b132=b117 := by decide
theorem e449 : o1.add b536 b133=b118 := by decide
theorem e450 : o1.add b537 b134=b119 := by decide
theorem e451 : o1.add b538 b135=b120 := by decide
theorem e452 : o1.add b539 b136=b121 := by decide
theorem e453 : o1.add b540 b137=b122 := by decide
theorem e454 : o1.add b541 b138=b123 := by decide
theorem e455 : o1.add b542 b139=b124 := by decide
theorem e456 : o1.add b543 b140=b125 := by decide
theorem e457 : o1.add b544 b141=b126 := by decide
theorem e458 : o1.add b545 b142=b102 := by decide
theorem e459 : o2.add (List.nil : V2) b531=b531 := by rfl
theorem e460 : o2.add b560 b530=b575 := @add_cons V1 _ o1 b545 b142 b102 (List.nil : V2) b531 b531 b575 e458 e459 (by rfl)
theorem e461 : o2.add b559 b529=b574 := @add_cons V1 _ o1 b544 b141 b126 b560 b530 b575 b574 e457 e460 (by rfl)
theorem e462 : o2.add b558 b528=b573 := @add_cons V1 _ o1 b543 b140 b125 b559 b529 b574 b573 e456 e461 (by rfl)
theorem e463 : o2.add b557 b527=b572 := @add_cons V1 _ o1 b542 b139 b124 b558 b528 b573 b572 e455 e462 (by rfl)
theorem e464 : o2.add b556 b526=b571 := @add_cons V1 _ o1 b541 b138 b123 b557 b527 b572 b571 e454 e463 (by rfl)
theorem e465 : o2.add b555 b525=b570 := @add_cons V1 _ o1 b540 b137 b122 b556 b526 b571 b570 e453 e464 (by rfl)
theorem e466 : o2.add b554 b524=b569 := @add_cons V1 _ o1 b539 b136 b121 b555 b525 b570 b569 e452 e465 (by rfl)
theorem e467 : o2.add b553 b523=b568 := @add_cons V1 _ o1 b538 b135 b120 b554 b524 b569 b568 e451 e466 (by rfl)
theorem e468 : o2.add b552 b522=b567 := @add_cons V1 _ o1 b537 b134 b119 b553 b523 b568 b567 e450 e467 (by rfl)
theorem e469 : o2.add b551 b521=b566 := @add_cons V1 _ o1 b536 b133 b118 b552 b522 b567 b566 e449 e468 (by rfl)
theorem e470 : o2.add b550 b520=b565 := @add_cons V1 _ o1 b535 b132 b117 b551 b521 b566 b565 e448 e469 (by rfl)
theorem e471 : o2.add b549 b519=b564 := @add_cons V1 _ o1 b534 b131 b116 b550 b520 b565 b564 e447 e470 (by rfl)
theorem e472 : o2.add b548 b518=b563 := @add_cons V1 _ o1 b533 b130 b115 b549 b519 b564 b563 e446 e471 (by rfl)
theorem e473 : o2.add b547 b143=b562 := @add_cons V1 _ o1 b532 b129 b114 b548 b518 b563 b562 e445 e472 (by rfl)
theorem e474 : o2.add b546 b561=b127 := @add_cons V1 _ o1 b113 (List.nil : V1) b113 b547 b143 b562 b127 e444 e473 (by rfl)
theorem e475 : o2.mul b112 b33=b127 := @mul_cons V1 _ o1 b36 b128 b33 b143 b546 b561 b127 e412 e443 (by rfl) e474
theorem e476 : o1.mul b35 b18=b87 := by decide
theorem e477 : o1.mul b35 b19=b576 := by decide
theorem e478 : o1.mul b35 b20=b577 := by decide
theorem e479 : o1.mul b35 b21=b578 := by decide
theorem e480 : o1.mul b35 b22=b579 := by decide
theorem e481 : o1.mul b35 b23=b580 := by decide
theorem e482 : o1.mul b35 b24=b581 := by decide
theorem e483 : o1.mul b35 b25=b582 := by decide
theorem e484 : o1.mul b35 b26=b583 := by decide
theorem e485 : o1.mul b35 b27=b584 := by decide
theorem e486 : o1.mul b35 b28=b585 := by decide
theorem e487 : o1.mul b35 b29=b586 := by decide
theorem e488 : o1.mul b35 b30=b587 := by decide
theorem e489 : o1.mul b35 b31=b588 := by decide
theorem e490 : o1.mul b35 b32=b589 := by decide
theorem e491 : o1.scale b35 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e492 : o1.scale b35 b266=b604 := @scale_cons V1 _ o1 b35 b32 b589 (List.nil : V2) (List.nil : V2) b604 e490 e491 (by rfl)
theorem e493 : o1.scale b35 b264=b603 := @scale_cons V1 _ o1 b35 b31 b588 b266 b604 b603 e489 e492 (by rfl)
theorem e494 : o1.scale b35 b262=b602 := @scale_cons V1 _ o1 b35 b30 b587 b264 b603 b602 e488 e493 (by rfl)
theorem e495 : o1.scale b35 b260=b601 := @scale_cons V1 _ o1 b35 b29 b586 b262 b602 b601 e487 e494 (by rfl)
theorem e496 : o1.scale b35 b258=b600 := @scale_cons V1 _ o1 b35 b28 b585 b260 b601 b600 e486 e495 (by rfl)
theorem e497 : o1.scale b35 b256=b599 := @scale_cons V1 _ o1 b35 b27 b584 b258 b600 b599 e485 e496 (by rfl)
theorem e498 : o1.scale b35 b254=b598 := @scale_cons V1 _ o1 b35 b26 b583 b256 b599 b598 e484 e497 (by rfl)
theorem e499 : o1.scale b35 b252=b597 := @scale_cons V1 _ o1 b35 b25 b582 b254 b598 b597 e483 e498 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticDAG
