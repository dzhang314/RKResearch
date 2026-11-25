module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart004

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e400 : o2.add b435 b415=b445 := @add_cons V1 _ o1 b425 b77 b57 (List.nil : V2) b416 b416 b445 e398 e399 (by rfl)
theorem e401 : o2.add b434 b414=b444 := @add_cons V1 _ o1 b424 b76 b56 b435 b415 b445 b444 e397 e400 (by rfl)
theorem e402 : o2.add b433 b413=b443 := @add_cons V1 _ o1 b423 b75 b55 b434 b414 b444 b443 e396 e401 (by rfl)
theorem e403 : o2.add b432 b412=b442 := @add_cons V1 _ o1 b422 b74 b54 b433 b413 b443 b442 e395 e402 (by rfl)
theorem e404 : o2.add b431 b411=b441 := @add_cons V1 _ o1 b421 b73 b53 b432 b412 b442 b441 e394 e403 (by rfl)
theorem e405 : o2.add b430 b410=b440 := @add_cons V1 _ o1 b420 b72 b52 b431 b411 b441 b440 e393 e404 (by rfl)
theorem e406 : o2.add b429 b409=b439 := @add_cons V1 _ o1 b419 b71 b51 b430 b410 b440 b439 e392 e405 (by rfl)
theorem e407 : o2.add b428 b408=b438 := @add_cons V1 _ o1 b418 b70 b50 b429 b409 b439 b438 e391 e406 (by rfl)
theorem e408 : o2.add b427 b78=b437 := @add_cons V1 _ o1 b417 b69 b49 b428 b408 b438 b437 e390 e407 (by rfl)
theorem e409 : o2.add b426 b436=b67 := @add_cons V1 _ o1 b48 (List.nil : V1) b48 b427 b78 b437 b67 e389 e408 (by rfl)
theorem e410 : o2.mul b33 b10=b67 := @mul_cons V1 _ o1 b23 b68 b10 b78 b426 b436 b67 e367 e388 (by rfl) e409
theorem e411 : o2.mul (List.nil : V2) b22=(List.nil : V2) := by rfl
theorem e412 : o1.mul b42 b11=b551 := by decide
theorem e413 : o1.mul b42 b12=b552 := by decide
theorem e414 : o1.mul b42 b13=b553 := by decide
theorem e415 : o1.mul b42 b14=b554 := by decide
theorem e416 : o1.mul b42 b15=b555 := by decide
theorem e417 : o1.mul b42 b16=b556 := by decide
theorem e418 : o1.mul b42 b17=b557 := by decide
theorem e419 : o1.mul b42 b18=b558 := by decide
theorem e420 : o1.mul b42 b19=b559 := by decide
theorem e421 : o1.mul b42 b20=b560 := by decide
theorem e422 : o1.mul b42 b21=b464 := by decide
theorem e423 : o1.scale b42 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e424 : o1.scale b42 b580=b581 := @scale_cons V1 _ o1 b42 b21 b464 (List.nil : V2) (List.nil : V2) b581 e422 e423 (by rfl)
theorem e425 : o1.scale b42 b578=b579 := @scale_cons V1 _ o1 b42 b20 b560 b580 b581 b579 e421 e424 (by rfl)
theorem e426 : o1.scale b42 b576=b577 := @scale_cons V1 _ o1 b42 b19 b559 b578 b579 b577 e420 e425 (by rfl)
theorem e427 : o1.scale b42 b574=b575 := @scale_cons V1 _ o1 b42 b18 b558 b576 b577 b575 e419 e426 (by rfl)
theorem e428 : o1.scale b42 b572=b573 := @scale_cons V1 _ o1 b42 b17 b557 b574 b575 b573 e418 e427 (by rfl)
theorem e429 : o1.scale b42 b570=b571 := @scale_cons V1 _ o1 b42 b16 b556 b572 b573 b571 e417 e428 (by rfl)
theorem e430 : o1.scale b42 b568=b569 := @scale_cons V1 _ o1 b42 b15 b555 b570 b571 b569 e416 e429 (by rfl)
theorem e431 : o1.scale b42 b566=b567 := @scale_cons V1 _ o1 b42 b14 b554 b568 b569 b567 e415 e430 (by rfl)
theorem e432 : o1.scale b42 b564=b565 := @scale_cons V1 _ o1 b42 b13 b553 b566 b567 b565 e414 e431 (by rfl)
theorem e433 : o1.scale b42 b562=b563 := @scale_cons V1 _ o1 b42 b12 b552 b564 b565 b563 e413 e432 (by rfl)
theorem e434 : o1.scale b42 b22=b561 := @scale_cons V1 _ o1 b42 b11 b551 b562 b563 b561 e412 e433 (by rfl)
theorem e435 : o2.add b561 (List.nil : V2)=b561 := by rfl
theorem e436 : o2.mul b550 b22=b561 := @mul_cons V1 _ o1 b42 (List.nil : V2) b22 (List.nil : V2) b561 (List.nil : V2) b561 e411 e434 (by rfl) e435
theorem e437 : o1.mul b41 b11=b539 := by decide
theorem e438 : o1.mul b41 b12=b582 := by decide
theorem e439 : o1.mul b41 b13=b583 := by decide
theorem e440 : o1.mul b41 b14=b584 := by decide
theorem e441 : o1.mul b41 b15=b585 := by decide
theorem e442 : o1.mul b41 b16=b586 := by decide
theorem e443 : o1.mul b41 b17=b587 := by decide
theorem e444 : o1.mul b41 b18=b588 := by decide
theorem e445 : o1.mul b41 b19=b589 := by decide
theorem e446 : o1.mul b41 b20=b590 := by decide
theorem e447 : o1.mul b41 b21=b591 := by decide
theorem e448 : o1.scale b41 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e449 : o1.scale b41 b580=b602 := @scale_cons V1 _ o1 b41 b21 b591 (List.nil : V2) (List.nil : V2) b602 e447 e448 (by rfl)
theorem e450 : o1.scale b41 b578=b601 := @scale_cons V1 _ o1 b41 b20 b590 b580 b602 b601 e446 e449 (by rfl)
theorem e451 : o1.scale b41 b576=b600 := @scale_cons V1 _ o1 b41 b19 b589 b578 b601 b600 e445 e450 (by rfl)
theorem e452 : o1.scale b41 b574=b599 := @scale_cons V1 _ o1 b41 b18 b588 b576 b600 b599 e444 e451 (by rfl)
theorem e453 : o1.scale b41 b572=b598 := @scale_cons V1 _ o1 b41 b17 b587 b574 b599 b598 e443 e452 (by rfl)
theorem e454 : o1.scale b41 b570=b597 := @scale_cons V1 _ o1 b41 b16 b586 b572 b598 b597 e442 e453 (by rfl)
theorem e455 : o1.scale b41 b568=b596 := @scale_cons V1 _ o1 b41 b15 b585 b570 b597 b596 e441 e454 (by rfl)
theorem e456 : o1.scale b41 b566=b595 := @scale_cons V1 _ o1 b41 b14 b584 b568 b596 b595 e440 e455 (by rfl)
theorem e457 : o1.scale b41 b564=b594 := @scale_cons V1 _ o1 b41 b13 b583 b566 b595 b594 e439 e456 (by rfl)
theorem e458 : o1.scale b41 b562=b593 := @scale_cons V1 _ o1 b41 b12 b582 b564 b594 b593 e438 e457 (by rfl)
theorem e459 : o1.scale b41 b22=b592 := @scale_cons V1 _ o1 b41 b11 b539 b562 b593 b592 e437 e458 (by rfl)
theorem e460 : o1.add b539 (List.nil : V1)=b539 := by rfl
theorem e461 : o1.add b582 b551=b540 := by decide
theorem e462 : o1.add b583 b552=b541 := by decide
theorem e463 : o1.add b584 b553=b542 := by decide
theorem e464 : o1.add b585 b554=b543 := by decide
theorem e465 : o1.add b586 b555=b544 := by decide
theorem e466 : o1.add b587 b556=b545 := by decide
theorem e467 : o1.add b588 b557=b546 := by decide
theorem e468 : o1.add b589 b558=b547 := by decide
theorem e469 : o1.add b590 b559=b548 := by decide
theorem e470 : o1.add b591 b560=b463 := by decide
theorem e471 : o2.add (List.nil : V2) b581=b581 := by rfl
theorem e472 : o2.add b602 b579=b613 := @add_cons V1 _ o1 b591 b560 b463 (List.nil : V2) b581 b581 b613 e470 e471 (by rfl)
theorem e473 : o2.add b601 b577=b612 := @add_cons V1 _ o1 b590 b559 b548 b602 b579 b613 b612 e469 e472 (by rfl)
theorem e474 : o2.add b600 b575=b611 := @add_cons V1 _ o1 b589 b558 b547 b601 b577 b612 b611 e468 e473 (by rfl)
theorem e475 : o2.add b599 b573=b610 := @add_cons V1 _ o1 b588 b557 b546 b600 b575 b611 b610 e467 e474 (by rfl)
theorem e476 : o2.add b598 b571=b609 := @add_cons V1 _ o1 b587 b556 b545 b599 b573 b610 b609 e466 e475 (by rfl)
theorem e477 : o2.add b597 b569=b608 := @add_cons V1 _ o1 b586 b555 b544 b598 b571 b609 b608 e465 e476 (by rfl)
theorem e478 : o2.add b596 b567=b607 := @add_cons V1 _ o1 b585 b554 b543 b597 b569 b608 b607 e464 e477 (by rfl)
theorem e479 : o2.add b595 b565=b606 := @add_cons V1 _ o1 b584 b553 b542 b596 b567 b607 b606 e463 e478 (by rfl)
theorem e480 : o2.add b594 b563=b605 := @add_cons V1 _ o1 b583 b552 b541 b595 b565 b606 b605 e462 e479 (by rfl)
theorem e481 : o2.add b593 b561=b604 := @add_cons V1 _ o1 b582 b551 b540 b594 b563 b605 b604 e461 e480 (by rfl)
theorem e482 : o2.add b592 b603=b549 := @add_cons V1 _ o1 b539 (List.nil : V1) b539 b593 b561 b604 b549 e460 e481 (by rfl)
theorem e483 : o2.mul b538 b22=b549 := @mul_cons V1 _ o1 b41 b550 b22 b561 b592 b603 b549 e436 e459 (by rfl) e482
theorem e484 : o1.mul b40 b11=b527 := by decide
theorem e485 : o1.mul b40 b12=b614 := by decide
theorem e486 : o1.mul b40 b13=b615 := by decide
theorem e487 : o1.mul b40 b14=b616 := by decide
theorem e488 : o1.mul b40 b15=b617 := by decide
theorem e489 : o1.mul b40 b16=b618 := by decide
theorem e490 : o1.mul b40 b17=b619 := by decide
theorem e491 : o1.mul b40 b18=b620 := by decide
theorem e492 : o1.mul b40 b19=b621 := by decide
theorem e493 : o1.mul b40 b20=b622 := by decide
theorem e494 : o1.mul b40 b21=b623 := by decide
theorem e495 : o1.scale b40 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e496 : o1.scale b40 b580=b634 := @scale_cons V1 _ o1 b40 b21 b623 (List.nil : V2) (List.nil : V2) b634 e494 e495 (by rfl)
theorem e497 : o1.scale b40 b578=b633 := @scale_cons V1 _ o1 b40 b20 b622 b580 b634 b633 e493 e496 (by rfl)
theorem e498 : o1.scale b40 b576=b632 := @scale_cons V1 _ o1 b40 b19 b621 b578 b633 b632 e492 e497 (by rfl)
theorem e499 : o1.scale b40 b574=b631 := @scale_cons V1 _ o1 b40 b18 b620 b576 b632 b631 e491 e498 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
