module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart005

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e500 : o1.scale b40 b572=b630 := @scale_cons V1 _ o1 b40 b17 b619 b574 b631 b630 e490 e499 (by rfl)
theorem e501 : o1.scale b40 b570=b629 := @scale_cons V1 _ o1 b40 b16 b618 b572 b630 b629 e489 e500 (by rfl)
theorem e502 : o1.scale b40 b568=b628 := @scale_cons V1 _ o1 b40 b15 b617 b570 b629 b628 e488 e501 (by rfl)
theorem e503 : o1.scale b40 b566=b627 := @scale_cons V1 _ o1 b40 b14 b616 b568 b628 b627 e487 e502 (by rfl)
theorem e504 : o1.scale b40 b564=b626 := @scale_cons V1 _ o1 b40 b13 b615 b566 b627 b626 e486 e503 (by rfl)
theorem e505 : o1.scale b40 b562=b625 := @scale_cons V1 _ o1 b40 b12 b614 b564 b626 b625 e485 e504 (by rfl)
theorem e506 : o1.scale b40 b22=b624 := @scale_cons V1 _ o1 b40 b11 b527 b562 b625 b624 e484 e505 (by rfl)
theorem e507 : o1.add b527 (List.nil : V1)=b527 := by rfl
theorem e508 : o1.add b614 b539=b528 := by decide
theorem e509 : o1.add b615 b540=b529 := by decide
theorem e510 : o1.add b616 b541=b530 := by decide
theorem e511 : o1.add b617 b542=b531 := by decide
theorem e512 : o1.add b618 b543=b532 := by decide
theorem e513 : o1.add b619 b544=b533 := by decide
theorem e514 : o1.add b620 b545=b534 := by decide
theorem e515 : o1.add b621 b546=b535 := by decide
theorem e516 : o1.add b622 b547=b536 := by decide
theorem e517 : o1.add b623 b548=b462 := by decide
theorem e518 : o2.add (List.nil : V2) b613=b613 := by rfl
theorem e519 : o2.add b634 b612=b645 := @add_cons V1 _ o1 b623 b548 b462 (List.nil : V2) b613 b613 b645 e517 e518 (by rfl)
theorem e520 : o2.add b633 b611=b644 := @add_cons V1 _ o1 b622 b547 b536 b634 b612 b645 b644 e516 e519 (by rfl)
theorem e521 : o2.add b632 b610=b643 := @add_cons V1 _ o1 b621 b546 b535 b633 b611 b644 b643 e515 e520 (by rfl)
theorem e522 : o2.add b631 b609=b642 := @add_cons V1 _ o1 b620 b545 b534 b632 b610 b643 b642 e514 e521 (by rfl)
theorem e523 : o2.add b630 b608=b641 := @add_cons V1 _ o1 b619 b544 b533 b631 b609 b642 b641 e513 e522 (by rfl)
theorem e524 : o2.add b629 b607=b640 := @add_cons V1 _ o1 b618 b543 b532 b630 b608 b641 b640 e512 e523 (by rfl)
theorem e525 : o2.add b628 b606=b639 := @add_cons V1 _ o1 b617 b542 b531 b629 b607 b640 b639 e511 e524 (by rfl)
theorem e526 : o2.add b627 b605=b638 := @add_cons V1 _ o1 b616 b541 b530 b628 b606 b639 b638 e510 e525 (by rfl)
theorem e527 : o2.add b626 b604=b637 := @add_cons V1 _ o1 b615 b540 b529 b627 b605 b638 b637 e509 e526 (by rfl)
theorem e528 : o2.add b625 b549=b636 := @add_cons V1 _ o1 b614 b539 b528 b626 b604 b637 b636 e508 e527 (by rfl)
theorem e529 : o2.add b624 b635=b537 := @add_cons V1 _ o1 b527 (List.nil : V1) b527 b625 b549 b636 b537 e507 e528 (by rfl)
theorem e530 : o2.mul b526 b22=b537 := @mul_cons V1 _ o1 b40 b538 b22 b549 b624 b635 b537 e483 e506 (by rfl) e529
theorem e531 : o1.mul b39 b11=b515 := by decide
theorem e532 : o1.mul b39 b12=b646 := by decide
theorem e533 : o1.mul b39 b13=b647 := by decide
theorem e534 : o1.mul b39 b14=b648 := by decide
theorem e535 : o1.mul b39 b15=b649 := by decide
theorem e536 : o1.mul b39 b16=b650 := by decide
theorem e537 : o1.mul b39 b17=b651 := by decide
theorem e538 : o1.mul b39 b18=b652 := by decide
theorem e539 : o1.mul b39 b19=b653 := by decide
theorem e540 : o1.mul b39 b20=b654 := by decide
theorem e541 : o1.mul b39 b21=b655 := by decide
theorem e542 : o1.scale b39 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e543 : o1.scale b39 b580=b666 := @scale_cons V1 _ o1 b39 b21 b655 (List.nil : V2) (List.nil : V2) b666 e541 e542 (by rfl)
theorem e544 : o1.scale b39 b578=b665 := @scale_cons V1 _ o1 b39 b20 b654 b580 b666 b665 e540 e543 (by rfl)
theorem e545 : o1.scale b39 b576=b664 := @scale_cons V1 _ o1 b39 b19 b653 b578 b665 b664 e539 e544 (by rfl)
theorem e546 : o1.scale b39 b574=b663 := @scale_cons V1 _ o1 b39 b18 b652 b576 b664 b663 e538 e545 (by rfl)
theorem e547 : o1.scale b39 b572=b662 := @scale_cons V1 _ o1 b39 b17 b651 b574 b663 b662 e537 e546 (by rfl)
theorem e548 : o1.scale b39 b570=b661 := @scale_cons V1 _ o1 b39 b16 b650 b572 b662 b661 e536 e547 (by rfl)
theorem e549 : o1.scale b39 b568=b660 := @scale_cons V1 _ o1 b39 b15 b649 b570 b661 b660 e535 e548 (by rfl)
theorem e550 : o1.scale b39 b566=b659 := @scale_cons V1 _ o1 b39 b14 b648 b568 b660 b659 e534 e549 (by rfl)
theorem e551 : o1.scale b39 b564=b658 := @scale_cons V1 _ o1 b39 b13 b647 b566 b659 b658 e533 e550 (by rfl)
theorem e552 : o1.scale b39 b562=b657 := @scale_cons V1 _ o1 b39 b12 b646 b564 b658 b657 e532 e551 (by rfl)
theorem e553 : o1.scale b39 b22=b656 := @scale_cons V1 _ o1 b39 b11 b515 b562 b657 b656 e531 e552 (by rfl)
theorem e554 : o1.add b515 (List.nil : V1)=b515 := by rfl
theorem e555 : o1.add b646 b527=b516 := by decide
theorem e556 : o1.add b647 b528=b517 := by decide
theorem e557 : o1.add b648 b529=b518 := by decide
theorem e558 : o1.add b649 b530=b519 := by decide
theorem e559 : o1.add b650 b531=b520 := by decide
theorem e560 : o1.add b651 b532=b521 := by decide
theorem e561 : o1.add b652 b533=b522 := by decide
theorem e562 : o1.add b653 b534=b523 := by decide
theorem e563 : o1.add b654 b535=b524 := by decide
theorem e564 : o1.add b655 b536=b461 := by decide
theorem e565 : o2.add (List.nil : V2) b645=b645 := by rfl
theorem e566 : o2.add b666 b644=b677 := @add_cons V1 _ o1 b655 b536 b461 (List.nil : V2) b645 b645 b677 e564 e565 (by rfl)
theorem e567 : o2.add b665 b643=b676 := @add_cons V1 _ o1 b654 b535 b524 b666 b644 b677 b676 e563 e566 (by rfl)
theorem e568 : o2.add b664 b642=b675 := @add_cons V1 _ o1 b653 b534 b523 b665 b643 b676 b675 e562 e567 (by rfl)
theorem e569 : o2.add b663 b641=b674 := @add_cons V1 _ o1 b652 b533 b522 b664 b642 b675 b674 e561 e568 (by rfl)
theorem e570 : o2.add b662 b640=b673 := @add_cons V1 _ o1 b651 b532 b521 b663 b641 b674 b673 e560 e569 (by rfl)
theorem e571 : o2.add b661 b639=b672 := @add_cons V1 _ o1 b650 b531 b520 b662 b640 b673 b672 e559 e570 (by rfl)
theorem e572 : o2.add b660 b638=b671 := @add_cons V1 _ o1 b649 b530 b519 b661 b639 b672 b671 e558 e571 (by rfl)
theorem e573 : o2.add b659 b637=b670 := @add_cons V1 _ o1 b648 b529 b518 b660 b638 b671 b670 e557 e572 (by rfl)
theorem e574 : o2.add b658 b636=b669 := @add_cons V1 _ o1 b647 b528 b517 b659 b637 b670 b669 e556 e573 (by rfl)
theorem e575 : o2.add b657 b537=b668 := @add_cons V1 _ o1 b646 b527 b516 b658 b636 b669 b668 e555 e574 (by rfl)
theorem e576 : o2.add b656 b667=b525 := @add_cons V1 _ o1 b515 (List.nil : V1) b515 b657 b537 b668 b525 e554 e575 (by rfl)
theorem e577 : o2.mul b514 b22=b525 := @mul_cons V1 _ o1 b39 b526 b22 b537 b656 b667 b525 e530 e553 (by rfl) e576
theorem e578 : o1.mul b38 b11=b503 := by decide
theorem e579 : o1.mul b38 b12=b678 := by decide
theorem e580 : o1.mul b38 b13=b679 := by decide
theorem e581 : o1.mul b38 b14=b680 := by decide
theorem e582 : o1.mul b38 b15=b681 := by decide
theorem e583 : o1.mul b38 b16=b682 := by decide
theorem e584 : o1.mul b38 b17=b683 := by decide
theorem e585 : o1.mul b38 b18=b684 := by decide
theorem e586 : o1.mul b38 b19=b685 := by decide
theorem e587 : o1.mul b38 b20=b686 := by decide
theorem e588 : o1.mul b38 b21=b687 := by decide
theorem e589 : o1.scale b38 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e590 : o1.scale b38 b580=b698 := @scale_cons V1 _ o1 b38 b21 b687 (List.nil : V2) (List.nil : V2) b698 e588 e589 (by rfl)
theorem e591 : o1.scale b38 b578=b697 := @scale_cons V1 _ o1 b38 b20 b686 b580 b698 b697 e587 e590 (by rfl)
theorem e592 : o1.scale b38 b576=b696 := @scale_cons V1 _ o1 b38 b19 b685 b578 b697 b696 e586 e591 (by rfl)
theorem e593 : o1.scale b38 b574=b695 := @scale_cons V1 _ o1 b38 b18 b684 b576 b696 b695 e585 e592 (by rfl)
theorem e594 : o1.scale b38 b572=b694 := @scale_cons V1 _ o1 b38 b17 b683 b574 b695 b694 e584 e593 (by rfl)
theorem e595 : o1.scale b38 b570=b693 := @scale_cons V1 _ o1 b38 b16 b682 b572 b694 b693 e583 e594 (by rfl)
theorem e596 : o1.scale b38 b568=b692 := @scale_cons V1 _ o1 b38 b15 b681 b570 b693 b692 e582 e595 (by rfl)
theorem e597 : o1.scale b38 b566=b691 := @scale_cons V1 _ o1 b38 b14 b680 b568 b692 b691 e581 e596 (by rfl)
theorem e598 : o1.scale b38 b564=b690 := @scale_cons V1 _ o1 b38 b13 b679 b566 b691 b690 e580 e597 (by rfl)
theorem e599 : o1.scale b38 b562=b689 := @scale_cons V1 _ o1 b38 b12 b678 b564 b690 b689 e579 e598 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
