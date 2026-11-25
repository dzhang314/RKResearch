module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart005

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e500 : o1.scale b35 b250=b596 := @scale_cons V1 _ o1 b35 b24 b581 b252 b597 b596 e482 e499 (by rfl)
theorem e501 : o1.scale b35 b248=b595 := @scale_cons V1 _ o1 b35 b23 b580 b250 b596 b595 e481 e500 (by rfl)
theorem e502 : o1.scale b35 b246=b594 := @scale_cons V1 _ o1 b35 b22 b579 b248 b595 b594 e480 e501 (by rfl)
theorem e503 : o1.scale b35 b244=b593 := @scale_cons V1 _ o1 b35 b21 b578 b246 b594 b593 e479 e502 (by rfl)
theorem e504 : o1.scale b35 b242=b592 := @scale_cons V1 _ o1 b35 b20 b577 b244 b593 b592 e478 e503 (by rfl)
theorem e505 : o1.scale b35 b240=b591 := @scale_cons V1 _ o1 b35 b19 b576 b242 b592 b591 e477 e504 (by rfl)
theorem e506 : o1.scale b35 b33=b590 := @scale_cons V1 _ o1 b35 b18 b87 b240 b591 b590 e476 e505 (by rfl)
theorem e507 : o1.add b87 (List.nil : V1)=b87 := by rfl
theorem e508 : o1.add b576 b113=b88 := by decide
theorem e509 : o1.add b577 b114=b89 := by decide
theorem e510 : o1.add b578 b115=b90 := by decide
theorem e511 : o1.add b579 b116=b91 := by decide
theorem e512 : o1.add b580 b117=b92 := by decide
theorem e513 : o1.add b581 b118=b93 := by decide
theorem e514 : o1.add b582 b119=b94 := by decide
theorem e515 : o1.add b583 b120=b95 := by decide
theorem e516 : o1.add b584 b121=b96 := by decide
theorem e517 : o1.add b585 b122=b97 := by decide
theorem e518 : o1.add b586 b123=b98 := by decide
theorem e519 : o1.add b587 b124=b99 := by decide
theorem e520 : o1.add b588 b125=b100 := by decide
theorem e521 : o1.add b589 b126=b101 := by decide
theorem e522 : o2.add (List.nil : V2) b575=b575 := by rfl
theorem e523 : o2.add b604 b574=b619 := @add_cons V1 _ o1 b589 b126 b101 (List.nil : V2) b575 b575 b619 e521 e522 (by rfl)
theorem e524 : o2.add b603 b573=b618 := @add_cons V1 _ o1 b588 b125 b100 b604 b574 b619 b618 e520 e523 (by rfl)
theorem e525 : o2.add b602 b572=b617 := @add_cons V1 _ o1 b587 b124 b99 b603 b573 b618 b617 e519 e524 (by rfl)
theorem e526 : o2.add b601 b571=b616 := @add_cons V1 _ o1 b586 b123 b98 b602 b572 b617 b616 e518 e525 (by rfl)
theorem e527 : o2.add b600 b570=b615 := @add_cons V1 _ o1 b585 b122 b97 b601 b571 b616 b615 e517 e526 (by rfl)
theorem e528 : o2.add b599 b569=b614 := @add_cons V1 _ o1 b584 b121 b96 b600 b570 b615 b614 e516 e527 (by rfl)
theorem e529 : o2.add b598 b568=b613 := @add_cons V1 _ o1 b583 b120 b95 b599 b569 b614 b613 e515 e528 (by rfl)
theorem e530 : o2.add b597 b567=b612 := @add_cons V1 _ o1 b582 b119 b94 b598 b568 b613 b612 e514 e529 (by rfl)
theorem e531 : o2.add b596 b566=b611 := @add_cons V1 _ o1 b581 b118 b93 b597 b567 b612 b611 e513 e530 (by rfl)
theorem e532 : o2.add b595 b565=b610 := @add_cons V1 _ o1 b580 b117 b92 b596 b566 b611 b610 e512 e531 (by rfl)
theorem e533 : o2.add b594 b564=b609 := @add_cons V1 _ o1 b579 b116 b91 b595 b565 b610 b609 e511 e532 (by rfl)
theorem e534 : o2.add b593 b563=b608 := @add_cons V1 _ o1 b578 b115 b90 b594 b564 b609 b608 e510 e533 (by rfl)
theorem e535 : o2.add b592 b562=b607 := @add_cons V1 _ o1 b577 b114 b89 b593 b563 b608 b607 e509 e534 (by rfl)
theorem e536 : o2.add b591 b127=b606 := @add_cons V1 _ o1 b576 b113 b88 b592 b562 b607 b606 e508 e535 (by rfl)
theorem e537 : o2.add b590 b605=b110 := @add_cons V1 _ o1 b87 (List.nil : V1) b87 b591 b127 b606 b110 e507 e536 (by rfl)
theorem e538 : o2.mul b44 b33=b110 := @mul_cons V1 _ o1 b35 b112 b33 b127 b590 b605 b110 e475 e506 (by rfl) e537
theorem e539 : o2.scale b44 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e540 : o2.scale b44 b34=b111 := @scale_cons V2 _ o2 b44 b33 b110 (List.nil : V3) (List.nil : V3) b111 e538 e539 (by rfl)
theorem e541 : o3.add b111 (List.nil : V3)=b111 := by rfl
theorem e542 : o3.mul b45 b34=b111 := @mul_cons V2 _ o2 b44 (List.nil : V3) b34 (List.nil : V3) b111 (List.nil : V3) b111 e0 e540 (by rfl) e541
theorem e543 : o3.mul (List.nil : V3) b5=(List.nil : V3) := by rfl
theorem e544 : o2.mul (List.nil : V2) b4=(List.nil : V2) := by rfl
theorem e545 : o1.mul b68 b3=b642 := by decide
theorem e546 : o1.scale b68 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e547 : o1.scale b68 b4=b688 := @scale_cons V1 _ o1 b68 b3 b642 (List.nil : V2) (List.nil : V2) b688 e545 e546 (by rfl)
theorem e548 : o2.add b688 (List.nil : V2)=b688 := by rfl
theorem e549 : o2.mul b687 b4=b688 := @mul_cons V1 _ o1 b68 (List.nil : V2) b4 (List.nil : V2) b688 (List.nil : V2) b688 e544 e547 (by rfl) e548
theorem e550 : o1.mul b67 b3=b641 := by decide
theorem e551 : o1.scale b67 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e552 : o1.scale b67 b4=b689 := @scale_cons V1 _ o1 b67 b3 b641 (List.nil : V2) (List.nil : V2) b689 e550 e551 (by rfl)
theorem e553 : o1.add b641 (List.nil : V1)=b641 := by rfl
theorem e554 : o2.add (List.nil : V2) b688=b688 := by rfl
theorem e555 : o2.add b689 b690=b686 := @add_cons V1 _ o1 b641 (List.nil : V1) b641 (List.nil : V2) b688 b688 b686 e553 e554 (by rfl)
theorem e556 : o2.mul b685 b4=b686 := @mul_cons V1 _ o1 b67 b687 b4 b688 b689 b690 b686 e549 e552 (by rfl) e555
theorem e557 : o1.mul b66 b3=b640 := by decide
theorem e558 : o1.scale b66 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e559 : o1.scale b66 b4=b691 := @scale_cons V1 _ o1 b66 b3 b640 (List.nil : V2) (List.nil : V2) b691 e557 e558 (by rfl)
theorem e560 : o1.add b640 (List.nil : V1)=b640 := by rfl
theorem e561 : o2.add (List.nil : V2) b686=b686 := by rfl
theorem e562 : o2.add b691 b692=b684 := @add_cons V1 _ o1 b640 (List.nil : V1) b640 (List.nil : V2) b686 b686 b684 e560 e561 (by rfl)
theorem e563 : o2.mul b683 b4=b684 := @mul_cons V1 _ o1 b66 b685 b4 b686 b691 b692 b684 e556 e559 (by rfl) e562
theorem e564 : o1.mul b65 b3=b639 := by decide
theorem e565 : o1.scale b65 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e566 : o1.scale b65 b4=b693 := @scale_cons V1 _ o1 b65 b3 b639 (List.nil : V2) (List.nil : V2) b693 e564 e565 (by rfl)
theorem e567 : o1.add b639 (List.nil : V1)=b639 := by rfl
theorem e568 : o2.add (List.nil : V2) b684=b684 := by rfl
theorem e569 : o2.add b693 b694=b682 := @add_cons V1 _ o1 b639 (List.nil : V1) b639 (List.nil : V2) b684 b684 b682 e567 e568 (by rfl)
theorem e570 : o2.mul b681 b4=b682 := @mul_cons V1 _ o1 b65 b683 b4 b684 b693 b694 b682 e563 e566 (by rfl) e569
theorem e571 : o1.mul b64 b3=b638 := by decide
theorem e572 : o1.scale b64 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e573 : o1.scale b64 b4=b695 := @scale_cons V1 _ o1 b64 b3 b638 (List.nil : V2) (List.nil : V2) b695 e571 e572 (by rfl)
theorem e574 : o1.add b638 (List.nil : V1)=b638 := by rfl
theorem e575 : o2.add (List.nil : V2) b682=b682 := by rfl
theorem e576 : o2.add b695 b696=b680 := @add_cons V1 _ o1 b638 (List.nil : V1) b638 (List.nil : V2) b682 b682 b680 e574 e575 (by rfl)
theorem e577 : o2.mul b679 b4=b680 := @mul_cons V1 _ o1 b64 b681 b4 b682 b695 b696 b680 e570 e573 (by rfl) e576
theorem e578 : o1.mul b63 b3=b637 := by decide
theorem e579 : o1.scale b63 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e580 : o1.scale b63 b4=b697 := @scale_cons V1 _ o1 b63 b3 b637 (List.nil : V2) (List.nil : V2) b697 e578 e579 (by rfl)
theorem e581 : o1.add b637 (List.nil : V1)=b637 := by rfl
theorem e582 : o2.add (List.nil : V2) b680=b680 := by rfl
theorem e583 : o2.add b697 b698=b678 := @add_cons V1 _ o1 b637 (List.nil : V1) b637 (List.nil : V2) b680 b680 b678 e581 e582 (by rfl)
theorem e584 : o2.mul b677 b4=b678 := @mul_cons V1 _ o1 b63 b679 b4 b680 b697 b698 b678 e577 e580 (by rfl) e583
theorem e585 : o1.mul b62 b3=b636 := by decide
theorem e586 : o1.scale b62 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e587 : o1.scale b62 b4=b699 := @scale_cons V1 _ o1 b62 b3 b636 (List.nil : V2) (List.nil : V2) b699 e585 e586 (by rfl)
theorem e588 : o1.add b636 (List.nil : V1)=b636 := by rfl
theorem e589 : o2.add (List.nil : V2) b678=b678 := by rfl
theorem e590 : o2.add b699 b700=b676 := @add_cons V1 _ o1 b636 (List.nil : V1) b636 (List.nil : V2) b678 b678 b676 e588 e589 (by rfl)
theorem e591 : o2.mul b675 b4=b676 := @mul_cons V1 _ o1 b62 b677 b4 b678 b699 b700 b676 e584 e587 (by rfl) e590
theorem e592 : o1.mul b61 b3=b635 := by decide
theorem e593 : o1.scale b61 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e594 : o1.scale b61 b4=b701 := @scale_cons V1 _ o1 b61 b3 b635 (List.nil : V2) (List.nil : V2) b701 e592 e593 (by rfl)
theorem e595 : o1.add b635 (List.nil : V1)=b635 := by rfl
theorem e596 : o2.add (List.nil : V2) b676=b676 := by rfl
theorem e597 : o2.add b701 b702=b674 := @add_cons V1 _ o1 b635 (List.nil : V1) b635 (List.nil : V2) b676 b676 b674 e595 e596 (by rfl)
theorem e598 : o2.mul b673 b4=b674 := @mul_cons V1 _ o1 b61 b675 b4 b676 b701 b702 b674 e591 e594 (by rfl) e597
theorem e599 : o1.mul b60 b3=b634 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
