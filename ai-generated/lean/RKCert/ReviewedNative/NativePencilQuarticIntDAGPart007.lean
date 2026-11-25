module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart006

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e600 : o1.scale b38 b22=b688 := @scale_cons V1 _ o1 b38 b11 b503 b562 b689 b688 e578 e599 (by rfl)
theorem e601 : o1.add b503 (List.nil : V1)=b503 := by rfl
theorem e602 : o1.add b678 b515=b504 := by decide
theorem e603 : o1.add b679 b516=b505 := by decide
theorem e604 : o1.add b680 b517=b506 := by decide
theorem e605 : o1.add b681 b518=b507 := by decide
theorem e606 : o1.add b682 b519=b508 := by decide
theorem e607 : o1.add b683 b520=b509 := by decide
theorem e608 : o1.add b684 b521=b510 := by decide
theorem e609 : o1.add b685 b522=b511 := by decide
theorem e610 : o1.add b686 b523=b512 := by decide
theorem e611 : o1.add b687 b524=b460 := by decide
theorem e612 : o2.add (List.nil : V2) b677=b677 := by rfl
theorem e613 : o2.add b698 b676=b709 := @add_cons V1 _ o1 b687 b524 b460 (List.nil : V2) b677 b677 b709 e611 e612 (by rfl)
theorem e614 : o2.add b697 b675=b708 := @add_cons V1 _ o1 b686 b523 b512 b698 b676 b709 b708 e610 e613 (by rfl)
theorem e615 : o2.add b696 b674=b707 := @add_cons V1 _ o1 b685 b522 b511 b697 b675 b708 b707 e609 e614 (by rfl)
theorem e616 : o2.add b695 b673=b706 := @add_cons V1 _ o1 b684 b521 b510 b696 b674 b707 b706 e608 e615 (by rfl)
theorem e617 : o2.add b694 b672=b705 := @add_cons V1 _ o1 b683 b520 b509 b695 b673 b706 b705 e607 e616 (by rfl)
theorem e618 : o2.add b693 b671=b704 := @add_cons V1 _ o1 b682 b519 b508 b694 b672 b705 b704 e606 e617 (by rfl)
theorem e619 : o2.add b692 b670=b703 := @add_cons V1 _ o1 b681 b518 b507 b693 b671 b704 b703 e605 e618 (by rfl)
theorem e620 : o2.add b691 b669=b702 := @add_cons V1 _ o1 b680 b517 b506 b692 b670 b703 b702 e604 e619 (by rfl)
theorem e621 : o2.add b690 b668=b701 := @add_cons V1 _ o1 b679 b516 b505 b691 b669 b702 b701 e603 e620 (by rfl)
theorem e622 : o2.add b689 b525=b700 := @add_cons V1 _ o1 b678 b515 b504 b690 b668 b701 b700 e602 e621 (by rfl)
theorem e623 : o2.add b688 b699=b513 := @add_cons V1 _ o1 b503 (List.nil : V1) b503 b689 b525 b700 b513 e601 e622 (by rfl)
theorem e624 : o2.mul b502 b22=b513 := @mul_cons V1 _ o1 b38 b514 b22 b525 b688 b699 b513 e577 e600 (by rfl) e623
theorem e625 : o1.mul b37 b11=b491 := by decide
theorem e626 : o1.mul b37 b12=b710 := by decide
theorem e627 : o1.mul b37 b13=b711 := by decide
theorem e628 : o1.mul b37 b14=b712 := by decide
theorem e629 : o1.mul b37 b15=b713 := by decide
theorem e630 : o1.mul b37 b16=b714 := by decide
theorem e631 : o1.mul b37 b17=b715 := by decide
theorem e632 : o1.mul b37 b18=b716 := by decide
theorem e633 : o1.mul b37 b19=b717 := by decide
theorem e634 : o1.mul b37 b20=b718 := by decide
theorem e635 : o1.mul b37 b21=b719 := by decide
theorem e636 : o1.scale b37 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e637 : o1.scale b37 b580=b730 := @scale_cons V1 _ o1 b37 b21 b719 (List.nil : V2) (List.nil : V2) b730 e635 e636 (by rfl)
theorem e638 : o1.scale b37 b578=b729 := @scale_cons V1 _ o1 b37 b20 b718 b580 b730 b729 e634 e637 (by rfl)
theorem e639 : o1.scale b37 b576=b728 := @scale_cons V1 _ o1 b37 b19 b717 b578 b729 b728 e633 e638 (by rfl)
theorem e640 : o1.scale b37 b574=b727 := @scale_cons V1 _ o1 b37 b18 b716 b576 b728 b727 e632 e639 (by rfl)
theorem e641 : o1.scale b37 b572=b726 := @scale_cons V1 _ o1 b37 b17 b715 b574 b727 b726 e631 e640 (by rfl)
theorem e642 : o1.scale b37 b570=b725 := @scale_cons V1 _ o1 b37 b16 b714 b572 b726 b725 e630 e641 (by rfl)
theorem e643 : o1.scale b37 b568=b724 := @scale_cons V1 _ o1 b37 b15 b713 b570 b725 b724 e629 e642 (by rfl)
theorem e644 : o1.scale b37 b566=b723 := @scale_cons V1 _ o1 b37 b14 b712 b568 b724 b723 e628 e643 (by rfl)
theorem e645 : o1.scale b37 b564=b722 := @scale_cons V1 _ o1 b37 b13 b711 b566 b723 b722 e627 e644 (by rfl)
theorem e646 : o1.scale b37 b562=b721 := @scale_cons V1 _ o1 b37 b12 b710 b564 b722 b721 e626 e645 (by rfl)
theorem e647 : o1.scale b37 b22=b720 := @scale_cons V1 _ o1 b37 b11 b491 b562 b721 b720 e625 e646 (by rfl)
theorem e648 : o1.add b491 (List.nil : V1)=b491 := by rfl
theorem e649 : o1.add b710 b503=b492 := by decide
theorem e650 : o1.add b711 b504=b493 := by decide
theorem e651 : o1.add b712 b505=b494 := by decide
theorem e652 : o1.add b713 b506=b495 := by decide
theorem e653 : o1.add b714 b507=b496 := by decide
theorem e654 : o1.add b715 b508=b497 := by decide
theorem e655 : o1.add b716 b509=b498 := by decide
theorem e656 : o1.add b717 b510=b499 := by decide
theorem e657 : o1.add b718 b511=b500 := by decide
theorem e658 : o1.add b719 b512=b459 := by decide
theorem e659 : o2.add (List.nil : V2) b709=b709 := by rfl
theorem e660 : o2.add b730 b708=b741 := @add_cons V1 _ o1 b719 b512 b459 (List.nil : V2) b709 b709 b741 e658 e659 (by rfl)
theorem e661 : o2.add b729 b707=b740 := @add_cons V1 _ o1 b718 b511 b500 b730 b708 b741 b740 e657 e660 (by rfl)
theorem e662 : o2.add b728 b706=b739 := @add_cons V1 _ o1 b717 b510 b499 b729 b707 b740 b739 e656 e661 (by rfl)
theorem e663 : o2.add b727 b705=b738 := @add_cons V1 _ o1 b716 b509 b498 b728 b706 b739 b738 e655 e662 (by rfl)
theorem e664 : o2.add b726 b704=b737 := @add_cons V1 _ o1 b715 b508 b497 b727 b705 b738 b737 e654 e663 (by rfl)
theorem e665 : o2.add b725 b703=b736 := @add_cons V1 _ o1 b714 b507 b496 b726 b704 b737 b736 e653 e664 (by rfl)
theorem e666 : o2.add b724 b702=b735 := @add_cons V1 _ o1 b713 b506 b495 b725 b703 b736 b735 e652 e665 (by rfl)
theorem e667 : o2.add b723 b701=b734 := @add_cons V1 _ o1 b712 b505 b494 b724 b702 b735 b734 e651 e666 (by rfl)
theorem e668 : o2.add b722 b700=b733 := @add_cons V1 _ o1 b711 b504 b493 b723 b701 b734 b733 e650 e667 (by rfl)
theorem e669 : o2.add b721 b513=b732 := @add_cons V1 _ o1 b710 b503 b492 b722 b700 b733 b732 e649 e668 (by rfl)
theorem e670 : o2.add b720 b731=b501 := @add_cons V1 _ o1 b491 (List.nil : V1) b491 b721 b513 b732 b501 e648 e669 (by rfl)
theorem e671 : o2.mul b490 b22=b501 := @mul_cons V1 _ o1 b37 b502 b22 b513 b720 b731 b501 e624 e647 (by rfl) e670
theorem e672 : o1.mul b36 b11=b479 := by decide
theorem e673 : o1.mul b36 b12=b742 := by decide
theorem e674 : o1.mul b36 b13=b743 := by decide
theorem e675 : o1.mul b36 b14=b744 := by decide
theorem e676 : o1.mul b36 b15=b745 := by decide
theorem e677 : o1.mul b36 b16=b746 := by decide
theorem e678 : o1.mul b36 b17=b747 := by decide
theorem e679 : o1.mul b36 b18=b748 := by decide
theorem e680 : o1.mul b36 b19=b749 := by decide
theorem e681 : o1.mul b36 b20=b750 := by decide
theorem e682 : o1.mul b36 b21=b751 := by decide
theorem e683 : o1.scale b36 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e684 : o1.scale b36 b580=b762 := @scale_cons V1 _ o1 b36 b21 b751 (List.nil : V2) (List.nil : V2) b762 e682 e683 (by rfl)
theorem e685 : o1.scale b36 b578=b761 := @scale_cons V1 _ o1 b36 b20 b750 b580 b762 b761 e681 e684 (by rfl)
theorem e686 : o1.scale b36 b576=b760 := @scale_cons V1 _ o1 b36 b19 b749 b578 b761 b760 e680 e685 (by rfl)
theorem e687 : o1.scale b36 b574=b759 := @scale_cons V1 _ o1 b36 b18 b748 b576 b760 b759 e679 e686 (by rfl)
theorem e688 : o1.scale b36 b572=b758 := @scale_cons V1 _ o1 b36 b17 b747 b574 b759 b758 e678 e687 (by rfl)
theorem e689 : o1.scale b36 b570=b757 := @scale_cons V1 _ o1 b36 b16 b746 b572 b758 b757 e677 e688 (by rfl)
theorem e690 : o1.scale b36 b568=b756 := @scale_cons V1 _ o1 b36 b15 b745 b570 b757 b756 e676 e689 (by rfl)
theorem e691 : o1.scale b36 b566=b755 := @scale_cons V1 _ o1 b36 b14 b744 b568 b756 b755 e675 e690 (by rfl)
theorem e692 : o1.scale b36 b564=b754 := @scale_cons V1 _ o1 b36 b13 b743 b566 b755 b754 e674 e691 (by rfl)
theorem e693 : o1.scale b36 b562=b753 := @scale_cons V1 _ o1 b36 b12 b742 b564 b754 b753 e673 e692 (by rfl)
theorem e694 : o1.scale b36 b22=b752 := @scale_cons V1 _ o1 b36 b11 b479 b562 b753 b752 e672 e693 (by rfl)
theorem e695 : o1.add b479 (List.nil : V1)=b479 := by rfl
theorem e696 : o1.add b742 b491=b480 := by decide
theorem e697 : o1.add b743 b492=b481 := by decide
theorem e698 : o1.add b744 b493=b482 := by decide
theorem e699 : o1.add b745 b494=b483 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
