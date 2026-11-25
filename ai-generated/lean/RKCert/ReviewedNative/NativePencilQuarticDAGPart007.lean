module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart006

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e600 : o1.scale b60 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e601 : o1.scale b60 b4=b703 := @scale_cons V1 _ o1 b60 b3 b634 (List.nil : V2) (List.nil : V2) b703 e599 e600 (by rfl)
theorem e602 : o1.add b634 (List.nil : V1)=b634 := by rfl
theorem e603 : o2.add (List.nil : V2) b674=b674 := by rfl
theorem e604 : o2.add b703 b704=b672 := @add_cons V1 _ o1 b634 (List.nil : V1) b634 (List.nil : V2) b674 b674 b672 e602 e603 (by rfl)
theorem e605 : o2.mul b671 b4=b672 := @mul_cons V1 _ o1 b60 b673 b4 b674 b703 b704 b672 e598 e601 (by rfl) e604
theorem e606 : o1.mul b59 b3=b633 := by decide
theorem e607 : o1.scale b59 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e608 : o1.scale b59 b4=b705 := @scale_cons V1 _ o1 b59 b3 b633 (List.nil : V2) (List.nil : V2) b705 e606 e607 (by rfl)
theorem e609 : o1.add b633 (List.nil : V1)=b633 := by rfl
theorem e610 : o2.add (List.nil : V2) b672=b672 := by rfl
theorem e611 : o2.add b705 b706=b670 := @add_cons V1 _ o1 b633 (List.nil : V1) b633 (List.nil : V2) b672 b672 b670 e609 e610 (by rfl)
theorem e612 : o2.mul b669 b4=b670 := @mul_cons V1 _ o1 b59 b671 b4 b672 b705 b706 b670 e605 e608 (by rfl) e611
theorem e613 : o1.mul b58 b3=b632 := by decide
theorem e614 : o1.scale b58 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e615 : o1.scale b58 b4=b707 := @scale_cons V1 _ o1 b58 b3 b632 (List.nil : V2) (List.nil : V2) b707 e613 e614 (by rfl)
theorem e616 : o1.add b632 (List.nil : V1)=b632 := by rfl
theorem e617 : o2.add (List.nil : V2) b670=b670 := by rfl
theorem e618 : o2.add b707 b708=b668 := @add_cons V1 _ o1 b632 (List.nil : V1) b632 (List.nil : V2) b670 b670 b668 e616 e617 (by rfl)
theorem e619 : o2.mul b667 b4=b668 := @mul_cons V1 _ o1 b58 b669 b4 b670 b707 b708 b668 e612 e615 (by rfl) e618
theorem e620 : o1.mul b57 b3=b631 := by decide
theorem e621 : o1.scale b57 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e622 : o1.scale b57 b4=b709 := @scale_cons V1 _ o1 b57 b3 b631 (List.nil : V2) (List.nil : V2) b709 e620 e621 (by rfl)
theorem e623 : o1.add b631 (List.nil : V1)=b631 := by rfl
theorem e624 : o2.add (List.nil : V2) b668=b668 := by rfl
theorem e625 : o2.add b709 b710=b666 := @add_cons V1 _ o1 b631 (List.nil : V1) b631 (List.nil : V2) b668 b668 b666 e623 e624 (by rfl)
theorem e626 : o2.mul b665 b4=b666 := @mul_cons V1 _ o1 b57 b667 b4 b668 b709 b710 b666 e619 e622 (by rfl) e625
theorem e627 : o1.mul b56 b3=b630 := by decide
theorem e628 : o1.scale b56 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e629 : o1.scale b56 b4=b711 := @scale_cons V1 _ o1 b56 b3 b630 (List.nil : V2) (List.nil : V2) b711 e627 e628 (by rfl)
theorem e630 : o1.add b630 (List.nil : V1)=b630 := by rfl
theorem e631 : o2.add (List.nil : V2) b666=b666 := by rfl
theorem e632 : o2.add b711 b712=b664 := @add_cons V1 _ o1 b630 (List.nil : V1) b630 (List.nil : V2) b666 b666 b664 e630 e631 (by rfl)
theorem e633 : o2.mul b663 b4=b664 := @mul_cons V1 _ o1 b56 b665 b4 b666 b711 b712 b664 e626 e629 (by rfl) e632
theorem e634 : o1.mul b55 b3=b629 := by decide
theorem e635 : o1.scale b55 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e636 : o1.scale b55 b4=b713 := @scale_cons V1 _ o1 b55 b3 b629 (List.nil : V2) (List.nil : V2) b713 e634 e635 (by rfl)
theorem e637 : o1.add b629 (List.nil : V1)=b629 := by rfl
theorem e638 : o2.add (List.nil : V2) b664=b664 := by rfl
theorem e639 : o2.add b713 b714=b662 := @add_cons V1 _ o1 b629 (List.nil : V1) b629 (List.nil : V2) b664 b664 b662 e637 e638 (by rfl)
theorem e640 : o2.mul b661 b4=b662 := @mul_cons V1 _ o1 b55 b663 b4 b664 b713 b714 b662 e633 e636 (by rfl) e639
theorem e641 : o1.mul b54 b3=b628 := by decide
theorem e642 : o1.scale b54 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e643 : o1.scale b54 b4=b715 := @scale_cons V1 _ o1 b54 b3 b628 (List.nil : V2) (List.nil : V2) b715 e641 e642 (by rfl)
theorem e644 : o1.add b628 (List.nil : V1)=b628 := by rfl
theorem e645 : o2.add (List.nil : V2) b662=b662 := by rfl
theorem e646 : o2.add b715 b716=b660 := @add_cons V1 _ o1 b628 (List.nil : V1) b628 (List.nil : V2) b662 b662 b660 e644 e645 (by rfl)
theorem e647 : o2.mul b659 b4=b660 := @mul_cons V1 _ o1 b54 b661 b4 b662 b715 b716 b660 e640 e643 (by rfl) e646
theorem e648 : o1.mul b53 b3=b627 := by decide
theorem e649 : o1.scale b53 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e650 : o1.scale b53 b4=b717 := @scale_cons V1 _ o1 b53 b3 b627 (List.nil : V2) (List.nil : V2) b717 e648 e649 (by rfl)
theorem e651 : o1.add b627 (List.nil : V1)=b627 := by rfl
theorem e652 : o2.add (List.nil : V2) b660=b660 := by rfl
theorem e653 : o2.add b717 b718=b658 := @add_cons V1 _ o1 b627 (List.nil : V1) b627 (List.nil : V2) b660 b660 b658 e651 e652 (by rfl)
theorem e654 : o2.mul b657 b4=b658 := @mul_cons V1 _ o1 b53 b659 b4 b660 b717 b718 b658 e647 e650 (by rfl) e653
theorem e655 : o1.mul b52 b3=b626 := by decide
theorem e656 : o1.scale b52 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e657 : o1.scale b52 b4=b719 := @scale_cons V1 _ o1 b52 b3 b626 (List.nil : V2) (List.nil : V2) b719 e655 e656 (by rfl)
theorem e658 : o1.add b626 (List.nil : V1)=b626 := by rfl
theorem e659 : o2.add (List.nil : V2) b658=b658 := by rfl
theorem e660 : o2.add b719 b720=b656 := @add_cons V1 _ o1 b626 (List.nil : V1) b626 (List.nil : V2) b658 b658 b656 e658 e659 (by rfl)
theorem e661 : o2.mul b655 b4=b656 := @mul_cons V1 _ o1 b52 b657 b4 b658 b719 b720 b656 e654 e657 (by rfl) e660
theorem e662 : o1.mul b51 b3=b625 := by decide
theorem e663 : o1.scale b51 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e664 : o1.scale b51 b4=b721 := @scale_cons V1 _ o1 b51 b3 b625 (List.nil : V2) (List.nil : V2) b721 e662 e663 (by rfl)
theorem e665 : o1.add b625 (List.nil : V1)=b625 := by rfl
theorem e666 : o2.add (List.nil : V2) b656=b656 := by rfl
theorem e667 : o2.add b721 b722=b654 := @add_cons V1 _ o1 b625 (List.nil : V1) b625 (List.nil : V2) b656 b656 b654 e665 e666 (by rfl)
theorem e668 : o2.mul b653 b4=b654 := @mul_cons V1 _ o1 b51 b655 b4 b656 b721 b722 b654 e661 e664 (by rfl) e667
theorem e669 : o1.mul b50 b3=b624 := by decide
theorem e670 : o1.scale b50 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e671 : o1.scale b50 b4=b723 := @scale_cons V1 _ o1 b50 b3 b624 (List.nil : V2) (List.nil : V2) b723 e669 e670 (by rfl)
theorem e672 : o1.add b624 (List.nil : V1)=b624 := by rfl
theorem e673 : o2.add (List.nil : V2) b654=b654 := by rfl
theorem e674 : o2.add b723 b724=b652 := @add_cons V1 _ o1 b624 (List.nil : V1) b624 (List.nil : V2) b654 b654 b652 e672 e673 (by rfl)
theorem e675 : o2.mul b651 b4=b652 := @mul_cons V1 _ o1 b50 b653 b4 b654 b723 b724 b652 e668 e671 (by rfl) e674
theorem e676 : o1.mul b49 b3=b623 := by decide
theorem e677 : o1.scale b49 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e678 : o1.scale b49 b4=b725 := @scale_cons V1 _ o1 b49 b3 b623 (List.nil : V2) (List.nil : V2) b725 e676 e677 (by rfl)
theorem e679 : o1.add b623 (List.nil : V1)=b623 := by rfl
theorem e680 : o2.add (List.nil : V2) b652=b652 := by rfl
theorem e681 : o2.add b725 b726=b650 := @add_cons V1 _ o1 b623 (List.nil : V1) b623 (List.nil : V2) b652 b652 b650 e679 e680 (by rfl)
theorem e682 : o2.mul b649 b4=b650 := @mul_cons V1 _ o1 b49 b651 b4 b652 b725 b726 b650 e675 e678 (by rfl) e681
theorem e683 : o1.mul b48 b3=b622 := by decide
theorem e684 : o1.scale b48 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e685 : o1.scale b48 b4=b727 := @scale_cons V1 _ o1 b48 b3 b622 (List.nil : V2) (List.nil : V2) b727 e683 e684 (by rfl)
theorem e686 : o1.add b622 (List.nil : V1)=b622 := by rfl
theorem e687 : o2.add (List.nil : V2) b650=b650 := by rfl
theorem e688 : o2.add b727 b728=b648 := @add_cons V1 _ o1 b622 (List.nil : V1) b622 (List.nil : V2) b650 b650 b648 e686 e687 (by rfl)
theorem e689 : o2.mul b647 b4=b648 := @mul_cons V1 _ o1 b48 b649 b4 b650 b727 b728 b648 e682 e685 (by rfl) e688
theorem e690 : o1.mul b47 b3=b621 := by decide
theorem e691 : o1.scale b47 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e692 : o1.scale b47 b4=b729 := @scale_cons V1 _ o1 b47 b3 b621 (List.nil : V2) (List.nil : V2) b729 e690 e691 (by rfl)
theorem e693 : o1.add b621 (List.nil : V1)=b621 := by rfl
theorem e694 : o2.add (List.nil : V2) b648=b648 := by rfl
theorem e695 : o2.add b729 b730=b646 := @add_cons V1 _ o1 b621 (List.nil : V1) b621 (List.nil : V2) b648 b648 b646 e693 e694 (by rfl)
theorem e696 : o2.mul b645 b4=b646 := @mul_cons V1 _ o1 b47 b647 b4 b648 b729 b730 b646 e689 e692 (by rfl) e695
theorem e697 : o1.mul b46 b3=b620 := by decide
theorem e698 : o1.scale b46 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e699 : o1.scale b46 b4=b731 := @scale_cons V1 _ o1 b46 b3 b620 (List.nil : V2) (List.nil : V2) b731 e697 e698 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticDAG
