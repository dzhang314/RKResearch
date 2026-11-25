module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart007

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e700 : o1.add b746 b495=b484 := by decide
theorem e701 : o1.add b747 b496=b485 := by decide
theorem e702 : o1.add b748 b497=b486 := by decide
theorem e703 : o1.add b749 b498=b487 := by decide
theorem e704 : o1.add b750 b499=b488 := by decide
theorem e705 : o1.add b751 b500=b458 := by decide
theorem e706 : o2.add (List.nil : V2) b741=b741 := by rfl
theorem e707 : o2.add b762 b740=b773 := @add_cons V1 _ o1 b751 b500 b458 (List.nil : V2) b741 b741 b773 e705 e706 (by rfl)
theorem e708 : o2.add b761 b739=b772 := @add_cons V1 _ o1 b750 b499 b488 b762 b740 b773 b772 e704 e707 (by rfl)
theorem e709 : o2.add b760 b738=b771 := @add_cons V1 _ o1 b749 b498 b487 b761 b739 b772 b771 e703 e708 (by rfl)
theorem e710 : o2.add b759 b737=b770 := @add_cons V1 _ o1 b748 b497 b486 b760 b738 b771 b770 e702 e709 (by rfl)
theorem e711 : o2.add b758 b736=b769 := @add_cons V1 _ o1 b747 b496 b485 b759 b737 b770 b769 e701 e710 (by rfl)
theorem e712 : o2.add b757 b735=b768 := @add_cons V1 _ o1 b746 b495 b484 b758 b736 b769 b768 e700 e711 (by rfl)
theorem e713 : o2.add b756 b734=b767 := @add_cons V1 _ o1 b745 b494 b483 b757 b735 b768 b767 e699 e712 (by rfl)
theorem e714 : o2.add b755 b733=b766 := @add_cons V1 _ o1 b744 b493 b482 b756 b734 b767 b766 e698 e713 (by rfl)
theorem e715 : o2.add b754 b732=b765 := @add_cons V1 _ o1 b743 b492 b481 b755 b733 b766 b765 e697 e714 (by rfl)
theorem e716 : o2.add b753 b501=b764 := @add_cons V1 _ o1 b742 b491 b480 b754 b732 b765 b764 e696 e715 (by rfl)
theorem e717 : o2.add b752 b763=b489 := @add_cons V1 _ o1 b479 (List.nil : V1) b479 b753 b501 b764 b489 e695 e716 (by rfl)
theorem e718 : o2.mul b478 b22=b489 := @mul_cons V1 _ o1 b36 b490 b22 b501 b752 b763 b489 e671 e694 (by rfl) e717
theorem e719 : o1.mul b35 b11=b467 := by decide
theorem e720 : o1.mul b35 b12=b774 := by decide
theorem e721 : o1.mul b35 b13=b775 := by decide
theorem e722 : o1.mul b35 b14=b776 := by decide
theorem e723 : o1.mul b35 b15=b777 := by decide
theorem e724 : o1.mul b35 b16=b778 := by decide
theorem e725 : o1.mul b35 b17=b779 := by decide
theorem e726 : o1.mul b35 b18=b780 := by decide
theorem e727 : o1.mul b35 b19=b781 := by decide
theorem e728 : o1.mul b35 b20=b782 := by decide
theorem e729 : o1.mul b35 b21=b783 := by decide
theorem e730 : o1.scale b35 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e731 : o1.scale b35 b580=b794 := @scale_cons V1 _ o1 b35 b21 b783 (List.nil : V2) (List.nil : V2) b794 e729 e730 (by rfl)
theorem e732 : o1.scale b35 b578=b793 := @scale_cons V1 _ o1 b35 b20 b782 b580 b794 b793 e728 e731 (by rfl)
theorem e733 : o1.scale b35 b576=b792 := @scale_cons V1 _ o1 b35 b19 b781 b578 b793 b792 e727 e732 (by rfl)
theorem e734 : o1.scale b35 b574=b791 := @scale_cons V1 _ o1 b35 b18 b780 b576 b792 b791 e726 e733 (by rfl)
theorem e735 : o1.scale b35 b572=b790 := @scale_cons V1 _ o1 b35 b17 b779 b574 b791 b790 e725 e734 (by rfl)
theorem e736 : o1.scale b35 b570=b789 := @scale_cons V1 _ o1 b35 b16 b778 b572 b790 b789 e724 e735 (by rfl)
theorem e737 : o1.scale b35 b568=b788 := @scale_cons V1 _ o1 b35 b15 b777 b570 b789 b788 e723 e736 (by rfl)
theorem e738 : o1.scale b35 b566=b787 := @scale_cons V1 _ o1 b35 b14 b776 b568 b788 b787 e722 e737 (by rfl)
theorem e739 : o1.scale b35 b564=b786 := @scale_cons V1 _ o1 b35 b13 b775 b566 b787 b786 e721 e738 (by rfl)
theorem e740 : o1.scale b35 b562=b785 := @scale_cons V1 _ o1 b35 b12 b774 b564 b786 b785 e720 e739 (by rfl)
theorem e741 : o1.scale b35 b22=b784 := @scale_cons V1 _ o1 b35 b11 b467 b562 b785 b784 e719 e740 (by rfl)
theorem e742 : o1.add b467 (List.nil : V1)=b467 := by rfl
theorem e743 : o1.add b774 b479=b468 := by decide
theorem e744 : o1.add b775 b480=b469 := by decide
theorem e745 : o1.add b776 b481=b470 := by decide
theorem e746 : o1.add b777 b482=b471 := by decide
theorem e747 : o1.add b778 b483=b472 := by decide
theorem e748 : o1.add b779 b484=b473 := by decide
theorem e749 : o1.add b780 b485=b474 := by decide
theorem e750 : o1.add b781 b486=b475 := by decide
theorem e751 : o1.add b782 b487=b476 := by decide
theorem e752 : o1.add b783 b488=b457 := by decide
theorem e753 : o2.add (List.nil : V2) b773=b773 := by rfl
theorem e754 : o2.add b794 b772=b805 := @add_cons V1 _ o1 b783 b488 b457 (List.nil : V2) b773 b773 b805 e752 e753 (by rfl)
theorem e755 : o2.add b793 b771=b804 := @add_cons V1 _ o1 b782 b487 b476 b794 b772 b805 b804 e751 e754 (by rfl)
theorem e756 : o2.add b792 b770=b803 := @add_cons V1 _ o1 b781 b486 b475 b793 b771 b804 b803 e750 e755 (by rfl)
theorem e757 : o2.add b791 b769=b802 := @add_cons V1 _ o1 b780 b485 b474 b792 b770 b803 b802 e749 e756 (by rfl)
theorem e758 : o2.add b790 b768=b801 := @add_cons V1 _ o1 b779 b484 b473 b791 b769 b802 b801 e748 e757 (by rfl)
theorem e759 : o2.add b789 b767=b800 := @add_cons V1 _ o1 b778 b483 b472 b790 b768 b801 b800 e747 e758 (by rfl)
theorem e760 : o2.add b788 b766=b799 := @add_cons V1 _ o1 b777 b482 b471 b789 b767 b800 b799 e746 e759 (by rfl)
theorem e761 : o2.add b787 b765=b798 := @add_cons V1 _ o1 b776 b481 b470 b788 b766 b799 b798 e745 e760 (by rfl)
theorem e762 : o2.add b786 b764=b797 := @add_cons V1 _ o1 b775 b480 b469 b787 b765 b798 b797 e744 e761 (by rfl)
theorem e763 : o2.add b785 b489=b796 := @add_cons V1 _ o1 b774 b479 b468 b786 b764 b797 b796 e743 e762 (by rfl)
theorem e764 : o2.add b784 b795=b477 := @add_cons V1 _ o1 b467 (List.nil : V1) b467 b785 b489 b796 b477 e742 e763 (by rfl)
theorem e765 : o2.mul b466 b22=b477 := @mul_cons V1 _ o1 b35 b478 b22 b489 b784 b795 b477 e718 e741 (by rfl) e764
theorem e766 : o1.mul b34 b11=b446 := by decide
theorem e767 : o1.mul b34 b12=b806 := by decide
theorem e768 : o1.mul b34 b13=b807 := by decide
theorem e769 : o1.mul b34 b14=b808 := by decide
theorem e770 : o1.mul b34 b15=b809 := by decide
theorem e771 : o1.mul b34 b16=b810 := by decide
theorem e772 : o1.mul b34 b17=b811 := by decide
theorem e773 : o1.mul b34 b18=b812 := by decide
theorem e774 : o1.mul b34 b19=b813 := by decide
theorem e775 : o1.mul b34 b20=b814 := by decide
theorem e776 : o1.mul b34 b21=b815 := by decide
theorem e777 : o1.scale b34 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e778 : o1.scale b34 b580=b826 := @scale_cons V1 _ o1 b34 b21 b815 (List.nil : V2) (List.nil : V2) b826 e776 e777 (by rfl)
theorem e779 : o1.scale b34 b578=b825 := @scale_cons V1 _ o1 b34 b20 b814 b580 b826 b825 e775 e778 (by rfl)
theorem e780 : o1.scale b34 b576=b824 := @scale_cons V1 _ o1 b34 b19 b813 b578 b825 b824 e774 e779 (by rfl)
theorem e781 : o1.scale b34 b574=b823 := @scale_cons V1 _ o1 b34 b18 b812 b576 b824 b823 e773 e780 (by rfl)
theorem e782 : o1.scale b34 b572=b822 := @scale_cons V1 _ o1 b34 b17 b811 b574 b823 b822 e772 e781 (by rfl)
theorem e783 : o1.scale b34 b570=b821 := @scale_cons V1 _ o1 b34 b16 b810 b572 b822 b821 e771 e782 (by rfl)
theorem e784 : o1.scale b34 b568=b820 := @scale_cons V1 _ o1 b34 b15 b809 b570 b821 b820 e770 e783 (by rfl)
theorem e785 : o1.scale b34 b566=b819 := @scale_cons V1 _ o1 b34 b14 b808 b568 b820 b819 e769 e784 (by rfl)
theorem e786 : o1.scale b34 b564=b818 := @scale_cons V1 _ o1 b34 b13 b807 b566 b819 b818 e768 e785 (by rfl)
theorem e787 : o1.scale b34 b562=b817 := @scale_cons V1 _ o1 b34 b12 b806 b564 b818 b817 e767 e786 (by rfl)
theorem e788 : o1.scale b34 b22=b816 := @scale_cons V1 _ o1 b34 b11 b446 b562 b817 b816 e766 e787 (by rfl)
theorem e789 : o1.add b446 (List.nil : V1)=b446 := by rfl
theorem e790 : o1.add b806 b467=b447 := by decide
theorem e791 : o1.add b807 b468=b448 := by decide
theorem e792 : o1.add b808 b469=b449 := by decide
theorem e793 : o1.add b809 b470=b450 := by decide
theorem e794 : o1.add b810 b471=b451 := by decide
theorem e795 : o1.add b811 b472=b452 := by decide
theorem e796 : o1.add b812 b473=b453 := by decide
theorem e797 : o1.add b813 b474=b454 := by decide
theorem e798 : o1.add b814 b475=b455 := by decide
theorem e799 : o1.add b815 b476=b456 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
