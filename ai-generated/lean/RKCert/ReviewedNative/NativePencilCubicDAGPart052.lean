module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart051

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e7650 : o2.mul b6680 b67=b6776 := @mul_cons V1 _ o1 b263 b6682 b67 b6777 b6796 b6797 b6776 e7644 e7646 (by rfl) e7649
theorem e7651 : o1.mul b262 b66=b6640 := by decide
theorem e7652 : o1.scale b262 b67=b6798 := @scale_cons V1 _ o1 b262 b66 b6640 (List.nil : V2) (List.nil : V2) b6798 e7651 e7465 (by rfl)
theorem e7653 : o1.add b6640 (List.nil : V1)=b6640 := by rfl
theorem e7654 : o2.add (List.nil : V2) b6776=b6776 := by rfl
theorem e7655 : o2.add b6798 b6799=b6775 := @add_cons V1 _ o1 b6640 (List.nil : V1) b6640 (List.nil : V2) b6776 b6776 b6775 e7653 e7654 (by rfl)
theorem e7656 : o2.mul b6678 b67=b6775 := @mul_cons V1 _ o1 b262 b6680 b67 b6776 b6798 b6799 b6775 e7650 e7652 (by rfl) e7655
theorem e7657 : o1.mul b261 b66=b6639 := by decide
theorem e7658 : o1.scale b261 b67=b6800 := @scale_cons V1 _ o1 b261 b66 b6639 (List.nil : V2) (List.nil : V2) b6800 e7657 e7472 (by rfl)
theorem e7659 : o1.add b6639 (List.nil : V1)=b6639 := by rfl
theorem e7660 : o2.add (List.nil : V2) b6775=b6775 := by rfl
theorem e7661 : o2.add b6800 b6801=b6774 := @add_cons V1 _ o1 b6639 (List.nil : V1) b6639 (List.nil : V2) b6775 b6775 b6774 e7659 e7660 (by rfl)
theorem e7662 : o2.mul b6676 b67=b6774 := @mul_cons V1 _ o1 b261 b6678 b67 b6775 b6800 b6801 b6774 e7656 e7658 (by rfl) e7661
theorem e7663 : o1.mul b260 b66=b6638 := by decide
theorem e7664 : o1.scale b260 b67=b6802 := @scale_cons V1 _ o1 b260 b66 b6638 (List.nil : V2) (List.nil : V2) b6802 e7663 e7479 (by rfl)
theorem e7665 : o1.add b6638 (List.nil : V1)=b6638 := by rfl
theorem e7666 : o2.add (List.nil : V2) b6774=b6774 := by rfl
theorem e7667 : o2.add b6802 b6803=b6773 := @add_cons V1 _ o1 b6638 (List.nil : V1) b6638 (List.nil : V2) b6774 b6774 b6773 e7665 e7666 (by rfl)
theorem e7668 : o2.mul b6674 b67=b6773 := @mul_cons V1 _ o1 b260 b6676 b67 b6774 b6802 b6803 b6773 e7662 e7664 (by rfl) e7667
theorem e7669 : o1.mul b259 b66=b6637 := by decide
theorem e7670 : o1.scale b259 b67=b6804 := @scale_cons V1 _ o1 b259 b66 b6637 (List.nil : V2) (List.nil : V2) b6804 e7669 e7486 (by rfl)
theorem e7671 : o1.add b6637 (List.nil : V1)=b6637 := by rfl
theorem e7672 : o2.add (List.nil : V2) b6773=b6773 := by rfl
theorem e7673 : o2.add b6804 b6805=b6772 := @add_cons V1 _ o1 b6637 (List.nil : V1) b6637 (List.nil : V2) b6773 b6773 b6772 e7671 e7672 (by rfl)
theorem e7674 : o2.mul b6672 b67=b6772 := @mul_cons V1 _ o1 b259 b6674 b67 b6773 b6804 b6805 b6772 e7668 e7670 (by rfl) e7673
theorem e7675 : o1.mul b258 b66=b6636 := by decide
theorem e7676 : o1.scale b258 b67=b6806 := @scale_cons V1 _ o1 b258 b66 b6636 (List.nil : V2) (List.nil : V2) b6806 e7675 e7493 (by rfl)
theorem e7677 : o1.add b6636 (List.nil : V1)=b6636 := by rfl
theorem e7678 : o2.add (List.nil : V2) b6772=b6772 := by rfl
theorem e7679 : o2.add b6806 b6807=b6771 := @add_cons V1 _ o1 b6636 (List.nil : V1) b6636 (List.nil : V2) b6772 b6772 b6771 e7677 e7678 (by rfl)
theorem e7680 : o2.mul b6670 b67=b6771 := @mul_cons V1 _ o1 b258 b6672 b67 b6772 b6806 b6807 b6771 e7674 e7676 (by rfl) e7679
theorem e7681 : o1.mul b257 b66=b6635 := by decide
theorem e7682 : o1.scale b257 b67=b6808 := @scale_cons V1 _ o1 b257 b66 b6635 (List.nil : V2) (List.nil : V2) b6808 e7681 e7500 (by rfl)
theorem e7683 : o1.add b6635 (List.nil : V1)=b6635 := by rfl
theorem e7684 : o2.add (List.nil : V2) b6771=b6771 := by rfl
theorem e7685 : o2.add b6808 b6809=b6770 := @add_cons V1 _ o1 b6635 (List.nil : V1) b6635 (List.nil : V2) b6771 b6771 b6770 e7683 e7684 (by rfl)
theorem e7686 : o2.mul b6668 b67=b6770 := @mul_cons V1 _ o1 b257 b6670 b67 b6771 b6808 b6809 b6770 e7680 e7682 (by rfl) e7685
theorem e7687 : o1.mul b256 b66=b5134 := by decide
theorem e7688 : o1.scale b256 b67=b6810 := @scale_cons V1 _ o1 b256 b66 b5134 (List.nil : V2) (List.nil : V2) b6810 e7687 e7507 (by rfl)
theorem e7689 : o1.add b5134 (List.nil : V1)=b5134 := by rfl
theorem e7690 : o2.add (List.nil : V2) b6770=b6770 := by rfl
theorem e7691 : o2.add b6810 b6811=b6769 := @add_cons V1 _ o1 b5134 (List.nil : V1) b5134 (List.nil : V2) b6770 b6770 b6769 e7689 e7690 (by rfl)
theorem e7692 : o2.mul b6666 b67=b6769 := @mul_cons V1 _ o1 b256 b6668 b67 b6770 b6810 b6811 b6769 e7686 e7688 (by rfl) e7691
theorem e7693 : o2.add (List.nil : V2) b6649=b6649 := by rfl
theorem e7694 : o2.mul b271 b67=b6649 := @mul_cons V1 _ o1 (List.nil : V1) b6666 b67 b6769 (List.nil : V2) b6649 b6649 e7692 e5609 (by rfl) e7693
theorem e7695 : o1.mul b270 b68=b6663 := by decide
theorem e7696 : o1.scale b270 b69=b6827 := @scale_cons V1 _ o1 b270 b68 b6663 (List.nil : V2) (List.nil : V2) b6827 e7695 e7411 (by rfl)
theorem e7697 : o2.add b6827 (List.nil : V2)=b6827 := by rfl
theorem e7698 : o2.mul b6694 b69=b6827 := @mul_cons V1 _ o1 b270 (List.nil : V2) b69 (List.nil : V2) b6827 (List.nil : V2) b6827 e5622 e7696 (by rfl) e7697
theorem e7699 : o1.mul b269 b68=b6662 := by decide
theorem e7700 : o1.scale b269 b69=b6828 := @scale_cons V1 _ o1 b269 b68 b6662 (List.nil : V2) (List.nil : V2) b6828 e7699 e7416 (by rfl)
theorem e7701 : o1.add b6662 (List.nil : V1)=b6662 := by rfl
theorem e7702 : o2.add (List.nil : V2) b6827=b6827 := by rfl
theorem e7703 : o2.add b6828 b6829=b6826 := @add_cons V1 _ o1 b6662 (List.nil : V1) b6662 (List.nil : V2) b6827 b6827 b6826 e7701 e7702 (by rfl)
theorem e7704 : o2.mul b6692 b69=b6826 := @mul_cons V1 _ o1 b269 b6694 b69 b6827 b6828 b6829 b6826 e7698 e7700 (by rfl) e7703
theorem e7705 : o1.mul b268 b68=b6661 := by decide
theorem e7706 : o1.scale b268 b69=b6830 := @scale_cons V1 _ o1 b268 b68 b6661 (List.nil : V2) (List.nil : V2) b6830 e7705 e7423 (by rfl)
theorem e7707 : o1.add b6661 (List.nil : V1)=b6661 := by rfl
theorem e7708 : o2.add (List.nil : V2) b6826=b6826 := by rfl
theorem e7709 : o2.add b6830 b6831=b6825 := @add_cons V1 _ o1 b6661 (List.nil : V1) b6661 (List.nil : V2) b6826 b6826 b6825 e7707 e7708 (by rfl)
theorem e7710 : o2.mul b6690 b69=b6825 := @mul_cons V1 _ o1 b268 b6692 b69 b6826 b6830 b6831 b6825 e7704 e7706 (by rfl) e7709
theorem e7711 : o1.mul b267 b68=b6660 := by decide
theorem e7712 : o1.scale b267 b69=b6832 := @scale_cons V1 _ o1 b267 b68 b6660 (List.nil : V2) (List.nil : V2) b6832 e7711 e7430 (by rfl)
theorem e7713 : o1.add b6660 (List.nil : V1)=b6660 := by rfl
theorem e7714 : o2.add (List.nil : V2) b6825=b6825 := by rfl
theorem e7715 : o2.add b6832 b6833=b6824 := @add_cons V1 _ o1 b6660 (List.nil : V1) b6660 (List.nil : V2) b6825 b6825 b6824 e7713 e7714 (by rfl)
theorem e7716 : o2.mul b6688 b69=b6824 := @mul_cons V1 _ o1 b267 b6690 b69 b6825 b6832 b6833 b6824 e7710 e7712 (by rfl) e7715
theorem e7717 : o1.mul b266 b68=b6659 := by decide
theorem e7718 : o1.scale b266 b69=b6834 := @scale_cons V1 _ o1 b266 b68 b6659 (List.nil : V2) (List.nil : V2) b6834 e7717 e7437 (by rfl)
theorem e7719 : o1.add b6659 (List.nil : V1)=b6659 := by rfl
theorem e7720 : o2.add (List.nil : V2) b6824=b6824 := by rfl
theorem e7721 : o2.add b6834 b6835=b6823 := @add_cons V1 _ o1 b6659 (List.nil : V1) b6659 (List.nil : V2) b6824 b6824 b6823 e7719 e7720 (by rfl)
theorem e7722 : o2.mul b6686 b69=b6823 := @mul_cons V1 _ o1 b266 b6688 b69 b6824 b6834 b6835 b6823 e7716 e7718 (by rfl) e7721
theorem e7723 : o1.mul b265 b68=b6658 := by decide
theorem e7724 : o1.scale b265 b69=b6836 := @scale_cons V1 _ o1 b265 b68 b6658 (List.nil : V2) (List.nil : V2) b6836 e7723 e7444 (by rfl)
theorem e7725 : o1.add b6658 (List.nil : V1)=b6658 := by rfl
theorem e7726 : o2.add (List.nil : V2) b6823=b6823 := by rfl
theorem e7727 : o2.add b6836 b6837=b6822 := @add_cons V1 _ o1 b6658 (List.nil : V1) b6658 (List.nil : V2) b6823 b6823 b6822 e7725 e7726 (by rfl)
theorem e7728 : o2.mul b6684 b69=b6822 := @mul_cons V1 _ o1 b265 b6686 b69 b6823 b6836 b6837 b6822 e7722 e7724 (by rfl) e7727
theorem e7729 : o1.mul b264 b68=b6657 := by decide
theorem e7730 : o1.scale b264 b69=b6838 := @scale_cons V1 _ o1 b264 b68 b6657 (List.nil : V2) (List.nil : V2) b6838 e7729 e7451 (by rfl)
theorem e7731 : o1.add b6657 (List.nil : V1)=b6657 := by rfl
theorem e7732 : o2.add (List.nil : V2) b6822=b6822 := by rfl
theorem e7733 : o2.add b6838 b6839=b6821 := @add_cons V1 _ o1 b6657 (List.nil : V1) b6657 (List.nil : V2) b6822 b6822 b6821 e7731 e7732 (by rfl)
theorem e7734 : o2.mul b6682 b69=b6821 := @mul_cons V1 _ o1 b264 b6684 b69 b6822 b6838 b6839 b6821 e7728 e7730 (by rfl) e7733
theorem e7735 : o1.mul b263 b68=b6656 := by decide
theorem e7736 : o1.scale b263 b69=b6840 := @scale_cons V1 _ o1 b263 b68 b6656 (List.nil : V2) (List.nil : V2) b6840 e7735 e7458 (by rfl)
theorem e7737 : o1.add b6656 (List.nil : V1)=b6656 := by rfl
theorem e7738 : o2.add (List.nil : V2) b6821=b6821 := by rfl
theorem e7739 : o2.add b6840 b6841=b6820 := @add_cons V1 _ o1 b6656 (List.nil : V1) b6656 (List.nil : V2) b6821 b6821 b6820 e7737 e7738 (by rfl)
theorem e7740 : o2.mul b6680 b69=b6820 := @mul_cons V1 _ o1 b263 b6682 b69 b6821 b6840 b6841 b6820 e7734 e7736 (by rfl) e7739
theorem e7741 : o1.mul b262 b68=b6655 := by decide
theorem e7742 : o1.scale b262 b69=b6842 := @scale_cons V1 _ o1 b262 b68 b6655 (List.nil : V2) (List.nil : V2) b6842 e7741 e7465 (by rfl)
theorem e7743 : o1.add b6655 (List.nil : V1)=b6655 := by rfl
theorem e7744 : o2.add (List.nil : V2) b6820=b6820 := by rfl
theorem e7745 : o2.add b6842 b6843=b6819 := @add_cons V1 _ o1 b6655 (List.nil : V1) b6655 (List.nil : V2) b6820 b6820 b6819 e7743 e7744 (by rfl)
theorem e7746 : o2.mul b6678 b69=b6819 := @mul_cons V1 _ o1 b262 b6680 b69 b6820 b6842 b6843 b6819 e7740 e7742 (by rfl) e7745
theorem e7747 : o1.mul b261 b68=b6654 := by decide
theorem e7748 : o1.scale b261 b69=b6844 := @scale_cons V1 _ o1 b261 b68 b6654 (List.nil : V2) (List.nil : V2) b6844 e7747 e7472 (by rfl)
theorem e7749 : o1.add b6654 (List.nil : V1)=b6654 := by rfl
theorem e7750 : o2.add (List.nil : V2) b6819=b6819 := by rfl
theorem e7751 : o2.add b6844 b6845=b6818 := @add_cons V1 _ o1 b6654 (List.nil : V1) b6654 (List.nil : V2) b6819 b6819 b6818 e7749 e7750 (by rfl)
theorem e7752 : o2.mul b6676 b69=b6818 := @mul_cons V1 _ o1 b261 b6678 b69 b6819 b6844 b6845 b6818 e7746 e7748 (by rfl) e7751
theorem e7753 : o1.mul b260 b68=b6653 := by decide
theorem e7754 : o1.scale b260 b69=b6846 := @scale_cons V1 _ o1 b260 b68 b6653 (List.nil : V2) (List.nil : V2) b6846 e7753 e7479 (by rfl)
theorem e7755 : o1.add b6653 (List.nil : V1)=b6653 := by rfl
theorem e7756 : o2.add (List.nil : V2) b6818=b6818 := by rfl
theorem e7757 : o2.add b6846 b6847=b6817 := @add_cons V1 _ o1 b6653 (List.nil : V1) b6653 (List.nil : V2) b6818 b6818 b6817 e7755 e7756 (by rfl)
theorem e7758 : o2.mul b6674 b69=b6817 := @mul_cons V1 _ o1 b260 b6676 b69 b6818 b6846 b6847 b6817 e7752 e7754 (by rfl) e7757
theorem e7759 : o1.mul b259 b68=b6652 := by decide
theorem e7760 : o1.scale b259 b69=b6848 := @scale_cons V1 _ o1 b259 b68 b6652 (List.nil : V2) (List.nil : V2) b6848 e7759 e7486 (by rfl)
theorem e7761 : o1.add b6652 (List.nil : V1)=b6652 := by rfl
theorem e7762 : o2.add (List.nil : V2) b6817=b6817 := by rfl
theorem e7763 : o2.add b6848 b6849=b6816 := @add_cons V1 _ o1 b6652 (List.nil : V1) b6652 (List.nil : V2) b6817 b6817 b6816 e7761 e7762 (by rfl)
theorem e7764 : o2.mul b6672 b69=b6816 := @mul_cons V1 _ o1 b259 b6674 b69 b6817 b6848 b6849 b6816 e7758 e7760 (by rfl) e7763
theorem e7765 : o1.mul b258 b68=b6651 := by decide
theorem e7766 : o1.scale b258 b69=b6850 := @scale_cons V1 _ o1 b258 b68 b6651 (List.nil : V2) (List.nil : V2) b6850 e7765 e7493 (by rfl)
theorem e7767 : o1.add b6651 (List.nil : V1)=b6651 := by rfl
theorem e7768 : o2.add (List.nil : V2) b6816=b6816 := by rfl
theorem e7769 : o2.add b6850 b6851=b6815 := @add_cons V1 _ o1 b6651 (List.nil : V1) b6651 (List.nil : V2) b6816 b6816 b6815 e7767 e7768 (by rfl)
theorem e7770 : o2.mul b6670 b69=b6815 := @mul_cons V1 _ o1 b258 b6672 b69 b6816 b6850 b6851 b6815 e7764 e7766 (by rfl) e7769
theorem e7771 : o1.mul b257 b68=b6650 := by decide
theorem e7772 : o1.scale b257 b69=b6852 := @scale_cons V1 _ o1 b257 b68 b6650 (List.nil : V2) (List.nil : V2) b6852 e7771 e7500 (by rfl)
theorem e7773 : o1.add b6650 (List.nil : V1)=b6650 := by rfl
theorem e7774 : o2.add (List.nil : V2) b6815=b6815 := by rfl
theorem e7775 : o2.add b6852 b6853=b6814 := @add_cons V1 _ o1 b6650 (List.nil : V1) b6650 (List.nil : V2) b6815 b6815 b6814 e7773 e7774 (by rfl)
theorem e7776 : o2.mul b6668 b69=b6814 := @mul_cons V1 _ o1 b257 b6670 b69 b6815 b6852 b6853 b6814 e7770 e7772 (by rfl) e7775
theorem e7777 : o1.mul b256 b68=b5150 := by decide
theorem e7778 : o1.scale b256 b69=b6854 := @scale_cons V1 _ o1 b256 b68 b5150 (List.nil : V2) (List.nil : V2) b6854 e7777 e7507 (by rfl)
theorem e7779 : o1.add b5150 (List.nil : V1)=b5150 := by rfl
theorem e7780 : o2.add (List.nil : V2) b6814=b6814 := by rfl
theorem e7781 : o2.add b6854 b6855=b6813 := @add_cons V1 _ o1 b5150 (List.nil : V1) b5150 (List.nil : V2) b6814 b6814 b6813 e7779 e7780 (by rfl)
theorem e7782 : o2.mul b6666 b69=b6813 := @mul_cons V1 _ o1 b256 b6668 b69 b6814 b6854 b6855 b6813 e7776 e7778 (by rfl) e7781
theorem e7783 : o2.add (List.nil : V2) b6664=b6664 := by rfl
theorem e7784 : o2.mul b271 b69=b6664 := @mul_cons V1 _ o1 (List.nil : V1) b6666 b69 b6813 (List.nil : V2) b6664 b6664 e7782 e5682 (by rfl) e7783
theorem e7785 : o2.scale b271 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e7786 : o2.scale b271 b5555=b6812 := @scale_cons V2 _ o2 b271 b69 b6664 (List.nil : V3) (List.nil : V3) b6812 e7784 e7785 (by rfl)
theorem e7787 : o2.scale b271 b5520=b6768 := @scale_cons V2 _ o2 b271 b67 b6649 b5555 b6812 b6768 e7694 e7786 (by rfl)
theorem e7788 : o2.scale b271 b5485=b6724 := @scale_cons V2 _ o2 b271 b65 b6634 b5520 b6768 b6724 e7604 e7787 (by rfl)
theorem e7789 : o2.scale b271 b70=b6665 := @scale_cons V2 _ o2 b271 b63 b5117 b5485 b6724 b6665 e7514 e7788 (by rfl)
theorem e7790 : o2.add b5117 (List.nil : V2)=b5117 := by rfl
theorem e7791 : o1.add b6620 b5233=b5119 := by decide
theorem e7792 : o1.add b6621 b5234=b5120 := by decide
theorem e7793 : o1.add b6622 b5235=b5121 := by decide
theorem e7794 : o1.add b6623 b5236=b5122 := by decide
theorem e7795 : o1.add b6624 b5237=b5123 := by decide
theorem e7796 : o1.add b6625 b5238=b5124 := by decide
theorem e7797 : o1.add b6626 b5239=b5125 := by decide
theorem e7798 : o1.add b6627 b5240=b5126 := by decide
theorem e7799 : o1.add b6628 b5241=b5127 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
