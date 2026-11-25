module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart007

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e700 : o1.add b620 (List.nil : V1)=b620 := by rfl
theorem e701 : o2.add (List.nil : V2) b646=b646 := by rfl
theorem e702 : o2.add b731 b732=b643 := @add_cons V1 _ o1 b620 (List.nil : V1) b620 (List.nil : V2) b646 b646 b643 e700 e701 (by rfl)
theorem e703 : o2.mul b69 b4=b643 := @mul_cons V1 _ o1 b46 b645 b4 b646 b731 b732 b643 e696 e699 (by rfl) e702
theorem e704 : o2.scale b69 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e705 : o2.scale b69 b5=b644 := @scale_cons V2 _ o2 b69 b4 b643 (List.nil : V3) (List.nil : V3) b644 e703 e704 (by rfl)
theorem e706 : o3.add b644 (List.nil : V3)=b644 := by rfl
theorem e707 : o3.mul b70 b5=b644 := @mul_cons V2 _ o2 b69 (List.nil : V3) b5 (List.nil : V3) b644 (List.nil : V3) b644 e543 e705 (by rfl) e706
theorem e708 : o3.mul (List.nil : V3) b17=(List.nil : V3) := by rfl
theorem e709 : o2.mul (List.nil : V2) b16=(List.nil : V2) := by rfl
theorem e710 : o1.mul b84 b6=b891 := by decide
theorem e711 : o1.mul b84 b7=b892 := by decide
theorem e712 : o1.mul b84 b8=b893 := by decide
theorem e713 : o1.mul b84 b9=b894 := by decide
theorem e714 : o1.mul b84 b10=b895 := by decide
theorem e715 : o1.mul b84 b11=b896 := by decide
theorem e716 : o1.mul b84 b12=b897 := by decide
theorem e717 : o1.mul b84 b13=b898 := by decide
theorem e718 : o1.mul b84 b14=b899 := by decide
theorem e719 : o1.mul b84 b15=b755 := by decide
theorem e720 : o1.scale b84 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e721 : o1.scale b84 b917=b918 := @scale_cons V1 _ o1 b84 b15 b755 (List.nil : V2) (List.nil : V2) b918 e719 e720 (by rfl)
theorem e722 : o1.scale b84 b915=b916 := @scale_cons V1 _ o1 b84 b14 b899 b917 b918 b916 e718 e721 (by rfl)
theorem e723 : o1.scale b84 b913=b914 := @scale_cons V1 _ o1 b84 b13 b898 b915 b916 b914 e717 e722 (by rfl)
theorem e724 : o1.scale b84 b911=b912 := @scale_cons V1 _ o1 b84 b12 b897 b913 b914 b912 e716 e723 (by rfl)
theorem e725 : o1.scale b84 b909=b910 := @scale_cons V1 _ o1 b84 b11 b896 b911 b912 b910 e715 e724 (by rfl)
theorem e726 : o1.scale b84 b907=b908 := @scale_cons V1 _ o1 b84 b10 b895 b909 b910 b908 e714 e725 (by rfl)
theorem e727 : o1.scale b84 b905=b906 := @scale_cons V1 _ o1 b84 b9 b894 b907 b908 b906 e713 e726 (by rfl)
theorem e728 : o1.scale b84 b903=b904 := @scale_cons V1 _ o1 b84 b8 b893 b905 b906 b904 e712 e727 (by rfl)
theorem e729 : o1.scale b84 b901=b902 := @scale_cons V1 _ o1 b84 b7 b892 b903 b904 b902 e711 e728 (by rfl)
theorem e730 : o1.scale b84 b16=b900 := @scale_cons V1 _ o1 b84 b6 b891 b901 b902 b900 e710 e729 (by rfl)
theorem e731 : o2.add b900 (List.nil : V2)=b900 := by rfl
theorem e732 : o2.mul b890 b16=b900 := @mul_cons V1 _ o1 b84 (List.nil : V2) b16 (List.nil : V2) b900 (List.nil : V2) b900 e709 e730 (by rfl) e731
theorem e733 : o1.mul b83 b6=b880 := by decide
theorem e734 : o1.mul b83 b7=b919 := by decide
theorem e735 : o1.mul b83 b8=b920 := by decide
theorem e736 : o1.mul b83 b9=b921 := by decide
theorem e737 : o1.mul b83 b10=b922 := by decide
theorem e738 : o1.mul b83 b11=b923 := by decide
theorem e739 : o1.mul b83 b12=b924 := by decide
theorem e740 : o1.mul b83 b13=b925 := by decide
theorem e741 : o1.mul b83 b14=b926 := by decide
theorem e742 : o1.mul b83 b15=b927 := by decide
theorem e743 : o1.scale b83 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e744 : o1.scale b83 b917=b937 := @scale_cons V1 _ o1 b83 b15 b927 (List.nil : V2) (List.nil : V2) b937 e742 e743 (by rfl)
theorem e745 : o1.scale b83 b915=b936 := @scale_cons V1 _ o1 b83 b14 b926 b917 b937 b936 e741 e744 (by rfl)
theorem e746 : o1.scale b83 b913=b935 := @scale_cons V1 _ o1 b83 b13 b925 b915 b936 b935 e740 e745 (by rfl)
theorem e747 : o1.scale b83 b911=b934 := @scale_cons V1 _ o1 b83 b12 b924 b913 b935 b934 e739 e746 (by rfl)
theorem e748 : o1.scale b83 b909=b933 := @scale_cons V1 _ o1 b83 b11 b923 b911 b934 b933 e738 e747 (by rfl)
theorem e749 : o1.scale b83 b907=b932 := @scale_cons V1 _ o1 b83 b10 b922 b909 b933 b932 e737 e748 (by rfl)
theorem e750 : o1.scale b83 b905=b931 := @scale_cons V1 _ o1 b83 b9 b921 b907 b932 b931 e736 e749 (by rfl)
theorem e751 : o1.scale b83 b903=b930 := @scale_cons V1 _ o1 b83 b8 b920 b905 b931 b930 e735 e750 (by rfl)
theorem e752 : o1.scale b83 b901=b929 := @scale_cons V1 _ o1 b83 b7 b919 b903 b930 b929 e734 e751 (by rfl)
theorem e753 : o1.scale b83 b16=b928 := @scale_cons V1 _ o1 b83 b6 b880 b901 b929 b928 e733 e752 (by rfl)
theorem e754 : o1.add b880 (List.nil : V1)=b880 := by rfl
theorem e755 : o1.add b919 b891=b881 := by decide
theorem e756 : o1.add b920 b892=b882 := by decide
theorem e757 : o1.add b921 b893=b883 := by decide
theorem e758 : o1.add b922 b894=b884 := by decide
theorem e759 : o1.add b923 b895=b885 := by decide
theorem e760 : o1.add b924 b896=b886 := by decide
theorem e761 : o1.add b925 b897=b887 := by decide
theorem e762 : o1.add b926 b898=b888 := by decide
theorem e763 : o1.add b927 b899=b754 := by decide
theorem e764 : o2.add (List.nil : V2) b918=b918 := by rfl
theorem e765 : o2.add b937 b916=b947 := @add_cons V1 _ o1 b927 b899 b754 (List.nil : V2) b918 b918 b947 e763 e764 (by rfl)
theorem e766 : o2.add b936 b914=b946 := @add_cons V1 _ o1 b926 b898 b888 b937 b916 b947 b946 e762 e765 (by rfl)
theorem e767 : o2.add b935 b912=b945 := @add_cons V1 _ o1 b925 b897 b887 b936 b914 b946 b945 e761 e766 (by rfl)
theorem e768 : o2.add b934 b910=b944 := @add_cons V1 _ o1 b924 b896 b886 b935 b912 b945 b944 e760 e767 (by rfl)
theorem e769 : o2.add b933 b908=b943 := @add_cons V1 _ o1 b923 b895 b885 b934 b910 b944 b943 e759 e768 (by rfl)
theorem e770 : o2.add b932 b906=b942 := @add_cons V1 _ o1 b922 b894 b884 b933 b908 b943 b942 e758 e769 (by rfl)
theorem e771 : o2.add b931 b904=b941 := @add_cons V1 _ o1 b921 b893 b883 b932 b906 b942 b941 e757 e770 (by rfl)
theorem e772 : o2.add b930 b902=b940 := @add_cons V1 _ o1 b920 b892 b882 b931 b904 b941 b940 e756 e771 (by rfl)
theorem e773 : o2.add b929 b900=b939 := @add_cons V1 _ o1 b919 b891 b881 b930 b902 b940 b939 e755 e772 (by rfl)
theorem e774 : o2.add b928 b938=b889 := @add_cons V1 _ o1 b880 (List.nil : V1) b880 b929 b900 b939 b889 e754 e773 (by rfl)
theorem e775 : o2.mul b879 b16=b889 := @mul_cons V1 _ o1 b83 b890 b16 b900 b928 b938 b889 e732 e753 (by rfl) e774
theorem e776 : o1.mul b82 b6=b869 := by decide
theorem e777 : o1.mul b82 b7=b948 := by decide
theorem e778 : o1.mul b82 b8=b949 := by decide
theorem e779 : o1.mul b82 b9=b950 := by decide
theorem e780 : o1.mul b82 b10=b951 := by decide
theorem e781 : o1.mul b82 b11=b952 := by decide
theorem e782 : o1.mul b82 b12=b953 := by decide
theorem e783 : o1.mul b82 b13=b954 := by decide
theorem e784 : o1.mul b82 b14=b955 := by decide
theorem e785 : o1.mul b82 b15=b956 := by decide
theorem e786 : o1.scale b82 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e787 : o1.scale b82 b917=b966 := @scale_cons V1 _ o1 b82 b15 b956 (List.nil : V2) (List.nil : V2) b966 e785 e786 (by rfl)
theorem e788 : o1.scale b82 b915=b965 := @scale_cons V1 _ o1 b82 b14 b955 b917 b966 b965 e784 e787 (by rfl)
theorem e789 : o1.scale b82 b913=b964 := @scale_cons V1 _ o1 b82 b13 b954 b915 b965 b964 e783 e788 (by rfl)
theorem e790 : o1.scale b82 b911=b963 := @scale_cons V1 _ o1 b82 b12 b953 b913 b964 b963 e782 e789 (by rfl)
theorem e791 : o1.scale b82 b909=b962 := @scale_cons V1 _ o1 b82 b11 b952 b911 b963 b962 e781 e790 (by rfl)
theorem e792 : o1.scale b82 b907=b961 := @scale_cons V1 _ o1 b82 b10 b951 b909 b962 b961 e780 e791 (by rfl)
theorem e793 : o1.scale b82 b905=b960 := @scale_cons V1 _ o1 b82 b9 b950 b907 b961 b960 e779 e792 (by rfl)
theorem e794 : o1.scale b82 b903=b959 := @scale_cons V1 _ o1 b82 b8 b949 b905 b960 b959 e778 e793 (by rfl)
theorem e795 : o1.scale b82 b901=b958 := @scale_cons V1 _ o1 b82 b7 b948 b903 b959 b958 e777 e794 (by rfl)
theorem e796 : o1.scale b82 b16=b957 := @scale_cons V1 _ o1 b82 b6 b869 b901 b958 b957 e776 e795 (by rfl)
theorem e797 : o1.add b869 (List.nil : V1)=b869 := by rfl
theorem e798 : o1.add b948 b880=b870 := by decide
theorem e799 : o1.add b949 b881=b871 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
