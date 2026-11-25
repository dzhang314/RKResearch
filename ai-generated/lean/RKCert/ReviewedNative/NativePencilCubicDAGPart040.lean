module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart039

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5850 : o2.mul b5632 b65=b5679 := @mul_cons V1 _ o1 b314 b5634 b65 b5680 b5708 b5709 b5679 e5844 e5846 (by rfl) e5849
theorem e5851 : o2.add (List.nil : V2) b5678=b5678 := by rfl
theorem e5852 : o2.mul b5630 b65=b5678 := @mul_cons V1 _ o1 (List.nil : V1) b5632 b65 b5679 (List.nil : V2) b5678 b5678 e5850 e5536 (by rfl) e5851
theorem e5853 : o2.add (List.nil : V2) b5677=b5677 := by rfl
theorem e5854 : o2.mul b5628 b65=b5677 := @mul_cons V1 _ o1 (List.nil : V1) b5630 b65 b5678 (List.nil : V2) b5677 b5677 e5852 e5536 (by rfl) e5853
theorem e5855 : o2.add (List.nil : V2) b5676=b5676 := by rfl
theorem e5856 : o2.mul b5626 b65=b5676 := @mul_cons V1 _ o1 (List.nil : V1) b5628 b65 b5677 (List.nil : V2) b5676 b5676 e5854 e5536 (by rfl) e5855
theorem e5857 : o2.add (List.nil : V2) b5675=b5675 := by rfl
theorem e5858 : o2.mul b5624 b65=b5675 := @mul_cons V1 _ o1 (List.nil : V1) b5626 b65 b5676 (List.nil : V2) b5675 b5675 e5856 e5536 (by rfl) e5857
theorem e5859 : o2.add (List.nil : V2) b5600=b5600 := by rfl
theorem e5860 : o2.mul b325 b65=b5600 := @mul_cons V1 _ o1 (List.nil : V1) b5624 b65 b5675 (List.nil : V2) b5600 b5600 e5858 e5536 (by rfl) e5859
theorem e5861 : o1.mul b324 b66=b5610 := by decide
theorem e5862 : o1.scale b324 b67=b5725 := @scale_cons V1 _ o1 b324 b66 b5610 (List.nil : V2) (List.nil : V2) b5725 e5861 e5703 (by rfl)
theorem e5863 : o2.add b5725 (List.nil : V2)=b5725 := by rfl
theorem e5864 : o2.mul b5652 b67=b5725 := @mul_cons V1 _ o1 b324 (List.nil : V2) b67 (List.nil : V2) b5725 (List.nil : V2) b5725 e5549 e5862 (by rfl) e5863
theorem e5865 : o1.mul b323 b66=b5609 := by decide
theorem e5866 : o1.scale b323 b67=b5726 := @scale_cons V1 _ o1 b323 b66 b5609 (List.nil : V2) (List.nil : V2) b5726 e5865 e5708 (by rfl)
theorem e5867 : o1.add b5609 (List.nil : V1)=b5609 := by rfl
theorem e5868 : o2.add (List.nil : V2) b5725=b5725 := by rfl
theorem e5869 : o2.add b5726 b5727=b5724 := @add_cons V1 _ o1 b5609 (List.nil : V1) b5609 (List.nil : V2) b5725 b5725 b5724 e5867 e5868 (by rfl)
theorem e5870 : o2.mul b5650 b67=b5724 := @mul_cons V1 _ o1 b323 b5652 b67 b5725 b5726 b5727 b5724 e5864 e5866 (by rfl) e5869
theorem e5871 : o1.mul b322 b66=b5608 := by decide
theorem e5872 : o1.scale b322 b67=b5728 := @scale_cons V1 _ o1 b322 b66 b5608 (List.nil : V2) (List.nil : V2) b5728 e5871 e5715 (by rfl)
theorem e5873 : o1.add b5608 (List.nil : V1)=b5608 := by rfl
theorem e5874 : o2.add (List.nil : V2) b5724=b5724 := by rfl
theorem e5875 : o2.add b5728 b5729=b5723 := @add_cons V1 _ o1 b5608 (List.nil : V1) b5608 (List.nil : V2) b5724 b5724 b5723 e5873 e5874 (by rfl)
theorem e5876 : o2.mul b5648 b67=b5723 := @mul_cons V1 _ o1 b322 b5650 b67 b5724 b5728 b5729 b5723 e5870 e5872 (by rfl) e5875
theorem e5877 : o1.mul b321 b66=b5607 := by decide
theorem e5878 : o1.scale b321 b67=b5730 := @scale_cons V1 _ o1 b321 b66 b5607 (List.nil : V2) (List.nil : V2) b5730 e5877 e5722 (by rfl)
theorem e5879 : o1.add b5607 (List.nil : V1)=b5607 := by rfl
theorem e5880 : o2.add (List.nil : V2) b5723=b5723 := by rfl
theorem e5881 : o2.add b5730 b5731=b5722 := @add_cons V1 _ o1 b5607 (List.nil : V1) b5607 (List.nil : V2) b5723 b5723 b5722 e5879 e5880 (by rfl)
theorem e5882 : o2.mul b5646 b67=b5722 := @mul_cons V1 _ o1 b321 b5648 b67 b5723 b5730 b5731 b5722 e5876 e5878 (by rfl) e5881
theorem e5883 : o1.mul b320 b66=b5606 := by decide
theorem e5884 : o1.scale b320 b67=b5732 := @scale_cons V1 _ o1 b320 b66 b5606 (List.nil : V2) (List.nil : V2) b5732 e5883 e5729 (by rfl)
theorem e5885 : o1.add b5606 (List.nil : V1)=b5606 := by rfl
theorem e5886 : o2.add (List.nil : V2) b5722=b5722 := by rfl
theorem e5887 : o2.add b5732 b5733=b5721 := @add_cons V1 _ o1 b5606 (List.nil : V1) b5606 (List.nil : V2) b5722 b5722 b5721 e5885 e5886 (by rfl)
theorem e5888 : o2.mul b5644 b67=b5721 := @mul_cons V1 _ o1 b320 b5646 b67 b5722 b5732 b5733 b5721 e5882 e5884 (by rfl) e5887
theorem e5889 : o1.mul b319 b66=b5605 := by decide
theorem e5890 : o1.scale b319 b67=b5734 := @scale_cons V1 _ o1 b319 b66 b5605 (List.nil : V2) (List.nil : V2) b5734 e5889 e5736 (by rfl)
theorem e5891 : o1.add b5605 (List.nil : V1)=b5605 := by rfl
theorem e5892 : o2.add (List.nil : V2) b5721=b5721 := by rfl
theorem e5893 : o2.add b5734 b5735=b5720 := @add_cons V1 _ o1 b5605 (List.nil : V1) b5605 (List.nil : V2) b5721 b5721 b5720 e5891 e5892 (by rfl)
theorem e5894 : o2.mul b5642 b67=b5720 := @mul_cons V1 _ o1 b319 b5644 b67 b5721 b5734 b5735 b5720 e5888 e5890 (by rfl) e5893
theorem e5895 : o1.mul b318 b66=b5604 := by decide
theorem e5896 : o1.scale b318 b67=b5736 := @scale_cons V1 _ o1 b318 b66 b5604 (List.nil : V2) (List.nil : V2) b5736 e5895 e5743 (by rfl)
theorem e5897 : o1.add b5604 (List.nil : V1)=b5604 := by rfl
theorem e5898 : o2.add (List.nil : V2) b5720=b5720 := by rfl
theorem e5899 : o2.add b5736 b5737=b5719 := @add_cons V1 _ o1 b5604 (List.nil : V1) b5604 (List.nil : V2) b5720 b5720 b5719 e5897 e5898 (by rfl)
theorem e5900 : o2.mul b5640 b67=b5719 := @mul_cons V1 _ o1 b318 b5642 b67 b5720 b5736 b5737 b5719 e5894 e5896 (by rfl) e5899
theorem e5901 : o1.mul b317 b66=b5603 := by decide
theorem e5902 : o1.scale b317 b67=b5738 := @scale_cons V1 _ o1 b317 b66 b5603 (List.nil : V2) (List.nil : V2) b5738 e5901 e5750 (by rfl)
theorem e5903 : o1.add b5603 (List.nil : V1)=b5603 := by rfl
theorem e5904 : o2.add (List.nil : V2) b5719=b5719 := by rfl
theorem e5905 : o2.add b5738 b5739=b5718 := @add_cons V1 _ o1 b5603 (List.nil : V1) b5603 (List.nil : V2) b5719 b5719 b5718 e5903 e5904 (by rfl)
theorem e5906 : o2.mul b5638 b67=b5718 := @mul_cons V1 _ o1 b317 b5640 b67 b5719 b5738 b5739 b5718 e5900 e5902 (by rfl) e5905
theorem e5907 : o1.mul b316 b66=b5602 := by decide
theorem e5908 : o1.scale b316 b67=b5740 := @scale_cons V1 _ o1 b316 b66 b5602 (List.nil : V2) (List.nil : V2) b5740 e5907 e5757 (by rfl)
theorem e5909 : o1.add b5602 (List.nil : V1)=b5602 := by rfl
theorem e5910 : o2.add (List.nil : V2) b5718=b5718 := by rfl
theorem e5911 : o2.add b5740 b5741=b5717 := @add_cons V1 _ o1 b5602 (List.nil : V1) b5602 (List.nil : V2) b5718 b5718 b5717 e5909 e5910 (by rfl)
theorem e5912 : o2.mul b5636 b67=b5717 := @mul_cons V1 _ o1 b316 b5638 b67 b5718 b5740 b5741 b5717 e5906 e5908 (by rfl) e5911
theorem e5913 : o1.mul b315 b66=b5601 := by decide
theorem e5914 : o1.scale b315 b67=b5742 := @scale_cons V1 _ o1 b315 b66 b5601 (List.nil : V2) (List.nil : V2) b5742 e5913 e5764 (by rfl)
theorem e5915 : o1.add b5601 (List.nil : V1)=b5601 := by rfl
theorem e5916 : o2.add (List.nil : V2) b5717=b5717 := by rfl
theorem e5917 : o2.add b5742 b5743=b5716 := @add_cons V1 _ o1 b5601 (List.nil : V1) b5601 (List.nil : V2) b5717 b5717 b5716 e5915 e5916 (by rfl)
theorem e5918 : o2.mul b5634 b67=b5716 := @mul_cons V1 _ o1 b315 b5636 b67 b5717 b5742 b5743 b5716 e5912 e5914 (by rfl) e5917
theorem e5919 : o1.mul b314 b66=b5389 := by decide
theorem e5920 : o1.scale b314 b67=b5744 := @scale_cons V1 _ o1 b314 b66 b5389 (List.nil : V2) (List.nil : V2) b5744 e5919 e5771 (by rfl)
theorem e5921 : o1.add b5389 (List.nil : V1)=b5389 := by rfl
theorem e5922 : o2.add (List.nil : V2) b5716=b5716 := by rfl
theorem e5923 : o2.add b5744 b5745=b5715 := @add_cons V1 _ o1 b5389 (List.nil : V1) b5389 (List.nil : V2) b5716 b5716 b5715 e5921 e5922 (by rfl)
theorem e5924 : o2.mul b5632 b67=b5715 := @mul_cons V1 _ o1 b314 b5634 b67 b5716 b5744 b5745 b5715 e5918 e5920 (by rfl) e5923
theorem e5925 : o2.add (List.nil : V2) b5714=b5714 := by rfl
theorem e5926 : o2.mul b5630 b67=b5714 := @mul_cons V1 _ o1 (List.nil : V1) b5632 b67 b5715 (List.nil : V2) b5714 b5714 e5924 e5609 (by rfl) e5925
theorem e5927 : o2.add (List.nil : V2) b5713=b5713 := by rfl
theorem e5928 : o2.mul b5628 b67=b5713 := @mul_cons V1 _ o1 (List.nil : V1) b5630 b67 b5714 (List.nil : V2) b5713 b5713 e5926 e5609 (by rfl) e5927
theorem e5929 : o2.add (List.nil : V2) b5712=b5712 := by rfl
theorem e5930 : o2.mul b5626 b67=b5712 := @mul_cons V1 _ o1 (List.nil : V1) b5628 b67 b5713 (List.nil : V2) b5712 b5712 e5928 e5609 (by rfl) e5929
theorem e5931 : o2.add (List.nil : V2) b5711=b5711 := by rfl
theorem e5932 : o2.mul b5624 b67=b5711 := @mul_cons V1 _ o1 (List.nil : V1) b5626 b67 b5712 (List.nil : V2) b5711 b5711 e5930 e5609 (by rfl) e5931
theorem e5933 : o2.add (List.nil : V2) b5611=b5611 := by rfl
theorem e5934 : o2.mul b325 b67=b5611 := @mul_cons V1 _ o1 (List.nil : V1) b5624 b67 b5711 (List.nil : V2) b5611 b5611 e5932 e5609 (by rfl) e5933
theorem e5935 : o1.mul b324 b68=b5621 := by decide
theorem e5936 : o1.scale b324 b69=b5761 := @scale_cons V1 _ o1 b324 b68 b5621 (List.nil : V2) (List.nil : V2) b5761 e5935 e5703 (by rfl)
theorem e5937 : o2.add b5761 (List.nil : V2)=b5761 := by rfl
theorem e5938 : o2.mul b5652 b69=b5761 := @mul_cons V1 _ o1 b324 (List.nil : V2) b69 (List.nil : V2) b5761 (List.nil : V2) b5761 e5622 e5936 (by rfl) e5937
theorem e5939 : o1.mul b323 b68=b5620 := by decide
theorem e5940 : o1.scale b323 b69=b5762 := @scale_cons V1 _ o1 b323 b68 b5620 (List.nil : V2) (List.nil : V2) b5762 e5939 e5708 (by rfl)
theorem e5941 : o1.add b5620 (List.nil : V1)=b5620 := by rfl
theorem e5942 : o2.add (List.nil : V2) b5761=b5761 := by rfl
theorem e5943 : o2.add b5762 b5763=b5760 := @add_cons V1 _ o1 b5620 (List.nil : V1) b5620 (List.nil : V2) b5761 b5761 b5760 e5941 e5942 (by rfl)
theorem e5944 : o2.mul b5650 b69=b5760 := @mul_cons V1 _ o1 b323 b5652 b69 b5761 b5762 b5763 b5760 e5938 e5940 (by rfl) e5943
theorem e5945 : o1.mul b322 b68=b5619 := by decide
theorem e5946 : o1.scale b322 b69=b5764 := @scale_cons V1 _ o1 b322 b68 b5619 (List.nil : V2) (List.nil : V2) b5764 e5945 e5715 (by rfl)
theorem e5947 : o1.add b5619 (List.nil : V1)=b5619 := by rfl
theorem e5948 : o2.add (List.nil : V2) b5760=b5760 := by rfl
theorem e5949 : o2.add b5764 b5765=b5759 := @add_cons V1 _ o1 b5619 (List.nil : V1) b5619 (List.nil : V2) b5760 b5760 b5759 e5947 e5948 (by rfl)
theorem e5950 : o2.mul b5648 b69=b5759 := @mul_cons V1 _ o1 b322 b5650 b69 b5760 b5764 b5765 b5759 e5944 e5946 (by rfl) e5949
theorem e5951 : o1.mul b321 b68=b5618 := by decide
theorem e5952 : o1.scale b321 b69=b5766 := @scale_cons V1 _ o1 b321 b68 b5618 (List.nil : V2) (List.nil : V2) b5766 e5951 e5722 (by rfl)
theorem e5953 : o1.add b5618 (List.nil : V1)=b5618 := by rfl
theorem e5954 : o2.add (List.nil : V2) b5759=b5759 := by rfl
theorem e5955 : o2.add b5766 b5767=b5758 := @add_cons V1 _ o1 b5618 (List.nil : V1) b5618 (List.nil : V2) b5759 b5759 b5758 e5953 e5954 (by rfl)
theorem e5956 : o2.mul b5646 b69=b5758 := @mul_cons V1 _ o1 b321 b5648 b69 b5759 b5766 b5767 b5758 e5950 e5952 (by rfl) e5955
theorem e5957 : o1.mul b320 b68=b5617 := by decide
theorem e5958 : o1.scale b320 b69=b5768 := @scale_cons V1 _ o1 b320 b68 b5617 (List.nil : V2) (List.nil : V2) b5768 e5957 e5729 (by rfl)
theorem e5959 : o1.add b5617 (List.nil : V1)=b5617 := by rfl
theorem e5960 : o2.add (List.nil : V2) b5758=b5758 := by rfl
theorem e5961 : o2.add b5768 b5769=b5757 := @add_cons V1 _ o1 b5617 (List.nil : V1) b5617 (List.nil : V2) b5758 b5758 b5757 e5959 e5960 (by rfl)
theorem e5962 : o2.mul b5644 b69=b5757 := @mul_cons V1 _ o1 b320 b5646 b69 b5758 b5768 b5769 b5757 e5956 e5958 (by rfl) e5961
theorem e5963 : o1.mul b319 b68=b5616 := by decide
theorem e5964 : o1.scale b319 b69=b5770 := @scale_cons V1 _ o1 b319 b68 b5616 (List.nil : V2) (List.nil : V2) b5770 e5963 e5736 (by rfl)
theorem e5965 : o1.add b5616 (List.nil : V1)=b5616 := by rfl
theorem e5966 : o2.add (List.nil : V2) b5757=b5757 := by rfl
theorem e5967 : o2.add b5770 b5771=b5756 := @add_cons V1 _ o1 b5616 (List.nil : V1) b5616 (List.nil : V2) b5757 b5757 b5756 e5965 e5966 (by rfl)
theorem e5968 : o2.mul b5642 b69=b5756 := @mul_cons V1 _ o1 b319 b5644 b69 b5757 b5770 b5771 b5756 e5962 e5964 (by rfl) e5967
theorem e5969 : o1.mul b318 b68=b5615 := by decide
theorem e5970 : o1.scale b318 b69=b5772 := @scale_cons V1 _ o1 b318 b68 b5615 (List.nil : V2) (List.nil : V2) b5772 e5969 e5743 (by rfl)
theorem e5971 : o1.add b5615 (List.nil : V1)=b5615 := by rfl
theorem e5972 : o2.add (List.nil : V2) b5756=b5756 := by rfl
theorem e5973 : o2.add b5772 b5773=b5755 := @add_cons V1 _ o1 b5615 (List.nil : V1) b5615 (List.nil : V2) b5756 b5756 b5755 e5971 e5972 (by rfl)
theorem e5974 : o2.mul b5640 b69=b5755 := @mul_cons V1 _ o1 b318 b5642 b69 b5756 b5772 b5773 b5755 e5968 e5970 (by rfl) e5973
theorem e5975 : o1.mul b317 b68=b5614 := by decide
theorem e5976 : o1.scale b317 b69=b5774 := @scale_cons V1 _ o1 b317 b68 b5614 (List.nil : V2) (List.nil : V2) b5774 e5975 e5750 (by rfl)
theorem e5977 : o1.add b5614 (List.nil : V1)=b5614 := by rfl
theorem e5978 : o2.add (List.nil : V2) b5755=b5755 := by rfl
theorem e5979 : o2.add b5774 b5775=b5754 := @add_cons V1 _ o1 b5614 (List.nil : V1) b5614 (List.nil : V2) b5755 b5755 b5754 e5977 e5978 (by rfl)
theorem e5980 : o2.mul b5638 b69=b5754 := @mul_cons V1 _ o1 b317 b5640 b69 b5755 b5774 b5775 b5754 e5974 e5976 (by rfl) e5979
theorem e5981 : o1.mul b316 b68=b5613 := by decide
theorem e5982 : o1.scale b316 b69=b5776 := @scale_cons V1 _ o1 b316 b68 b5613 (List.nil : V2) (List.nil : V2) b5776 e5981 e5757 (by rfl)
theorem e5983 : o1.add b5613 (List.nil : V1)=b5613 := by rfl
theorem e5984 : o2.add (List.nil : V2) b5754=b5754 := by rfl
theorem e5985 : o2.add b5776 b5777=b5753 := @add_cons V1 _ o1 b5613 (List.nil : V1) b5613 (List.nil : V2) b5754 b5754 b5753 e5983 e5984 (by rfl)
theorem e5986 : o2.mul b5636 b69=b5753 := @mul_cons V1 _ o1 b316 b5638 b69 b5754 b5776 b5777 b5753 e5980 e5982 (by rfl) e5985
theorem e5987 : o1.mul b315 b68=b5612 := by decide
theorem e5988 : o1.scale b315 b69=b5778 := @scale_cons V1 _ o1 b315 b68 b5612 (List.nil : V2) (List.nil : V2) b5778 e5987 e5764 (by rfl)
theorem e5989 : o1.add b5612 (List.nil : V1)=b5612 := by rfl
theorem e5990 : o2.add (List.nil : V2) b5753=b5753 := by rfl
theorem e5991 : o2.add b5778 b5779=b5752 := @add_cons V1 _ o1 b5612 (List.nil : V1) b5612 (List.nil : V2) b5753 b5753 b5752 e5989 e5990 (by rfl)
theorem e5992 : o2.mul b5634 b69=b5752 := @mul_cons V1 _ o1 b315 b5636 b69 b5753 b5778 b5779 b5752 e5986 e5988 (by rfl) e5991
theorem e5993 : o1.mul b314 b68=b5208 := by decide
theorem e5994 : o1.scale b314 b69=b5780 := @scale_cons V1 _ o1 b314 b68 b5208 (List.nil : V2) (List.nil : V2) b5780 e5993 e5771 (by rfl)
theorem e5995 : o1.add b5208 (List.nil : V1)=b5208 := by rfl
theorem e5996 : o2.add (List.nil : V2) b5752=b5752 := by rfl
theorem e5997 : o2.add b5780 b5781=b5751 := @add_cons V1 _ o1 b5208 (List.nil : V1) b5208 (List.nil : V2) b5752 b5752 b5751 e5995 e5996 (by rfl)
theorem e5998 : o2.mul b5632 b69=b5751 := @mul_cons V1 _ o1 b314 b5634 b69 b5752 b5780 b5781 b5751 e5992 e5994 (by rfl) e5997
theorem e5999 : o2.add (List.nil : V2) b5750=b5750 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
