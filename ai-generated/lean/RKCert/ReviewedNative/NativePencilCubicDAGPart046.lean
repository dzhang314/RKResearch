module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart045

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6750 : o2.mul b6133 b67=b6223 := @mul_cons V1 _ o1 b290 b6135 b67 b6224 b6249 b6250 b6223 e6744 e6746 (by rfl) e6749
theorem e6751 : o1.mul b289 b66=b6097 := by decide
theorem e6752 : o1.scale b289 b67=b6251 := @scale_cons V1 _ o1 b289 b66 b6097 (List.nil : V2) (List.nil : V2) b6251 e6751 e6585 (by rfl)
theorem e6753 : o1.add b6097 (List.nil : V1)=b6097 := by rfl
theorem e6754 : o2.add (List.nil : V2) b6223=b6223 := by rfl
theorem e6755 : o2.add b6251 b6252=b6222 := @add_cons V1 _ o1 b6097 (List.nil : V1) b6097 (List.nil : V2) b6223 b6223 b6222 e6753 e6754 (by rfl)
theorem e6756 : o2.mul b6131 b67=b6222 := @mul_cons V1 _ o1 b289 b6133 b67 b6223 b6251 b6252 b6222 e6750 e6752 (by rfl) e6755
theorem e6757 : o1.mul b288 b66=b6096 := by decide
theorem e6758 : o1.scale b288 b67=b6253 := @scale_cons V1 _ o1 b288 b66 b6096 (List.nil : V2) (List.nil : V2) b6253 e6757 e6592 (by rfl)
theorem e6759 : o1.add b6096 (List.nil : V1)=b6096 := by rfl
theorem e6760 : o2.add (List.nil : V2) b6222=b6222 := by rfl
theorem e6761 : o2.add b6253 b6254=b6221 := @add_cons V1 _ o1 b6096 (List.nil : V1) b6096 (List.nil : V2) b6222 b6222 b6221 e6759 e6760 (by rfl)
theorem e6762 : o2.mul b6129 b67=b6221 := @mul_cons V1 _ o1 b288 b6131 b67 b6222 b6253 b6254 b6221 e6756 e6758 (by rfl) e6761
theorem e6763 : o1.mul b287 b66=b5308 := by decide
theorem e6764 : o1.scale b287 b67=b6255 := @scale_cons V1 _ o1 b287 b66 b5308 (List.nil : V2) (List.nil : V2) b6255 e6763 e6599 (by rfl)
theorem e6765 : o1.add b5308 (List.nil : V1)=b5308 := by rfl
theorem e6766 : o2.add (List.nil : V2) b6221=b6221 := by rfl
theorem e6767 : o2.add b6255 b6256=b6220 := @add_cons V1 _ o1 b5308 (List.nil : V1) b5308 (List.nil : V2) b6221 b6221 b6220 e6765 e6766 (by rfl)
theorem e6768 : o2.mul b6127 b67=b6220 := @mul_cons V1 _ o1 b287 b6129 b67 b6221 b6255 b6256 b6220 e6762 e6764 (by rfl) e6767
theorem e6769 : o2.add (List.nil : V2) b6219=b6219 := by rfl
theorem e6770 : o2.mul b6125 b67=b6219 := @mul_cons V1 _ o1 (List.nil : V1) b6127 b67 b6220 (List.nil : V2) b6219 b6219 e6768 e5609 (by rfl) e6769
theorem e6771 : o2.add (List.nil : V2) b6218=b6218 := by rfl
theorem e6772 : o2.mul b6123 b67=b6218 := @mul_cons V1 _ o1 (List.nil : V1) b6125 b67 b6219 (List.nil : V2) b6218 b6218 e6770 e5609 (by rfl) e6771
theorem e6773 : o2.add (List.nil : V2) b6108=b6108 := by rfl
theorem e6774 : o2.mul b300 b67=b6108 := @mul_cons V1 _ o1 (List.nil : V1) b6123 b67 b6218 (List.nil : V2) b6108 b6108 e6772 e5609 (by rfl) e6773
theorem e6775 : o1.mul b299 b68=b6120 := by decide
theorem e6776 : o1.scale b299 b69=b6272 := @scale_cons V1 _ o1 b299 b68 b6120 (List.nil : V2) (List.nil : V2) b6272 e6775 e6517 (by rfl)
theorem e6777 : o2.add b6272 (List.nil : V2)=b6272 := by rfl
theorem e6778 : o2.mul b6151 b69=b6272 := @mul_cons V1 _ o1 b299 (List.nil : V2) b69 (List.nil : V2) b6272 (List.nil : V2) b6272 e5622 e6776 (by rfl) e6777
theorem e6779 : o1.mul b298 b68=b6119 := by decide
theorem e6780 : o1.scale b298 b69=b6273 := @scale_cons V1 _ o1 b298 b68 b6119 (List.nil : V2) (List.nil : V2) b6273 e6779 e6522 (by rfl)
theorem e6781 : o1.add b6119 (List.nil : V1)=b6119 := by rfl
theorem e6782 : o2.add (List.nil : V2) b6272=b6272 := by rfl
theorem e6783 : o2.add b6273 b6274=b6271 := @add_cons V1 _ o1 b6119 (List.nil : V1) b6119 (List.nil : V2) b6272 b6272 b6271 e6781 e6782 (by rfl)
theorem e6784 : o2.mul b6149 b69=b6271 := @mul_cons V1 _ o1 b298 b6151 b69 b6272 b6273 b6274 b6271 e6778 e6780 (by rfl) e6783
theorem e6785 : o1.mul b297 b68=b6118 := by decide
theorem e6786 : o1.scale b297 b69=b6275 := @scale_cons V1 _ o1 b297 b68 b6118 (List.nil : V2) (List.nil : V2) b6275 e6785 e6529 (by rfl)
theorem e6787 : o1.add b6118 (List.nil : V1)=b6118 := by rfl
theorem e6788 : o2.add (List.nil : V2) b6271=b6271 := by rfl
theorem e6789 : o2.add b6275 b6276=b6270 := @add_cons V1 _ o1 b6118 (List.nil : V1) b6118 (List.nil : V2) b6271 b6271 b6270 e6787 e6788 (by rfl)
theorem e6790 : o2.mul b6147 b69=b6270 := @mul_cons V1 _ o1 b297 b6149 b69 b6271 b6275 b6276 b6270 e6784 e6786 (by rfl) e6789
theorem e6791 : o1.mul b296 b68=b6117 := by decide
theorem e6792 : o1.scale b296 b69=b6277 := @scale_cons V1 _ o1 b296 b68 b6117 (List.nil : V2) (List.nil : V2) b6277 e6791 e6536 (by rfl)
theorem e6793 : o1.add b6117 (List.nil : V1)=b6117 := by rfl
theorem e6794 : o2.add (List.nil : V2) b6270=b6270 := by rfl
theorem e6795 : o2.add b6277 b6278=b6269 := @add_cons V1 _ o1 b6117 (List.nil : V1) b6117 (List.nil : V2) b6270 b6270 b6269 e6793 e6794 (by rfl)
theorem e6796 : o2.mul b6145 b69=b6269 := @mul_cons V1 _ o1 b296 b6147 b69 b6270 b6277 b6278 b6269 e6790 e6792 (by rfl) e6795
theorem e6797 : o1.mul b295 b68=b6116 := by decide
theorem e6798 : o1.scale b295 b69=b6279 := @scale_cons V1 _ o1 b295 b68 b6116 (List.nil : V2) (List.nil : V2) b6279 e6797 e6543 (by rfl)
theorem e6799 : o1.add b6116 (List.nil : V1)=b6116 := by rfl
theorem e6800 : o2.add (List.nil : V2) b6269=b6269 := by rfl
theorem e6801 : o2.add b6279 b6280=b6268 := @add_cons V1 _ o1 b6116 (List.nil : V1) b6116 (List.nil : V2) b6269 b6269 b6268 e6799 e6800 (by rfl)
theorem e6802 : o2.mul b6143 b69=b6268 := @mul_cons V1 _ o1 b295 b6145 b69 b6269 b6279 b6280 b6268 e6796 e6798 (by rfl) e6801
theorem e6803 : o1.mul b294 b68=b6115 := by decide
theorem e6804 : o1.scale b294 b69=b6281 := @scale_cons V1 _ o1 b294 b68 b6115 (List.nil : V2) (List.nil : V2) b6281 e6803 e6550 (by rfl)
theorem e6805 : o1.add b6115 (List.nil : V1)=b6115 := by rfl
theorem e6806 : o2.add (List.nil : V2) b6268=b6268 := by rfl
theorem e6807 : o2.add b6281 b6282=b6267 := @add_cons V1 _ o1 b6115 (List.nil : V1) b6115 (List.nil : V2) b6268 b6268 b6267 e6805 e6806 (by rfl)
theorem e6808 : o2.mul b6141 b69=b6267 := @mul_cons V1 _ o1 b294 b6143 b69 b6268 b6281 b6282 b6267 e6802 e6804 (by rfl) e6807
theorem e6809 : o1.mul b293 b68=b6114 := by decide
theorem e6810 : o1.scale b293 b69=b6283 := @scale_cons V1 _ o1 b293 b68 b6114 (List.nil : V2) (List.nil : V2) b6283 e6809 e6557 (by rfl)
theorem e6811 : o1.add b6114 (List.nil : V1)=b6114 := by rfl
theorem e6812 : o2.add (List.nil : V2) b6267=b6267 := by rfl
theorem e6813 : o2.add b6283 b6284=b6266 := @add_cons V1 _ o1 b6114 (List.nil : V1) b6114 (List.nil : V2) b6267 b6267 b6266 e6811 e6812 (by rfl)
theorem e6814 : o2.mul b6139 b69=b6266 := @mul_cons V1 _ o1 b293 b6141 b69 b6267 b6283 b6284 b6266 e6808 e6810 (by rfl) e6813
theorem e6815 : o1.mul b292 b68=b6113 := by decide
theorem e6816 : o1.scale b292 b69=b6285 := @scale_cons V1 _ o1 b292 b68 b6113 (List.nil : V2) (List.nil : V2) b6285 e6815 e6564 (by rfl)
theorem e6817 : o1.add b6113 (List.nil : V1)=b6113 := by rfl
theorem e6818 : o2.add (List.nil : V2) b6266=b6266 := by rfl
theorem e6819 : o2.add b6285 b6286=b6265 := @add_cons V1 _ o1 b6113 (List.nil : V1) b6113 (List.nil : V2) b6266 b6266 b6265 e6817 e6818 (by rfl)
theorem e6820 : o2.mul b6137 b69=b6265 := @mul_cons V1 _ o1 b292 b6139 b69 b6266 b6285 b6286 b6265 e6814 e6816 (by rfl) e6819
theorem e6821 : o1.mul b291 b68=b6112 := by decide
theorem e6822 : o1.scale b291 b69=b6287 := @scale_cons V1 _ o1 b291 b68 b6112 (List.nil : V2) (List.nil : V2) b6287 e6821 e6571 (by rfl)
theorem e6823 : o1.add b6112 (List.nil : V1)=b6112 := by rfl
theorem e6824 : o2.add (List.nil : V2) b6265=b6265 := by rfl
theorem e6825 : o2.add b6287 b6288=b6264 := @add_cons V1 _ o1 b6112 (List.nil : V1) b6112 (List.nil : V2) b6265 b6265 b6264 e6823 e6824 (by rfl)
theorem e6826 : o2.mul b6135 b69=b6264 := @mul_cons V1 _ o1 b291 b6137 b69 b6265 b6287 b6288 b6264 e6820 e6822 (by rfl) e6825
theorem e6827 : o1.mul b290 b68=b6111 := by decide
theorem e6828 : o1.scale b290 b69=b6289 := @scale_cons V1 _ o1 b290 b68 b6111 (List.nil : V2) (List.nil : V2) b6289 e6827 e6578 (by rfl)
theorem e6829 : o1.add b6111 (List.nil : V1)=b6111 := by rfl
theorem e6830 : o2.add (List.nil : V2) b6264=b6264 := by rfl
theorem e6831 : o2.add b6289 b6290=b6263 := @add_cons V1 _ o1 b6111 (List.nil : V1) b6111 (List.nil : V2) b6264 b6264 b6263 e6829 e6830 (by rfl)
theorem e6832 : o2.mul b6133 b69=b6263 := @mul_cons V1 _ o1 b290 b6135 b69 b6264 b6289 b6290 b6263 e6826 e6828 (by rfl) e6831
theorem e6833 : o1.mul b289 b68=b6110 := by decide
theorem e6834 : o1.scale b289 b69=b6291 := @scale_cons V1 _ o1 b289 b68 b6110 (List.nil : V2) (List.nil : V2) b6291 e6833 e6585 (by rfl)
theorem e6835 : o1.add b6110 (List.nil : V1)=b6110 := by rfl
theorem e6836 : o2.add (List.nil : V2) b6263=b6263 := by rfl
theorem e6837 : o2.add b6291 b6292=b6262 := @add_cons V1 _ o1 b6110 (List.nil : V1) b6110 (List.nil : V2) b6263 b6263 b6262 e6835 e6836 (by rfl)
theorem e6838 : o2.mul b6131 b69=b6262 := @mul_cons V1 _ o1 b289 b6133 b69 b6263 b6291 b6292 b6262 e6832 e6834 (by rfl) e6837
theorem e6839 : o1.mul b288 b68=b6109 := by decide
theorem e6840 : o1.scale b288 b69=b6293 := @scale_cons V1 _ o1 b288 b68 b6109 (List.nil : V2) (List.nil : V2) b6293 e6839 e6592 (by rfl)
theorem e6841 : o1.add b6109 (List.nil : V1)=b6109 := by rfl
theorem e6842 : o2.add (List.nil : V2) b6262=b6262 := by rfl
theorem e6843 : o2.add b6293 b6294=b6261 := @add_cons V1 _ o1 b6109 (List.nil : V1) b6109 (List.nil : V2) b6262 b6262 b6261 e6841 e6842 (by rfl)
theorem e6844 : o2.mul b6129 b69=b6261 := @mul_cons V1 _ o1 b288 b6131 b69 b6262 b6293 b6294 b6261 e6838 e6840 (by rfl) e6843
theorem e6845 : o1.mul b287 b68=b5181 := by decide
theorem e6846 : o1.scale b287 b69=b6295 := @scale_cons V1 _ o1 b287 b68 b5181 (List.nil : V2) (List.nil : V2) b6295 e6845 e6599 (by rfl)
theorem e6847 : o1.add b5181 (List.nil : V1)=b5181 := by rfl
theorem e6848 : o2.add (List.nil : V2) b6261=b6261 := by rfl
theorem e6849 : o2.add b6295 b6296=b6260 := @add_cons V1 _ o1 b5181 (List.nil : V1) b5181 (List.nil : V2) b6261 b6261 b6260 e6847 e6848 (by rfl)
theorem e6850 : o2.mul b6127 b69=b6260 := @mul_cons V1 _ o1 b287 b6129 b69 b6261 b6295 b6296 b6260 e6844 e6846 (by rfl) e6849
theorem e6851 : o2.add (List.nil : V2) b6259=b6259 := by rfl
theorem e6852 : o2.mul b6125 b69=b6259 := @mul_cons V1 _ o1 (List.nil : V1) b6127 b69 b6260 (List.nil : V2) b6259 b6259 e6850 e5682 (by rfl) e6851
theorem e6853 : o2.add (List.nil : V2) b6258=b6258 := by rfl
theorem e6854 : o2.mul b6123 b69=b6258 := @mul_cons V1 _ o1 (List.nil : V1) b6125 b69 b6259 (List.nil : V2) b6258 b6258 e6852 e5682 (by rfl) e6853
theorem e6855 : o2.add (List.nil : V2) b6121=b6121 := by rfl
theorem e6856 : o2.mul b300 b69=b6121 := @mul_cons V1 _ o1 (List.nil : V1) b6123 b69 b6258 (List.nil : V2) b6121 b6121 e6854 e5682 (by rfl) e6855
theorem e6857 : o2.scale b300 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e6858 : o2.scale b300 b5555=b6257 := @scale_cons V2 _ o2 b300 b69 b6121 (List.nil : V3) (List.nil : V3) b6257 e6856 e6857 (by rfl)
theorem e6859 : o2.scale b300 b5520=b6217 := @scale_cons V2 _ o2 b300 b67 b6108 b5555 b6257 b6217 e6774 e6858 (by rfl)
theorem e6860 : o2.scale b300 b5485=b6177 := @scale_cons V2 _ o2 b300 b65 b6095 b5520 b6217 b6177 e6692 e6859 (by rfl)
theorem e6861 : o2.scale b300 b70=b6122 := @scale_cons V2 _ o2 b300 b63 b5293 b5485 b6177 b6122 e6610 e6860 (by rfl)
theorem e6862 : o2.add b5293 (List.nil : V2)=b5293 := by rfl
theorem e6863 : o1.add b6083 b5324=b5295 := by decide
theorem e6864 : o1.add b6084 b5325=b5296 := by decide
theorem e6865 : o1.add b6085 b5326=b5297 := by decide
theorem e6866 : o1.add b6086 b5327=b5298 := by decide
theorem e6867 : o1.add b6087 b5328=b5299 := by decide
theorem e6868 : o1.add b6088 b5329=b5300 := by decide
theorem e6869 : o1.add b6089 b5330=b5301 := by decide
theorem e6870 : o1.add b6090 b5331=b5302 := by decide
theorem e6871 : o1.add b6091 b5332=b5303 := by decide
theorem e6872 : o1.add b6092 b5333=b5304 := by decide
theorem e6873 : o1.add b6093 b5334=b5305 := by decide
theorem e6874 : o1.add b6094 b5335=b5306 := by decide
theorem e6875 : o2.add b6192 b5897=b6313 := @add_cons V1 _ o1 b6094 b5335 b5306 (List.nil : V2) (List.nil : V2) (List.nil : V2) b6313 e6874 e2341 (by rfl)
theorem e6876 : o2.add b6191 b5895=b6312 := @add_cons V1 _ o1 b6093 b5334 b5305 b6192 b5897 b6313 b6312 e6873 e6875 (by rfl)
theorem e6877 : o2.add b6190 b5893=b6311 := @add_cons V1 _ o1 b6092 b5333 b5304 b6191 b5895 b6312 b6311 e6872 e6876 (by rfl)
theorem e6878 : o2.add b6189 b5891=b6310 := @add_cons V1 _ o1 b6091 b5332 b5303 b6190 b5893 b6311 b6310 e6871 e6877 (by rfl)
theorem e6879 : o2.add b6188 b5889=b6309 := @add_cons V1 _ o1 b6090 b5331 b5302 b6189 b5891 b6310 b6309 e6870 e6878 (by rfl)
theorem e6880 : o2.add b6187 b5887=b6308 := @add_cons V1 _ o1 b6089 b5330 b5301 b6188 b5889 b6309 b6308 e6869 e6879 (by rfl)
theorem e6881 : o2.add b6186 b5885=b6307 := @add_cons V1 _ o1 b6088 b5329 b5300 b6187 b5887 b6308 b6307 e6868 e6880 (by rfl)
theorem e6882 : o2.add b6185 b5883=b6306 := @add_cons V1 _ o1 b6087 b5328 b5299 b6186 b5885 b6307 b6306 e6867 e6881 (by rfl)
theorem e6883 : o2.add b6184 b5881=b6305 := @add_cons V1 _ o1 b6086 b5327 b5298 b6185 b5883 b6306 b6305 e6866 e6882 (by rfl)
theorem e6884 : o2.add b6183 b5879=b6304 := @add_cons V1 _ o1 b6085 b5326 b5297 b6184 b5881 b6305 b6304 e6865 e6883 (by rfl)
theorem e6885 : o2.add b6182 b5877=b6303 := @add_cons V1 _ o1 b6084 b5325 b5296 b6183 b5879 b6304 b6303 e6864 e6884 (by rfl)
theorem e6886 : o2.add b6181 b5875=b6302 := @add_cons V1 _ o1 b6083 b5324 b5295 b6182 b5877 b6303 b6302 e6863 e6885 (by rfl)
theorem e6887 : o2.add b6180 b5873=b6301 := @add_cons V1 _ o1 b5294 (List.nil : V1) b5294 b6181 b5875 b6302 b6301 e6683 e6886 (by rfl)
theorem e6888 : o2.add b6179 b5871=b6300 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6180 b5873 b6301 b6300 e34 e6887 (by rfl)
theorem e6889 : o2.add b6178 b5869=b6299 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6179 b5871 b6300 b6299 e34 e6888 (by rfl)
theorem e6890 : o2.add b6095 b5336=b5307 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6178 b5869 b6299 b5307 e34 e6889 (by rfl)
theorem e6891 : o1.add b6096 b5337=b5309 := by decide
theorem e6892 : o1.add b6097 b5338=b5310 := by decide
theorem e6893 : o1.add b6098 b5339=b5311 := by decide
theorem e6894 : o1.add b6099 b5340=b5312 := by decide
theorem e6895 : o1.add b6100 b5341=b5313 := by decide
theorem e6896 : o1.add b6101 b5342=b5314 := by decide
theorem e6897 : o1.add b6102 b5343=b5315 := by decide
theorem e6898 : o1.add b6103 b5344=b5316 := by decide
theorem e6899 : o1.add b6104 b5345=b5317 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
