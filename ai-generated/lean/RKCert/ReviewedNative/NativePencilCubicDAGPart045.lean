module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart044

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6600 : o1.scale b287 b63=b6175 := @scale_cons V1 _ o1 b287 b62 b5280 (List.nil : V2) (List.nil : V2) b6175 e6598 e6599 (by rfl)
theorem e6601 : o1.add b5280 (List.nil : V1)=b5280 := by rfl
theorem e6602 : o2.add (List.nil : V2) b6130=b6130 := by rfl
theorem e6603 : o2.add b6175 b6176=b6128 := @add_cons V1 _ o1 b5280 (List.nil : V1) b5280 (List.nil : V2) b6130 b6130 b6128 e6601 e6602 (by rfl)
theorem e6604 : o2.mul b6127 b63=b6128 := @mul_cons V1 _ o1 b287 b6129 b63 b6130 b6175 b6176 b6128 e6597 e6600 (by rfl) e6603
theorem e6605 : o2.add (List.nil : V2) b6126=b6126 := by rfl
theorem e6606 : o2.mul b6125 b63=b6126 := @mul_cons V1 _ o1 (List.nil : V1) b6127 b63 b6128 (List.nil : V2) b6126 b6126 e6604 e5463 (by rfl) e6605
theorem e6607 : o2.add (List.nil : V2) b6124=b6124 := by rfl
theorem e6608 : o2.mul b6123 b63=b6124 := @mul_cons V1 _ o1 (List.nil : V1) b6125 b63 b6126 (List.nil : V2) b6124 b6124 e6606 e5463 (by rfl) e6607
theorem e6609 : o2.add (List.nil : V2) b5293=b5293 := by rfl
theorem e6610 : o2.mul b300 b63=b5293 := @mul_cons V1 _ o1 (List.nil : V1) b6123 b63 b6124 (List.nil : V2) b5293 b5293 e6608 e5463 (by rfl) e6609
theorem e6611 : o1.mul b299 b64=b6094 := by decide
theorem e6612 : o1.scale b299 b65=b6192 := @scale_cons V1 _ o1 b299 b64 b6094 (List.nil : V2) (List.nil : V2) b6192 e6611 e6517 (by rfl)
theorem e6613 : o2.add b6192 (List.nil : V2)=b6192 := by rfl
theorem e6614 : o2.mul b6151 b65=b6192 := @mul_cons V1 _ o1 b299 (List.nil : V2) b65 (List.nil : V2) b6192 (List.nil : V2) b6192 e5476 e6612 (by rfl) e6613
theorem e6615 : o1.mul b298 b64=b6093 := by decide
theorem e6616 : o1.scale b298 b65=b6193 := @scale_cons V1 _ o1 b298 b64 b6093 (List.nil : V2) (List.nil : V2) b6193 e6615 e6522 (by rfl)
theorem e6617 : o1.add b6093 (List.nil : V1)=b6093 := by rfl
theorem e6618 : o2.add (List.nil : V2) b6192=b6192 := by rfl
theorem e6619 : o2.add b6193 b6194=b6191 := @add_cons V1 _ o1 b6093 (List.nil : V1) b6093 (List.nil : V2) b6192 b6192 b6191 e6617 e6618 (by rfl)
theorem e6620 : o2.mul b6149 b65=b6191 := @mul_cons V1 _ o1 b298 b6151 b65 b6192 b6193 b6194 b6191 e6614 e6616 (by rfl) e6619
theorem e6621 : o1.mul b297 b64=b6092 := by decide
theorem e6622 : o1.scale b297 b65=b6195 := @scale_cons V1 _ o1 b297 b64 b6092 (List.nil : V2) (List.nil : V2) b6195 e6621 e6529 (by rfl)
theorem e6623 : o1.add b6092 (List.nil : V1)=b6092 := by rfl
theorem e6624 : o2.add (List.nil : V2) b6191=b6191 := by rfl
theorem e6625 : o2.add b6195 b6196=b6190 := @add_cons V1 _ o1 b6092 (List.nil : V1) b6092 (List.nil : V2) b6191 b6191 b6190 e6623 e6624 (by rfl)
theorem e6626 : o2.mul b6147 b65=b6190 := @mul_cons V1 _ o1 b297 b6149 b65 b6191 b6195 b6196 b6190 e6620 e6622 (by rfl) e6625
theorem e6627 : o1.mul b296 b64=b6091 := by decide
theorem e6628 : o1.scale b296 b65=b6197 := @scale_cons V1 _ o1 b296 b64 b6091 (List.nil : V2) (List.nil : V2) b6197 e6627 e6536 (by rfl)
theorem e6629 : o1.add b6091 (List.nil : V1)=b6091 := by rfl
theorem e6630 : o2.add (List.nil : V2) b6190=b6190 := by rfl
theorem e6631 : o2.add b6197 b6198=b6189 := @add_cons V1 _ o1 b6091 (List.nil : V1) b6091 (List.nil : V2) b6190 b6190 b6189 e6629 e6630 (by rfl)
theorem e6632 : o2.mul b6145 b65=b6189 := @mul_cons V1 _ o1 b296 b6147 b65 b6190 b6197 b6198 b6189 e6626 e6628 (by rfl) e6631
theorem e6633 : o1.mul b295 b64=b6090 := by decide
theorem e6634 : o1.scale b295 b65=b6199 := @scale_cons V1 _ o1 b295 b64 b6090 (List.nil : V2) (List.nil : V2) b6199 e6633 e6543 (by rfl)
theorem e6635 : o1.add b6090 (List.nil : V1)=b6090 := by rfl
theorem e6636 : o2.add (List.nil : V2) b6189=b6189 := by rfl
theorem e6637 : o2.add b6199 b6200=b6188 := @add_cons V1 _ o1 b6090 (List.nil : V1) b6090 (List.nil : V2) b6189 b6189 b6188 e6635 e6636 (by rfl)
theorem e6638 : o2.mul b6143 b65=b6188 := @mul_cons V1 _ o1 b295 b6145 b65 b6189 b6199 b6200 b6188 e6632 e6634 (by rfl) e6637
theorem e6639 : o1.mul b294 b64=b6089 := by decide
theorem e6640 : o1.scale b294 b65=b6201 := @scale_cons V1 _ o1 b294 b64 b6089 (List.nil : V2) (List.nil : V2) b6201 e6639 e6550 (by rfl)
theorem e6641 : o1.add b6089 (List.nil : V1)=b6089 := by rfl
theorem e6642 : o2.add (List.nil : V2) b6188=b6188 := by rfl
theorem e6643 : o2.add b6201 b6202=b6187 := @add_cons V1 _ o1 b6089 (List.nil : V1) b6089 (List.nil : V2) b6188 b6188 b6187 e6641 e6642 (by rfl)
theorem e6644 : o2.mul b6141 b65=b6187 := @mul_cons V1 _ o1 b294 b6143 b65 b6188 b6201 b6202 b6187 e6638 e6640 (by rfl) e6643
theorem e6645 : o1.mul b293 b64=b6088 := by decide
theorem e6646 : o1.scale b293 b65=b6203 := @scale_cons V1 _ o1 b293 b64 b6088 (List.nil : V2) (List.nil : V2) b6203 e6645 e6557 (by rfl)
theorem e6647 : o1.add b6088 (List.nil : V1)=b6088 := by rfl
theorem e6648 : o2.add (List.nil : V2) b6187=b6187 := by rfl
theorem e6649 : o2.add b6203 b6204=b6186 := @add_cons V1 _ o1 b6088 (List.nil : V1) b6088 (List.nil : V2) b6187 b6187 b6186 e6647 e6648 (by rfl)
theorem e6650 : o2.mul b6139 b65=b6186 := @mul_cons V1 _ o1 b293 b6141 b65 b6187 b6203 b6204 b6186 e6644 e6646 (by rfl) e6649
theorem e6651 : o1.mul b292 b64=b6087 := by decide
theorem e6652 : o1.scale b292 b65=b6205 := @scale_cons V1 _ o1 b292 b64 b6087 (List.nil : V2) (List.nil : V2) b6205 e6651 e6564 (by rfl)
theorem e6653 : o1.add b6087 (List.nil : V1)=b6087 := by rfl
theorem e6654 : o2.add (List.nil : V2) b6186=b6186 := by rfl
theorem e6655 : o2.add b6205 b6206=b6185 := @add_cons V1 _ o1 b6087 (List.nil : V1) b6087 (List.nil : V2) b6186 b6186 b6185 e6653 e6654 (by rfl)
theorem e6656 : o2.mul b6137 b65=b6185 := @mul_cons V1 _ o1 b292 b6139 b65 b6186 b6205 b6206 b6185 e6650 e6652 (by rfl) e6655
theorem e6657 : o1.mul b291 b64=b6086 := by decide
theorem e6658 : o1.scale b291 b65=b6207 := @scale_cons V1 _ o1 b291 b64 b6086 (List.nil : V2) (List.nil : V2) b6207 e6657 e6571 (by rfl)
theorem e6659 : o1.add b6086 (List.nil : V1)=b6086 := by rfl
theorem e6660 : o2.add (List.nil : V2) b6185=b6185 := by rfl
theorem e6661 : o2.add b6207 b6208=b6184 := @add_cons V1 _ o1 b6086 (List.nil : V1) b6086 (List.nil : V2) b6185 b6185 b6184 e6659 e6660 (by rfl)
theorem e6662 : o2.mul b6135 b65=b6184 := @mul_cons V1 _ o1 b291 b6137 b65 b6185 b6207 b6208 b6184 e6656 e6658 (by rfl) e6661
theorem e6663 : o1.mul b290 b64=b6085 := by decide
theorem e6664 : o1.scale b290 b65=b6209 := @scale_cons V1 _ o1 b290 b64 b6085 (List.nil : V2) (List.nil : V2) b6209 e6663 e6578 (by rfl)
theorem e6665 : o1.add b6085 (List.nil : V1)=b6085 := by rfl
theorem e6666 : o2.add (List.nil : V2) b6184=b6184 := by rfl
theorem e6667 : o2.add b6209 b6210=b6183 := @add_cons V1 _ o1 b6085 (List.nil : V1) b6085 (List.nil : V2) b6184 b6184 b6183 e6665 e6666 (by rfl)
theorem e6668 : o2.mul b6133 b65=b6183 := @mul_cons V1 _ o1 b290 b6135 b65 b6184 b6209 b6210 b6183 e6662 e6664 (by rfl) e6667
theorem e6669 : o1.mul b289 b64=b6084 := by decide
theorem e6670 : o1.scale b289 b65=b6211 := @scale_cons V1 _ o1 b289 b64 b6084 (List.nil : V2) (List.nil : V2) b6211 e6669 e6585 (by rfl)
theorem e6671 : o1.add b6084 (List.nil : V1)=b6084 := by rfl
theorem e6672 : o2.add (List.nil : V2) b6183=b6183 := by rfl
theorem e6673 : o2.add b6211 b6212=b6182 := @add_cons V1 _ o1 b6084 (List.nil : V1) b6084 (List.nil : V2) b6183 b6183 b6182 e6671 e6672 (by rfl)
theorem e6674 : o2.mul b6131 b65=b6182 := @mul_cons V1 _ o1 b289 b6133 b65 b6183 b6211 b6212 b6182 e6668 e6670 (by rfl) e6673
theorem e6675 : o1.mul b288 b64=b6083 := by decide
theorem e6676 : o1.scale b288 b65=b6213 := @scale_cons V1 _ o1 b288 b64 b6083 (List.nil : V2) (List.nil : V2) b6213 e6675 e6592 (by rfl)
theorem e6677 : o1.add b6083 (List.nil : V1)=b6083 := by rfl
theorem e6678 : o2.add (List.nil : V2) b6182=b6182 := by rfl
theorem e6679 : o2.add b6213 b6214=b6181 := @add_cons V1 _ o1 b6083 (List.nil : V1) b6083 (List.nil : V2) b6182 b6182 b6181 e6677 e6678 (by rfl)
theorem e6680 : o2.mul b6129 b65=b6181 := @mul_cons V1 _ o1 b288 b6131 b65 b6182 b6213 b6214 b6181 e6674 e6676 (by rfl) e6679
theorem e6681 : o1.mul b287 b64=b5294 := by decide
theorem e6682 : o1.scale b287 b65=b6215 := @scale_cons V1 _ o1 b287 b64 b5294 (List.nil : V2) (List.nil : V2) b6215 e6681 e6599 (by rfl)
theorem e6683 : o1.add b5294 (List.nil : V1)=b5294 := by rfl
theorem e6684 : o2.add (List.nil : V2) b6181=b6181 := by rfl
theorem e6685 : o2.add b6215 b6216=b6180 := @add_cons V1 _ o1 b5294 (List.nil : V1) b5294 (List.nil : V2) b6181 b6181 b6180 e6683 e6684 (by rfl)
theorem e6686 : o2.mul b6127 b65=b6180 := @mul_cons V1 _ o1 b287 b6129 b65 b6181 b6215 b6216 b6180 e6680 e6682 (by rfl) e6685
theorem e6687 : o2.add (List.nil : V2) b6179=b6179 := by rfl
theorem e6688 : o2.mul b6125 b65=b6179 := @mul_cons V1 _ o1 (List.nil : V1) b6127 b65 b6180 (List.nil : V2) b6179 b6179 e6686 e5536 (by rfl) e6687
theorem e6689 : o2.add (List.nil : V2) b6178=b6178 := by rfl
theorem e6690 : o2.mul b6123 b65=b6178 := @mul_cons V1 _ o1 (List.nil : V1) b6125 b65 b6179 (List.nil : V2) b6178 b6178 e6688 e5536 (by rfl) e6689
theorem e6691 : o2.add (List.nil : V2) b6095=b6095 := by rfl
theorem e6692 : o2.mul b300 b65=b6095 := @mul_cons V1 _ o1 (List.nil : V1) b6123 b65 b6178 (List.nil : V2) b6095 b6095 e6690 e5536 (by rfl) e6691
theorem e6693 : o1.mul b299 b66=b6107 := by decide
theorem e6694 : o1.scale b299 b67=b6232 := @scale_cons V1 _ o1 b299 b66 b6107 (List.nil : V2) (List.nil : V2) b6232 e6693 e6517 (by rfl)
theorem e6695 : o2.add b6232 (List.nil : V2)=b6232 := by rfl
theorem e6696 : o2.mul b6151 b67=b6232 := @mul_cons V1 _ o1 b299 (List.nil : V2) b67 (List.nil : V2) b6232 (List.nil : V2) b6232 e5549 e6694 (by rfl) e6695
theorem e6697 : o1.mul b298 b66=b6106 := by decide
theorem e6698 : o1.scale b298 b67=b6233 := @scale_cons V1 _ o1 b298 b66 b6106 (List.nil : V2) (List.nil : V2) b6233 e6697 e6522 (by rfl)
theorem e6699 : o1.add b6106 (List.nil : V1)=b6106 := by rfl
theorem e6700 : o2.add (List.nil : V2) b6232=b6232 := by rfl
theorem e6701 : o2.add b6233 b6234=b6231 := @add_cons V1 _ o1 b6106 (List.nil : V1) b6106 (List.nil : V2) b6232 b6232 b6231 e6699 e6700 (by rfl)
theorem e6702 : o2.mul b6149 b67=b6231 := @mul_cons V1 _ o1 b298 b6151 b67 b6232 b6233 b6234 b6231 e6696 e6698 (by rfl) e6701
theorem e6703 : o1.mul b297 b66=b6105 := by decide
theorem e6704 : o1.scale b297 b67=b6235 := @scale_cons V1 _ o1 b297 b66 b6105 (List.nil : V2) (List.nil : V2) b6235 e6703 e6529 (by rfl)
theorem e6705 : o1.add b6105 (List.nil : V1)=b6105 := by rfl
theorem e6706 : o2.add (List.nil : V2) b6231=b6231 := by rfl
theorem e6707 : o2.add b6235 b6236=b6230 := @add_cons V1 _ o1 b6105 (List.nil : V1) b6105 (List.nil : V2) b6231 b6231 b6230 e6705 e6706 (by rfl)
theorem e6708 : o2.mul b6147 b67=b6230 := @mul_cons V1 _ o1 b297 b6149 b67 b6231 b6235 b6236 b6230 e6702 e6704 (by rfl) e6707
theorem e6709 : o1.mul b296 b66=b6104 := by decide
theorem e6710 : o1.scale b296 b67=b6237 := @scale_cons V1 _ o1 b296 b66 b6104 (List.nil : V2) (List.nil : V2) b6237 e6709 e6536 (by rfl)
theorem e6711 : o1.add b6104 (List.nil : V1)=b6104 := by rfl
theorem e6712 : o2.add (List.nil : V2) b6230=b6230 := by rfl
theorem e6713 : o2.add b6237 b6238=b6229 := @add_cons V1 _ o1 b6104 (List.nil : V1) b6104 (List.nil : V2) b6230 b6230 b6229 e6711 e6712 (by rfl)
theorem e6714 : o2.mul b6145 b67=b6229 := @mul_cons V1 _ o1 b296 b6147 b67 b6230 b6237 b6238 b6229 e6708 e6710 (by rfl) e6713
theorem e6715 : o1.mul b295 b66=b6103 := by decide
theorem e6716 : o1.scale b295 b67=b6239 := @scale_cons V1 _ o1 b295 b66 b6103 (List.nil : V2) (List.nil : V2) b6239 e6715 e6543 (by rfl)
theorem e6717 : o1.add b6103 (List.nil : V1)=b6103 := by rfl
theorem e6718 : o2.add (List.nil : V2) b6229=b6229 := by rfl
theorem e6719 : o2.add b6239 b6240=b6228 := @add_cons V1 _ o1 b6103 (List.nil : V1) b6103 (List.nil : V2) b6229 b6229 b6228 e6717 e6718 (by rfl)
theorem e6720 : o2.mul b6143 b67=b6228 := @mul_cons V1 _ o1 b295 b6145 b67 b6229 b6239 b6240 b6228 e6714 e6716 (by rfl) e6719
theorem e6721 : o1.mul b294 b66=b6102 := by decide
theorem e6722 : o1.scale b294 b67=b6241 := @scale_cons V1 _ o1 b294 b66 b6102 (List.nil : V2) (List.nil : V2) b6241 e6721 e6550 (by rfl)
theorem e6723 : o1.add b6102 (List.nil : V1)=b6102 := by rfl
theorem e6724 : o2.add (List.nil : V2) b6228=b6228 := by rfl
theorem e6725 : o2.add b6241 b6242=b6227 := @add_cons V1 _ o1 b6102 (List.nil : V1) b6102 (List.nil : V2) b6228 b6228 b6227 e6723 e6724 (by rfl)
theorem e6726 : o2.mul b6141 b67=b6227 := @mul_cons V1 _ o1 b294 b6143 b67 b6228 b6241 b6242 b6227 e6720 e6722 (by rfl) e6725
theorem e6727 : o1.mul b293 b66=b6101 := by decide
theorem e6728 : o1.scale b293 b67=b6243 := @scale_cons V1 _ o1 b293 b66 b6101 (List.nil : V2) (List.nil : V2) b6243 e6727 e6557 (by rfl)
theorem e6729 : o1.add b6101 (List.nil : V1)=b6101 := by rfl
theorem e6730 : o2.add (List.nil : V2) b6227=b6227 := by rfl
theorem e6731 : o2.add b6243 b6244=b6226 := @add_cons V1 _ o1 b6101 (List.nil : V1) b6101 (List.nil : V2) b6227 b6227 b6226 e6729 e6730 (by rfl)
theorem e6732 : o2.mul b6139 b67=b6226 := @mul_cons V1 _ o1 b293 b6141 b67 b6227 b6243 b6244 b6226 e6726 e6728 (by rfl) e6731
theorem e6733 : o1.mul b292 b66=b6100 := by decide
theorem e6734 : o1.scale b292 b67=b6245 := @scale_cons V1 _ o1 b292 b66 b6100 (List.nil : V2) (List.nil : V2) b6245 e6733 e6564 (by rfl)
theorem e6735 : o1.add b6100 (List.nil : V1)=b6100 := by rfl
theorem e6736 : o2.add (List.nil : V2) b6226=b6226 := by rfl
theorem e6737 : o2.add b6245 b6246=b6225 := @add_cons V1 _ o1 b6100 (List.nil : V1) b6100 (List.nil : V2) b6226 b6226 b6225 e6735 e6736 (by rfl)
theorem e6738 : o2.mul b6137 b67=b6225 := @mul_cons V1 _ o1 b292 b6139 b67 b6226 b6245 b6246 b6225 e6732 e6734 (by rfl) e6737
theorem e6739 : o1.mul b291 b66=b6099 := by decide
theorem e6740 : o1.scale b291 b67=b6247 := @scale_cons V1 _ o1 b291 b66 b6099 (List.nil : V2) (List.nil : V2) b6247 e6739 e6571 (by rfl)
theorem e6741 : o1.add b6099 (List.nil : V1)=b6099 := by rfl
theorem e6742 : o2.add (List.nil : V2) b6225=b6225 := by rfl
theorem e6743 : o2.add b6247 b6248=b6224 := @add_cons V1 _ o1 b6099 (List.nil : V1) b6099 (List.nil : V2) b6225 b6225 b6224 e6741 e6742 (by rfl)
theorem e6744 : o2.mul b6135 b67=b6224 := @mul_cons V1 _ o1 b291 b6137 b67 b6225 b6247 b6248 b6224 e6738 e6740 (by rfl) e6743
theorem e6745 : o1.mul b290 b66=b6098 := by decide
theorem e6746 : o1.scale b290 b67=b6249 := @scale_cons V1 _ o1 b290 b66 b6098 (List.nil : V2) (List.nil : V2) b6249 e6745 e6578 (by rfl)
theorem e6747 : o1.add b6098 (List.nil : V1)=b6098 := by rfl
theorem e6748 : o2.add (List.nil : V2) b6224=b6224 := by rfl
theorem e6749 : o2.add b6249 b6250=b6223 := @add_cons V1 _ o1 b6098 (List.nil : V1) b6098 (List.nil : V2) b6224 b6224 b6223 e6747 e6748 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
