module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart040

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6000 : o2.mul b5630 b69=b5750 := @mul_cons V1 _ o1 (List.nil : V1) b5632 b69 b5751 (List.nil : V2) b5750 b5750 e5998 e5682 (by rfl) e5999
theorem e6001 : o2.add (List.nil : V2) b5749=b5749 := by rfl
theorem e6002 : o2.mul b5628 b69=b5749 := @mul_cons V1 _ o1 (List.nil : V1) b5630 b69 b5750 (List.nil : V2) b5749 b5749 e6000 e5682 (by rfl) e6001
theorem e6003 : o2.add (List.nil : V2) b5748=b5748 := by rfl
theorem e6004 : o2.mul b5626 b69=b5748 := @mul_cons V1 _ o1 (List.nil : V1) b5628 b69 b5749 (List.nil : V2) b5748 b5748 e6002 e5682 (by rfl) e6003
theorem e6005 : o2.add (List.nil : V2) b5747=b5747 := by rfl
theorem e6006 : o2.mul b5624 b69=b5747 := @mul_cons V1 _ o1 (List.nil : V1) b5626 b69 b5748 (List.nil : V2) b5747 b5747 e6004 e5682 (by rfl) e6005
theorem e6007 : o2.add (List.nil : V2) b5622=b5622 := by rfl
theorem e6008 : o2.mul b325 b69=b5622 := @mul_cons V1 _ o1 (List.nil : V1) b5624 b69 b5747 (List.nil : V2) b5622 b5622 e6006 e5682 (by rfl) e6007
theorem e6009 : o2.scale b325 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e6010 : o2.scale b325 b5555=b5746 := @scale_cons V2 _ o2 b325 b69 b5622 (List.nil : V3) (List.nil : V3) b5746 e6008 e6009 (by rfl)
theorem e6011 : o2.scale b325 b5520=b5710 := @scale_cons V2 _ o2 b325 b67 b5611 b5555 b5746 b5710 e5934 e6010 (by rfl)
theorem e6012 : o2.scale b325 b5485=b5674 := @scale_cons V2 _ o2 b325 b65 b5600 b5520 b5710 b5674 e5860 e6011 (by rfl)
theorem e6013 : o2.scale b325 b70=b5623 := @scale_cons V2 _ o2 b325 b63 b5376 b5485 b5674 b5623 e5786 e6012 (by rfl)
theorem e6014 : o2.add b5376 (List.nil : V2)=b5376 := by rfl
theorem e6015 : o1.add b5590 b5403=b5378 := by decide
theorem e6016 : o1.add b5591 b5404=b5379 := by decide
theorem e6017 : o1.add b5592 b5405=b5380 := by decide
theorem e6018 : o1.add b5593 b5406=b5381 := by decide
theorem e6019 : o1.add b5594 b5407=b5382 := by decide
theorem e6020 : o1.add b5595 b5408=b5383 := by decide
theorem e6021 : o1.add b5596 b5409=b5384 := by decide
theorem e6022 : o1.add b5597 b5410=b5385 := by decide
theorem e6023 : o1.add b5598 b5411=b5386 := by decide
theorem e6024 : o1.add b5599 b5412=b5387 := by decide
theorem e6025 : o2.add b5689 b5466=b5798 := @add_cons V1 _ o1 b5599 b5412 b5387 (List.nil : V2) (List.nil : V2) (List.nil : V2) b5798 e6024 e2341 (by rfl)
theorem e6026 : o2.add b5688 b5464=b5797 := @add_cons V1 _ o1 b5598 b5411 b5386 b5689 b5466 b5798 b5797 e6023 e6025 (by rfl)
theorem e6027 : o2.add b5687 b5462=b5796 := @add_cons V1 _ o1 b5597 b5410 b5385 b5688 b5464 b5797 b5796 e6022 e6026 (by rfl)
theorem e6028 : o2.add b5686 b5460=b5795 := @add_cons V1 _ o1 b5596 b5409 b5384 b5687 b5462 b5796 b5795 e6021 e6027 (by rfl)
theorem e6029 : o2.add b5685 b5458=b5794 := @add_cons V1 _ o1 b5595 b5408 b5383 b5686 b5460 b5795 b5794 e6020 e6028 (by rfl)
theorem e6030 : o2.add b5684 b5456=b5793 := @add_cons V1 _ o1 b5594 b5407 b5382 b5685 b5458 b5794 b5793 e6019 e6029 (by rfl)
theorem e6031 : o2.add b5683 b5454=b5792 := @add_cons V1 _ o1 b5593 b5406 b5381 b5684 b5456 b5793 b5792 e6018 e6030 (by rfl)
theorem e6032 : o2.add b5682 b5452=b5791 := @add_cons V1 _ o1 b5592 b5405 b5380 b5683 b5454 b5792 b5791 e6017 e6031 (by rfl)
theorem e6033 : o2.add b5681 b5450=b5790 := @add_cons V1 _ o1 b5591 b5404 b5379 b5682 b5452 b5791 b5790 e6016 e6032 (by rfl)
theorem e6034 : o2.add b5680 b5448=b5789 := @add_cons V1 _ o1 b5590 b5403 b5378 b5681 b5450 b5790 b5789 e6015 e6033 (by rfl)
theorem e6035 : o2.add b5679 b5446=b5788 := @add_cons V1 _ o1 b5377 (List.nil : V1) b5377 b5680 b5448 b5789 b5788 e5847 e6034 (by rfl)
theorem e6036 : o2.add b5678 b5444=b5787 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5679 b5446 b5788 b5787 e34 e6035 (by rfl)
theorem e6037 : o2.add b5677 b5442=b5786 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5678 b5444 b5787 b5786 e34 e6036 (by rfl)
theorem e6038 : o2.add b5676 b5440=b5785 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5677 b5442 b5786 b5785 e34 e6037 (by rfl)
theorem e6039 : o2.add b5675 b5438=b5784 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5676 b5440 b5785 b5784 e34 e6038 (by rfl)
theorem e6040 : o2.add b5600 b5413=b5388 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5675 b5438 b5784 b5388 e34 e6039 (by rfl)
theorem e6041 : o1.add b5601 b5414=b5390 := by decide
theorem e6042 : o1.add b5602 b5415=b5391 := by decide
theorem e6043 : o1.add b5603 b5416=b5392 := by decide
theorem e6044 : o1.add b5604 b5417=b5393 := by decide
theorem e6045 : o1.add b5605 b5418=b5394 := by decide
theorem e6046 : o1.add b5606 b5419=b5395 := by decide
theorem e6047 : o1.add b5607 b5420=b5396 := by decide
theorem e6048 : o1.add b5608 b5421=b5397 := by decide
theorem e6049 : o1.add b5609 b5422=b5398 := by decide
theorem e6050 : o1.add b5610 b5423=b5399 := by decide
theorem e6051 : o2.add b5725 b5501=b5814 := @add_cons V1 _ o1 b5610 b5423 b5399 (List.nil : V2) (List.nil : V2) (List.nil : V2) b5814 e6050 e2341 (by rfl)
theorem e6052 : o2.add b5724 b5500=b5813 := @add_cons V1 _ o1 b5609 b5422 b5398 b5725 b5501 b5814 b5813 e6049 e6051 (by rfl)
theorem e6053 : o2.add b5723 b5499=b5812 := @add_cons V1 _ o1 b5608 b5421 b5397 b5724 b5500 b5813 b5812 e6048 e6052 (by rfl)
theorem e6054 : o2.add b5722 b5498=b5811 := @add_cons V1 _ o1 b5607 b5420 b5396 b5723 b5499 b5812 b5811 e6047 e6053 (by rfl)
theorem e6055 : o2.add b5721 b5497=b5810 := @add_cons V1 _ o1 b5606 b5419 b5395 b5722 b5498 b5811 b5810 e6046 e6054 (by rfl)
theorem e6056 : o2.add b5720 b5496=b5809 := @add_cons V1 _ o1 b5605 b5418 b5394 b5721 b5497 b5810 b5809 e6045 e6055 (by rfl)
theorem e6057 : o2.add b5719 b5495=b5808 := @add_cons V1 _ o1 b5604 b5417 b5393 b5720 b5496 b5809 b5808 e6044 e6056 (by rfl)
theorem e6058 : o2.add b5718 b5494=b5807 := @add_cons V1 _ o1 b5603 b5416 b5392 b5719 b5495 b5808 b5807 e6043 e6057 (by rfl)
theorem e6059 : o2.add b5717 b5493=b5806 := @add_cons V1 _ o1 b5602 b5415 b5391 b5718 b5494 b5807 b5806 e6042 e6058 (by rfl)
theorem e6060 : o2.add b5716 b5492=b5805 := @add_cons V1 _ o1 b5601 b5414 b5390 b5717 b5493 b5806 b5805 e6041 e6059 (by rfl)
theorem e6061 : o2.add b5715 b5491=b5804 := @add_cons V1 _ o1 b5389 (List.nil : V1) b5389 b5716 b5492 b5805 b5804 e5921 e6060 (by rfl)
theorem e6062 : o2.add b5714 b5490=b5803 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5715 b5491 b5804 b5803 e34 e6061 (by rfl)
theorem e6063 : o2.add b5713 b5489=b5802 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5714 b5490 b5803 b5802 e34 e6062 (by rfl)
theorem e6064 : o2.add b5712 b5488=b5801 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5713 b5489 b5802 b5801 e34 e6063 (by rfl)
theorem e6065 : o2.add b5711 b5487=b5800 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5712 b5488 b5801 b5800 e34 e6064 (by rfl)
theorem e6066 : o2.add b5611 b5424=b5400 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5711 b5487 b5800 b5400 e34 e6065 (by rfl)
theorem e6067 : o1.add b5612 b5425=b5209 := by decide
theorem e6068 : o1.add b5613 b5426=b5210 := by decide
theorem e6069 : o1.add b5614 b5427=b5211 := by decide
theorem e6070 : o1.add b5615 b5428=b5212 := by decide
theorem e6071 : o1.add b5616 b5429=b5213 := by decide
theorem e6072 : o1.add b5617 b5430=b5214 := by decide
theorem e6073 : o1.add b5618 b5431=b5215 := by decide
theorem e6074 : o1.add b5619 b5432=b5216 := by decide
theorem e6075 : o1.add b5620 b5433=b5217 := by decide
theorem e6076 : o1.add b5621 b5434=b5218 := by decide
theorem e6077 : o2.add b5761 b5536=b5830 := @add_cons V1 _ o1 b5621 b5434 b5218 (List.nil : V2) (List.nil : V2) (List.nil : V2) b5830 e6076 e2341 (by rfl)
theorem e6078 : o2.add b5760 b5535=b5829 := @add_cons V1 _ o1 b5620 b5433 b5217 b5761 b5536 b5830 b5829 e6075 e6077 (by rfl)
theorem e6079 : o2.add b5759 b5534=b5828 := @add_cons V1 _ o1 b5619 b5432 b5216 b5760 b5535 b5829 b5828 e6074 e6078 (by rfl)
theorem e6080 : o2.add b5758 b5533=b5827 := @add_cons V1 _ o1 b5618 b5431 b5215 b5759 b5534 b5828 b5827 e6073 e6079 (by rfl)
theorem e6081 : o2.add b5757 b5532=b5826 := @add_cons V1 _ o1 b5617 b5430 b5214 b5758 b5533 b5827 b5826 e6072 e6080 (by rfl)
theorem e6082 : o2.add b5756 b5531=b5825 := @add_cons V1 _ o1 b5616 b5429 b5213 b5757 b5532 b5826 b5825 e6071 e6081 (by rfl)
theorem e6083 : o2.add b5755 b5530=b5824 := @add_cons V1 _ o1 b5615 b5428 b5212 b5756 b5531 b5825 b5824 e6070 e6082 (by rfl)
theorem e6084 : o2.add b5754 b5529=b5823 := @add_cons V1 _ o1 b5614 b5427 b5211 b5755 b5530 b5824 b5823 e6069 e6083 (by rfl)
theorem e6085 : o2.add b5753 b5528=b5822 := @add_cons V1 _ o1 b5613 b5426 b5210 b5754 b5529 b5823 b5822 e6068 e6084 (by rfl)
theorem e6086 : o2.add b5752 b5527=b5821 := @add_cons V1 _ o1 b5612 b5425 b5209 b5753 b5528 b5822 b5821 e6067 e6085 (by rfl)
theorem e6087 : o2.add b5751 b5526=b5820 := @add_cons V1 _ o1 b5208 (List.nil : V1) b5208 b5752 b5527 b5821 b5820 e5995 e6086 (by rfl)
theorem e6088 : o2.add b5750 b5525=b5819 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5751 b5526 b5820 b5819 e34 e6087 (by rfl)
theorem e6089 : o2.add b5749 b5524=b5818 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5750 b5525 b5819 b5818 e34 e6088 (by rfl)
theorem e6090 : o2.add b5748 b5523=b5817 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5749 b5524 b5818 b5817 e34 e6089 (by rfl)
theorem e6091 : o2.add b5747 b5522=b5816 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5748 b5523 b5817 b5816 e34 e6090 (by rfl)
theorem e6092 : o2.add b5622 b5435=b5219 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b5747 b5522 b5816 b5219 e34 e6091 (by rfl)
theorem e6093 : o3.add (List.nil : V3) b5556=b5556 := by rfl
theorem e6094 : o3.add b5746 b5521=b5815 := @add_cons V2 _ o2 b5622 b5435 b5219 (List.nil : V3) b5556 b5556 b5815 e6092 e6093 (by rfl)
theorem e6095 : o3.add b5710 b5486=b5799 := @add_cons V2 _ o2 b5611 b5424 b5400 b5746 b5521 b5815 b5799 e6066 e6094 (by rfl)
theorem e6096 : o3.add b5674 b5436=b5783 := @add_cons V2 _ o2 b5600 b5413 b5388 b5710 b5486 b5799 b5783 e6040 e6095 (by rfl)
theorem e6097 : o3.add b5623 b5782=b5401 := @add_cons V2 _ o2 b5376 (List.nil : V2) b5376 b5674 b5436 b5783 b5401 e6014 e6096 (by rfl)
theorem e6098 : o3.mul b5364 b70=b5401 := @mul_cons V2 _ o2 b325 b5402 b70 b5436 b5623 b5782 b5401 e5701 e6013 (by rfl) e6097
theorem e6099 : o1.mul b312 b62=b5335 := by decide
theorem e6100 : o1.scale b312 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6101 : o1.scale b312 b63=b5897 := @scale_cons V1 _ o1 b312 b62 b5335 (List.nil : V2) (List.nil : V2) b5897 e6099 e6100 (by rfl)
theorem e6102 : o2.add b5897 (List.nil : V2)=b5897 := by rfl
theorem e6103 : o2.mul b5896 b63=b5897 := @mul_cons V1 _ o1 b312 (List.nil : V2) b63 (List.nil : V2) b5897 (List.nil : V2) b5897 e5393 e6101 (by rfl) e6102
theorem e6104 : o1.mul b311 b62=b5334 := by decide
theorem e6105 : o1.scale b311 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6106 : o1.scale b311 b63=b5898 := @scale_cons V1 _ o1 b311 b62 b5334 (List.nil : V2) (List.nil : V2) b5898 e6104 e6105 (by rfl)
theorem e6107 : o1.add b5334 (List.nil : V1)=b5334 := by rfl
theorem e6108 : o2.add (List.nil : V2) b5897=b5897 := by rfl
theorem e6109 : o2.add b5898 b5899=b5895 := @add_cons V1 _ o1 b5334 (List.nil : V1) b5334 (List.nil : V2) b5897 b5897 b5895 e6107 e6108 (by rfl)
theorem e6110 : o2.mul b5894 b63=b5895 := @mul_cons V1 _ o1 b311 b5896 b63 b5897 b5898 b5899 b5895 e6103 e6106 (by rfl) e6109
theorem e6111 : o1.mul b310 b62=b5333 := by decide
theorem e6112 : o1.scale b310 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6113 : o1.scale b310 b63=b5900 := @scale_cons V1 _ o1 b310 b62 b5333 (List.nil : V2) (List.nil : V2) b5900 e6111 e6112 (by rfl)
theorem e6114 : o1.add b5333 (List.nil : V1)=b5333 := by rfl
theorem e6115 : o2.add (List.nil : V2) b5895=b5895 := by rfl
theorem e6116 : o2.add b5900 b5901=b5893 := @add_cons V1 _ o1 b5333 (List.nil : V1) b5333 (List.nil : V2) b5895 b5895 b5893 e6114 e6115 (by rfl)
theorem e6117 : o2.mul b5892 b63=b5893 := @mul_cons V1 _ o1 b310 b5894 b63 b5895 b5900 b5901 b5893 e6110 e6113 (by rfl) e6116
theorem e6118 : o1.mul b309 b62=b5332 := by decide
theorem e6119 : o1.scale b309 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6120 : o1.scale b309 b63=b5902 := @scale_cons V1 _ o1 b309 b62 b5332 (List.nil : V2) (List.nil : V2) b5902 e6118 e6119 (by rfl)
theorem e6121 : o1.add b5332 (List.nil : V1)=b5332 := by rfl
theorem e6122 : o2.add (List.nil : V2) b5893=b5893 := by rfl
theorem e6123 : o2.add b5902 b5903=b5891 := @add_cons V1 _ o1 b5332 (List.nil : V1) b5332 (List.nil : V2) b5893 b5893 b5891 e6121 e6122 (by rfl)
theorem e6124 : o2.mul b5890 b63=b5891 := @mul_cons V1 _ o1 b309 b5892 b63 b5893 b5902 b5903 b5891 e6117 e6120 (by rfl) e6123
theorem e6125 : o1.mul b308 b62=b5331 := by decide
theorem e6126 : o1.scale b308 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6127 : o1.scale b308 b63=b5904 := @scale_cons V1 _ o1 b308 b62 b5331 (List.nil : V2) (List.nil : V2) b5904 e6125 e6126 (by rfl)
theorem e6128 : o1.add b5331 (List.nil : V1)=b5331 := by rfl
theorem e6129 : o2.add (List.nil : V2) b5891=b5891 := by rfl
theorem e6130 : o2.add b5904 b5905=b5889 := @add_cons V1 _ o1 b5331 (List.nil : V1) b5331 (List.nil : V2) b5891 b5891 b5889 e6128 e6129 (by rfl)
theorem e6131 : o2.mul b5888 b63=b5889 := @mul_cons V1 _ o1 b308 b5890 b63 b5891 b5904 b5905 b5889 e6124 e6127 (by rfl) e6130
theorem e6132 : o1.mul b307 b62=b5330 := by decide
theorem e6133 : o1.scale b307 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6134 : o1.scale b307 b63=b5906 := @scale_cons V1 _ o1 b307 b62 b5330 (List.nil : V2) (List.nil : V2) b5906 e6132 e6133 (by rfl)
theorem e6135 : o1.add b5330 (List.nil : V1)=b5330 := by rfl
theorem e6136 : o2.add (List.nil : V2) b5889=b5889 := by rfl
theorem e6137 : o2.add b5906 b5907=b5887 := @add_cons V1 _ o1 b5330 (List.nil : V1) b5330 (List.nil : V2) b5889 b5889 b5887 e6135 e6136 (by rfl)
theorem e6138 : o2.mul b5886 b63=b5887 := @mul_cons V1 _ o1 b307 b5888 b63 b5889 b5906 b5907 b5887 e6131 e6134 (by rfl) e6137
theorem e6139 : o1.mul b306 b62=b5329 := by decide
theorem e6140 : o1.scale b306 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6141 : o1.scale b306 b63=b5908 := @scale_cons V1 _ o1 b306 b62 b5329 (List.nil : V2) (List.nil : V2) b5908 e6139 e6140 (by rfl)
theorem e6142 : o1.add b5329 (List.nil : V1)=b5329 := by rfl
theorem e6143 : o2.add (List.nil : V2) b5887=b5887 := by rfl
theorem e6144 : o2.add b5908 b5909=b5885 := @add_cons V1 _ o1 b5329 (List.nil : V1) b5329 (List.nil : V2) b5887 b5887 b5885 e6142 e6143 (by rfl)
theorem e6145 : o2.mul b5884 b63=b5885 := @mul_cons V1 _ o1 b306 b5886 b63 b5887 b5908 b5909 b5885 e6138 e6141 (by rfl) e6144
theorem e6146 : o1.mul b305 b62=b5328 := by decide
theorem e6147 : o1.scale b305 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6148 : o1.scale b305 b63=b5910 := @scale_cons V1 _ o1 b305 b62 b5328 (List.nil : V2) (List.nil : V2) b5910 e6146 e6147 (by rfl)
theorem e6149 : o1.add b5328 (List.nil : V1)=b5328 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
