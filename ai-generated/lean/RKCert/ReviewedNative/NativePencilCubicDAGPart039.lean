module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart038

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5700 : o3.add b5436 (List.nil : V3)=b5436 := by rfl
theorem e5701 : o3.mul b5402 b70=b5436 := @mul_cons V2 _ o2 b336 (List.nil : V3) b70 (List.nil : V3) b5436 (List.nil : V3) b5436 e5392 e5699 (by rfl) e5700
theorem e5702 : o1.mul b324 b62=b5375 := by decide
theorem e5703 : o1.scale b324 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5704 : o1.scale b324 b63=b5653 := @scale_cons V1 _ o1 b324 b62 b5375 (List.nil : V2) (List.nil : V2) b5653 e5702 e5703 (by rfl)
theorem e5705 : o2.add b5653 (List.nil : V2)=b5653 := by rfl
theorem e5706 : o2.mul b5652 b63=b5653 := @mul_cons V1 _ o1 b324 (List.nil : V2) b63 (List.nil : V2) b5653 (List.nil : V2) b5653 e5393 e5704 (by rfl) e5705
theorem e5707 : o1.mul b323 b62=b5374 := by decide
theorem e5708 : o1.scale b323 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5709 : o1.scale b323 b63=b5654 := @scale_cons V1 _ o1 b323 b62 b5374 (List.nil : V2) (List.nil : V2) b5654 e5707 e5708 (by rfl)
theorem e5710 : o1.add b5374 (List.nil : V1)=b5374 := by rfl
theorem e5711 : o2.add (List.nil : V2) b5653=b5653 := by rfl
theorem e5712 : o2.add b5654 b5655=b5651 := @add_cons V1 _ o1 b5374 (List.nil : V1) b5374 (List.nil : V2) b5653 b5653 b5651 e5710 e5711 (by rfl)
theorem e5713 : o2.mul b5650 b63=b5651 := @mul_cons V1 _ o1 b323 b5652 b63 b5653 b5654 b5655 b5651 e5706 e5709 (by rfl) e5712
theorem e5714 : o1.mul b322 b62=b5373 := by decide
theorem e5715 : o1.scale b322 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5716 : o1.scale b322 b63=b5656 := @scale_cons V1 _ o1 b322 b62 b5373 (List.nil : V2) (List.nil : V2) b5656 e5714 e5715 (by rfl)
theorem e5717 : o1.add b5373 (List.nil : V1)=b5373 := by rfl
theorem e5718 : o2.add (List.nil : V2) b5651=b5651 := by rfl
theorem e5719 : o2.add b5656 b5657=b5649 := @add_cons V1 _ o1 b5373 (List.nil : V1) b5373 (List.nil : V2) b5651 b5651 b5649 e5717 e5718 (by rfl)
theorem e5720 : o2.mul b5648 b63=b5649 := @mul_cons V1 _ o1 b322 b5650 b63 b5651 b5656 b5657 b5649 e5713 e5716 (by rfl) e5719
theorem e5721 : o1.mul b321 b62=b5372 := by decide
theorem e5722 : o1.scale b321 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5723 : o1.scale b321 b63=b5658 := @scale_cons V1 _ o1 b321 b62 b5372 (List.nil : V2) (List.nil : V2) b5658 e5721 e5722 (by rfl)
theorem e5724 : o1.add b5372 (List.nil : V1)=b5372 := by rfl
theorem e5725 : o2.add (List.nil : V2) b5649=b5649 := by rfl
theorem e5726 : o2.add b5658 b5659=b5647 := @add_cons V1 _ o1 b5372 (List.nil : V1) b5372 (List.nil : V2) b5649 b5649 b5647 e5724 e5725 (by rfl)
theorem e5727 : o2.mul b5646 b63=b5647 := @mul_cons V1 _ o1 b321 b5648 b63 b5649 b5658 b5659 b5647 e5720 e5723 (by rfl) e5726
theorem e5728 : o1.mul b320 b62=b5371 := by decide
theorem e5729 : o1.scale b320 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5730 : o1.scale b320 b63=b5660 := @scale_cons V1 _ o1 b320 b62 b5371 (List.nil : V2) (List.nil : V2) b5660 e5728 e5729 (by rfl)
theorem e5731 : o1.add b5371 (List.nil : V1)=b5371 := by rfl
theorem e5732 : o2.add (List.nil : V2) b5647=b5647 := by rfl
theorem e5733 : o2.add b5660 b5661=b5645 := @add_cons V1 _ o1 b5371 (List.nil : V1) b5371 (List.nil : V2) b5647 b5647 b5645 e5731 e5732 (by rfl)
theorem e5734 : o2.mul b5644 b63=b5645 := @mul_cons V1 _ o1 b320 b5646 b63 b5647 b5660 b5661 b5645 e5727 e5730 (by rfl) e5733
theorem e5735 : o1.mul b319 b62=b5370 := by decide
theorem e5736 : o1.scale b319 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5737 : o1.scale b319 b63=b5662 := @scale_cons V1 _ o1 b319 b62 b5370 (List.nil : V2) (List.nil : V2) b5662 e5735 e5736 (by rfl)
theorem e5738 : o1.add b5370 (List.nil : V1)=b5370 := by rfl
theorem e5739 : o2.add (List.nil : V2) b5645=b5645 := by rfl
theorem e5740 : o2.add b5662 b5663=b5643 := @add_cons V1 _ o1 b5370 (List.nil : V1) b5370 (List.nil : V2) b5645 b5645 b5643 e5738 e5739 (by rfl)
theorem e5741 : o2.mul b5642 b63=b5643 := @mul_cons V1 _ o1 b319 b5644 b63 b5645 b5662 b5663 b5643 e5734 e5737 (by rfl) e5740
theorem e5742 : o1.mul b318 b62=b5369 := by decide
theorem e5743 : o1.scale b318 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5744 : o1.scale b318 b63=b5664 := @scale_cons V1 _ o1 b318 b62 b5369 (List.nil : V2) (List.nil : V2) b5664 e5742 e5743 (by rfl)
theorem e5745 : o1.add b5369 (List.nil : V1)=b5369 := by rfl
theorem e5746 : o2.add (List.nil : V2) b5643=b5643 := by rfl
theorem e5747 : o2.add b5664 b5665=b5641 := @add_cons V1 _ o1 b5369 (List.nil : V1) b5369 (List.nil : V2) b5643 b5643 b5641 e5745 e5746 (by rfl)
theorem e5748 : o2.mul b5640 b63=b5641 := @mul_cons V1 _ o1 b318 b5642 b63 b5643 b5664 b5665 b5641 e5741 e5744 (by rfl) e5747
theorem e5749 : o1.mul b317 b62=b5368 := by decide
theorem e5750 : o1.scale b317 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5751 : o1.scale b317 b63=b5666 := @scale_cons V1 _ o1 b317 b62 b5368 (List.nil : V2) (List.nil : V2) b5666 e5749 e5750 (by rfl)
theorem e5752 : o1.add b5368 (List.nil : V1)=b5368 := by rfl
theorem e5753 : o2.add (List.nil : V2) b5641=b5641 := by rfl
theorem e5754 : o2.add b5666 b5667=b5639 := @add_cons V1 _ o1 b5368 (List.nil : V1) b5368 (List.nil : V2) b5641 b5641 b5639 e5752 e5753 (by rfl)
theorem e5755 : o2.mul b5638 b63=b5639 := @mul_cons V1 _ o1 b317 b5640 b63 b5641 b5666 b5667 b5639 e5748 e5751 (by rfl) e5754
theorem e5756 : o1.mul b316 b62=b5367 := by decide
theorem e5757 : o1.scale b316 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5758 : o1.scale b316 b63=b5668 := @scale_cons V1 _ o1 b316 b62 b5367 (List.nil : V2) (List.nil : V2) b5668 e5756 e5757 (by rfl)
theorem e5759 : o1.add b5367 (List.nil : V1)=b5367 := by rfl
theorem e5760 : o2.add (List.nil : V2) b5639=b5639 := by rfl
theorem e5761 : o2.add b5668 b5669=b5637 := @add_cons V1 _ o1 b5367 (List.nil : V1) b5367 (List.nil : V2) b5639 b5639 b5637 e5759 e5760 (by rfl)
theorem e5762 : o2.mul b5636 b63=b5637 := @mul_cons V1 _ o1 b316 b5638 b63 b5639 b5668 b5669 b5637 e5755 e5758 (by rfl) e5761
theorem e5763 : o1.mul b315 b62=b5366 := by decide
theorem e5764 : o1.scale b315 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5765 : o1.scale b315 b63=b5670 := @scale_cons V1 _ o1 b315 b62 b5366 (List.nil : V2) (List.nil : V2) b5670 e5763 e5764 (by rfl)
theorem e5766 : o1.add b5366 (List.nil : V1)=b5366 := by rfl
theorem e5767 : o2.add (List.nil : V2) b5637=b5637 := by rfl
theorem e5768 : o2.add b5670 b5671=b5635 := @add_cons V1 _ o1 b5366 (List.nil : V1) b5366 (List.nil : V2) b5637 b5637 b5635 e5766 e5767 (by rfl)
theorem e5769 : o2.mul b5634 b63=b5635 := @mul_cons V1 _ o1 b315 b5636 b63 b5637 b5670 b5671 b5635 e5762 e5765 (by rfl) e5768
theorem e5770 : o1.mul b314 b62=b5365 := by decide
theorem e5771 : o1.scale b314 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5772 : o1.scale b314 b63=b5672 := @scale_cons V1 _ o1 b314 b62 b5365 (List.nil : V2) (List.nil : V2) b5672 e5770 e5771 (by rfl)
theorem e5773 : o1.add b5365 (List.nil : V1)=b5365 := by rfl
theorem e5774 : o2.add (List.nil : V2) b5635=b5635 := by rfl
theorem e5775 : o2.add b5672 b5673=b5633 := @add_cons V1 _ o1 b5365 (List.nil : V1) b5365 (List.nil : V2) b5635 b5635 b5633 e5773 e5774 (by rfl)
theorem e5776 : o2.mul b5632 b63=b5633 := @mul_cons V1 _ o1 b314 b5634 b63 b5635 b5672 b5673 b5633 e5769 e5772 (by rfl) e5775
theorem e5777 : o2.add (List.nil : V2) b5631=b5631 := by rfl
theorem e5778 : o2.mul b5630 b63=b5631 := @mul_cons V1 _ o1 (List.nil : V1) b5632 b63 b5633 (List.nil : V2) b5631 b5631 e5776 e5463 (by rfl) e5777
theorem e5779 : o2.add (List.nil : V2) b5629=b5629 := by rfl
theorem e5780 : o2.mul b5628 b63=b5629 := @mul_cons V1 _ o1 (List.nil : V1) b5630 b63 b5631 (List.nil : V2) b5629 b5629 e5778 e5463 (by rfl) e5779
theorem e5781 : o2.add (List.nil : V2) b5627=b5627 := by rfl
theorem e5782 : o2.mul b5626 b63=b5627 := @mul_cons V1 _ o1 (List.nil : V1) b5628 b63 b5629 (List.nil : V2) b5627 b5627 e5780 e5463 (by rfl) e5781
theorem e5783 : o2.add (List.nil : V2) b5625=b5625 := by rfl
theorem e5784 : o2.mul b5624 b63=b5625 := @mul_cons V1 _ o1 (List.nil : V1) b5626 b63 b5627 (List.nil : V2) b5625 b5625 e5782 e5463 (by rfl) e5783
theorem e5785 : o2.add (List.nil : V2) b5376=b5376 := by rfl
theorem e5786 : o2.mul b325 b63=b5376 := @mul_cons V1 _ o1 (List.nil : V1) b5624 b63 b5625 (List.nil : V2) b5376 b5376 e5784 e5463 (by rfl) e5785
theorem e5787 : o1.mul b324 b64=b5599 := by decide
theorem e5788 : o1.scale b324 b65=b5689 := @scale_cons V1 _ o1 b324 b64 b5599 (List.nil : V2) (List.nil : V2) b5689 e5787 e5703 (by rfl)
theorem e5789 : o2.add b5689 (List.nil : V2)=b5689 := by rfl
theorem e5790 : o2.mul b5652 b65=b5689 := @mul_cons V1 _ o1 b324 (List.nil : V2) b65 (List.nil : V2) b5689 (List.nil : V2) b5689 e5476 e5788 (by rfl) e5789
theorem e5791 : o1.mul b323 b64=b5598 := by decide
theorem e5792 : o1.scale b323 b65=b5690 := @scale_cons V1 _ o1 b323 b64 b5598 (List.nil : V2) (List.nil : V2) b5690 e5791 e5708 (by rfl)
theorem e5793 : o1.add b5598 (List.nil : V1)=b5598 := by rfl
theorem e5794 : o2.add (List.nil : V2) b5689=b5689 := by rfl
theorem e5795 : o2.add b5690 b5691=b5688 := @add_cons V1 _ o1 b5598 (List.nil : V1) b5598 (List.nil : V2) b5689 b5689 b5688 e5793 e5794 (by rfl)
theorem e5796 : o2.mul b5650 b65=b5688 := @mul_cons V1 _ o1 b323 b5652 b65 b5689 b5690 b5691 b5688 e5790 e5792 (by rfl) e5795
theorem e5797 : o1.mul b322 b64=b5597 := by decide
theorem e5798 : o1.scale b322 b65=b5692 := @scale_cons V1 _ o1 b322 b64 b5597 (List.nil : V2) (List.nil : V2) b5692 e5797 e5715 (by rfl)
theorem e5799 : o1.add b5597 (List.nil : V1)=b5597 := by rfl
theorem e5800 : o2.add (List.nil : V2) b5688=b5688 := by rfl
theorem e5801 : o2.add b5692 b5693=b5687 := @add_cons V1 _ o1 b5597 (List.nil : V1) b5597 (List.nil : V2) b5688 b5688 b5687 e5799 e5800 (by rfl)
theorem e5802 : o2.mul b5648 b65=b5687 := @mul_cons V1 _ o1 b322 b5650 b65 b5688 b5692 b5693 b5687 e5796 e5798 (by rfl) e5801
theorem e5803 : o1.mul b321 b64=b5596 := by decide
theorem e5804 : o1.scale b321 b65=b5694 := @scale_cons V1 _ o1 b321 b64 b5596 (List.nil : V2) (List.nil : V2) b5694 e5803 e5722 (by rfl)
theorem e5805 : o1.add b5596 (List.nil : V1)=b5596 := by rfl
theorem e5806 : o2.add (List.nil : V2) b5687=b5687 := by rfl
theorem e5807 : o2.add b5694 b5695=b5686 := @add_cons V1 _ o1 b5596 (List.nil : V1) b5596 (List.nil : V2) b5687 b5687 b5686 e5805 e5806 (by rfl)
theorem e5808 : o2.mul b5646 b65=b5686 := @mul_cons V1 _ o1 b321 b5648 b65 b5687 b5694 b5695 b5686 e5802 e5804 (by rfl) e5807
theorem e5809 : o1.mul b320 b64=b5595 := by decide
theorem e5810 : o1.scale b320 b65=b5696 := @scale_cons V1 _ o1 b320 b64 b5595 (List.nil : V2) (List.nil : V2) b5696 e5809 e5729 (by rfl)
theorem e5811 : o1.add b5595 (List.nil : V1)=b5595 := by rfl
theorem e5812 : o2.add (List.nil : V2) b5686=b5686 := by rfl
theorem e5813 : o2.add b5696 b5697=b5685 := @add_cons V1 _ o1 b5595 (List.nil : V1) b5595 (List.nil : V2) b5686 b5686 b5685 e5811 e5812 (by rfl)
theorem e5814 : o2.mul b5644 b65=b5685 := @mul_cons V1 _ o1 b320 b5646 b65 b5686 b5696 b5697 b5685 e5808 e5810 (by rfl) e5813
theorem e5815 : o1.mul b319 b64=b5594 := by decide
theorem e5816 : o1.scale b319 b65=b5698 := @scale_cons V1 _ o1 b319 b64 b5594 (List.nil : V2) (List.nil : V2) b5698 e5815 e5736 (by rfl)
theorem e5817 : o1.add b5594 (List.nil : V1)=b5594 := by rfl
theorem e5818 : o2.add (List.nil : V2) b5685=b5685 := by rfl
theorem e5819 : o2.add b5698 b5699=b5684 := @add_cons V1 _ o1 b5594 (List.nil : V1) b5594 (List.nil : V2) b5685 b5685 b5684 e5817 e5818 (by rfl)
theorem e5820 : o2.mul b5642 b65=b5684 := @mul_cons V1 _ o1 b319 b5644 b65 b5685 b5698 b5699 b5684 e5814 e5816 (by rfl) e5819
theorem e5821 : o1.mul b318 b64=b5593 := by decide
theorem e5822 : o1.scale b318 b65=b5700 := @scale_cons V1 _ o1 b318 b64 b5593 (List.nil : V2) (List.nil : V2) b5700 e5821 e5743 (by rfl)
theorem e5823 : o1.add b5593 (List.nil : V1)=b5593 := by rfl
theorem e5824 : o2.add (List.nil : V2) b5684=b5684 := by rfl
theorem e5825 : o2.add b5700 b5701=b5683 := @add_cons V1 _ o1 b5593 (List.nil : V1) b5593 (List.nil : V2) b5684 b5684 b5683 e5823 e5824 (by rfl)
theorem e5826 : o2.mul b5640 b65=b5683 := @mul_cons V1 _ o1 b318 b5642 b65 b5684 b5700 b5701 b5683 e5820 e5822 (by rfl) e5825
theorem e5827 : o1.mul b317 b64=b5592 := by decide
theorem e5828 : o1.scale b317 b65=b5702 := @scale_cons V1 _ o1 b317 b64 b5592 (List.nil : V2) (List.nil : V2) b5702 e5827 e5750 (by rfl)
theorem e5829 : o1.add b5592 (List.nil : V1)=b5592 := by rfl
theorem e5830 : o2.add (List.nil : V2) b5683=b5683 := by rfl
theorem e5831 : o2.add b5702 b5703=b5682 := @add_cons V1 _ o1 b5592 (List.nil : V1) b5592 (List.nil : V2) b5683 b5683 b5682 e5829 e5830 (by rfl)
theorem e5832 : o2.mul b5638 b65=b5682 := @mul_cons V1 _ o1 b317 b5640 b65 b5683 b5702 b5703 b5682 e5826 e5828 (by rfl) e5831
theorem e5833 : o1.mul b316 b64=b5591 := by decide
theorem e5834 : o1.scale b316 b65=b5704 := @scale_cons V1 _ o1 b316 b64 b5591 (List.nil : V2) (List.nil : V2) b5704 e5833 e5757 (by rfl)
theorem e5835 : o1.add b5591 (List.nil : V1)=b5591 := by rfl
theorem e5836 : o2.add (List.nil : V2) b5682=b5682 := by rfl
theorem e5837 : o2.add b5704 b5705=b5681 := @add_cons V1 _ o1 b5591 (List.nil : V1) b5591 (List.nil : V2) b5682 b5682 b5681 e5835 e5836 (by rfl)
theorem e5838 : o2.mul b5636 b65=b5681 := @mul_cons V1 _ o1 b316 b5638 b65 b5682 b5704 b5705 b5681 e5832 e5834 (by rfl) e5837
theorem e5839 : o1.mul b315 b64=b5590 := by decide
theorem e5840 : o1.scale b315 b65=b5706 := @scale_cons V1 _ o1 b315 b64 b5590 (List.nil : V2) (List.nil : V2) b5706 e5839 e5764 (by rfl)
theorem e5841 : o1.add b5590 (List.nil : V1)=b5590 := by rfl
theorem e5842 : o2.add (List.nil : V2) b5681=b5681 := by rfl
theorem e5843 : o2.add b5706 b5707=b5680 := @add_cons V1 _ o1 b5590 (List.nil : V1) b5590 (List.nil : V2) b5681 b5681 b5680 e5841 e5842 (by rfl)
theorem e5844 : o2.mul b5634 b65=b5680 := @mul_cons V1 _ o1 b315 b5636 b65 b5681 b5706 b5707 b5680 e5838 e5840 (by rfl) e5843
theorem e5845 : o1.mul b314 b64=b5377 := by decide
theorem e5846 : o1.scale b314 b65=b5708 := @scale_cons V1 _ o1 b314 b64 b5377 (List.nil : V2) (List.nil : V2) b5708 e5845 e5771 (by rfl)
theorem e5847 : o1.add b5377 (List.nil : V1)=b5377 := by rfl
theorem e5848 : o2.add (List.nil : V2) b5680=b5680 := by rfl
theorem e5849 : o2.add b5708 b5709=b5679 := @add_cons V1 _ o1 b5377 (List.nil : V1) b5377 (List.nil : V2) b5680 b5680 b5679 e5847 e5848 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
