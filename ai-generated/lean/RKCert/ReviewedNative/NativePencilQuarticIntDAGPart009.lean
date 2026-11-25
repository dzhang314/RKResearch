module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart008

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e800 : o2.add (List.nil : V2) b805=b805 := by rfl
theorem e801 : o2.add b826 b804=b837 := @add_cons V1 _ o1 b815 b476 b456 (List.nil : V2) b805 b805 b837 e799 e800 (by rfl)
theorem e802 : o2.add b825 b803=b836 := @add_cons V1 _ o1 b814 b475 b455 b826 b804 b837 b836 e798 e801 (by rfl)
theorem e803 : o2.add b824 b802=b835 := @add_cons V1 _ o1 b813 b474 b454 b825 b803 b836 b835 e797 e802 (by rfl)
theorem e804 : o2.add b823 b801=b834 := @add_cons V1 _ o1 b812 b473 b453 b824 b802 b835 b834 e796 e803 (by rfl)
theorem e805 : o2.add b822 b800=b833 := @add_cons V1 _ o1 b811 b472 b452 b823 b801 b834 b833 e795 e804 (by rfl)
theorem e806 : o2.add b821 b799=b832 := @add_cons V1 _ o1 b810 b471 b451 b822 b800 b833 b832 e794 e805 (by rfl)
theorem e807 : o2.add b820 b798=b831 := @add_cons V1 _ o1 b809 b470 b450 b821 b799 b832 b831 e793 e806 (by rfl)
theorem e808 : o2.add b819 b797=b830 := @add_cons V1 _ o1 b808 b469 b449 b820 b798 b831 b830 e792 e807 (by rfl)
theorem e809 : o2.add b818 b796=b829 := @add_cons V1 _ o1 b807 b468 b448 b819 b797 b830 b829 e791 e808 (by rfl)
theorem e810 : o2.add b817 b477=b828 := @add_cons V1 _ o1 b806 b467 b447 b818 b796 b829 b828 e790 e809 (by rfl)
theorem e811 : o2.add b816 b827=b465 := @add_cons V1 _ o1 b446 (List.nil : V1) b446 b817 b477 b828 b465 e789 e810 (by rfl)
theorem e812 : o2.mul b43 b22=b465 := @mul_cons V1 _ o1 b34 b466 b22 b477 b816 b827 b465 e765 e788 (by rfl) e811
theorem e813 : o1.add b48 b446=b838 := by decide
theorem e814 : o1.add b49 b447=(List.nil : V1) := by decide
theorem e815 : o1.add b50 b448=(List.nil : V1) := by decide
theorem e816 : o1.add b51 b449=(List.nil : V1) := by decide
theorem e817 : o1.add b52 b450=(List.nil : V1) := by decide
theorem e818 : o1.add b53 b451=(List.nil : V1) := by decide
theorem e819 : o1.add b54 b452=(List.nil : V1) := by decide
theorem e820 : o1.add b55 b453=(List.nil : V1) := by decide
theorem e821 : o1.add b56 b454=(List.nil : V1) := by decide
theorem e822 : o1.add b57 b455=(List.nil : V1) := by decide
theorem e823 : o1.add b58 b456=(List.nil : V1) := by decide
theorem e824 : o1.add b59 b457=(List.nil : V1) := by decide
theorem e825 : o1.add b60 b458=(List.nil : V1) := by decide
theorem e826 : o1.add b61 b459=(List.nil : V1) := by decide
theorem e827 : o1.add b62 b460=(List.nil : V1) := by decide
theorem e828 : o1.add b63 b461=(List.nil : V1) := by decide
theorem e829 : o1.add b64 b462=(List.nil : V1) := by decide
theorem e830 : o1.add b65 b463=(List.nil : V1) := by decide
theorem e831 : o1.add b66 b464=(List.nil : V1) := by decide
theorem e832 : o2.add (List.nil : V2) (List.nil : V2)=(List.nil : V2) := by rfl
theorem e833 : o2.add b184 b581=(List.nil : V2) := @add_cons V1 _ o1 b66 b464 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) (List.nil : V2) e831 e832 (by rfl)
theorem e834 : o2.add b213 b613=(List.nil : V2) := @add_cons V1 _ o1 b65 b463 (List.nil : V1) b184 b581 (List.nil : V2) (List.nil : V2) e830 e833 (by rfl)
theorem e835 : o2.add b242 b645=(List.nil : V2) := @add_cons V1 _ o1 b64 b462 (List.nil : V1) b213 b613 (List.nil : V2) (List.nil : V2) e829 e834 (by rfl)
theorem e836 : o2.add b271 b677=(List.nil : V2) := @add_cons V1 _ o1 b63 b461 (List.nil : V1) b242 b645 (List.nil : V2) (List.nil : V2) e828 e835 (by rfl)
theorem e837 : o2.add b300 b709=(List.nil : V2) := @add_cons V1 _ o1 b62 b460 (List.nil : V1) b271 b677 (List.nil : V2) (List.nil : V2) e827 e836 (by rfl)
theorem e838 : o2.add b329 b741=(List.nil : V2) := @add_cons V1 _ o1 b61 b459 (List.nil : V1) b300 b709 (List.nil : V2) (List.nil : V2) e826 e837 (by rfl)
theorem e839 : o2.add b358 b773=(List.nil : V2) := @add_cons V1 _ o1 b60 b458 (List.nil : V1) b329 b741 (List.nil : V2) (List.nil : V2) e825 e838 (by rfl)
theorem e840 : o2.add b387 b805=(List.nil : V2) := @add_cons V1 _ o1 b59 b457 (List.nil : V1) b358 b773 (List.nil : V2) (List.nil : V2) e824 e839 (by rfl)
theorem e841 : o2.add b416 b837=(List.nil : V2) := @add_cons V1 _ o1 b58 b456 (List.nil : V1) b387 b805 (List.nil : V2) (List.nil : V2) e823 e840 (by rfl)
theorem e842 : o2.add b445 b836=(List.nil : V2) := @add_cons V1 _ o1 b57 b455 (List.nil : V1) b416 b837 (List.nil : V2) (List.nil : V2) e822 e841 (by rfl)
theorem e843 : o2.add b444 b835=(List.nil : V2) := @add_cons V1 _ o1 b56 b454 (List.nil : V1) b445 b836 (List.nil : V2) (List.nil : V2) e821 e842 (by rfl)
theorem e844 : o2.add b443 b834=(List.nil : V2) := @add_cons V1 _ o1 b55 b453 (List.nil : V1) b444 b835 (List.nil : V2) (List.nil : V2) e820 e843 (by rfl)
theorem e845 : o2.add b442 b833=(List.nil : V2) := @add_cons V1 _ o1 b54 b452 (List.nil : V1) b443 b834 (List.nil : V2) (List.nil : V2) e819 e844 (by rfl)
theorem e846 : o2.add b441 b832=(List.nil : V2) := @add_cons V1 _ o1 b53 b451 (List.nil : V1) b442 b833 (List.nil : V2) (List.nil : V2) e818 e845 (by rfl)
theorem e847 : o2.add b440 b831=(List.nil : V2) := @add_cons V1 _ o1 b52 b450 (List.nil : V1) b441 b832 (List.nil : V2) (List.nil : V2) e817 e846 (by rfl)
theorem e848 : o2.add b439 b830=(List.nil : V2) := @add_cons V1 _ o1 b51 b449 (List.nil : V1) b440 b831 (List.nil : V2) (List.nil : V2) e816 e847 (by rfl)
theorem e849 : o2.add b438 b829=(List.nil : V2) := @add_cons V1 _ o1 b50 b448 (List.nil : V1) b439 b830 (List.nil : V2) (List.nil : V2) e815 e848 (by rfl)
theorem e850 : o2.add b437 b828=(List.nil : V2) := @add_cons V1 _ o1 b49 b447 (List.nil : V1) b438 b829 (List.nil : V2) (List.nil : V2) e814 e849 (by rfl)
theorem e851 : o2.add b67 b465=b839 := @add_cons V1 _ o1 b48 b446 b838 b437 b828 (List.nil : V2) b839 e813 e850 (by rfl)
theorem e852 : o2.mul (List.nil : V2) b47=(List.nil : V2) := by rfl
theorem e853 : o1.mul b44 b46=b838 := by decide
theorem e854 : o1.scale b44 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e855 : o1.scale b44 b47=b839 := @scale_cons V1 _ o1 b44 b46 b838 (List.nil : V2) (List.nil : V2) b839 e853 e854 (by rfl)
theorem e856 : o2.add b839 (List.nil : V2)=b839 := by rfl
theorem e857 : o2.mul b45 b47=b839 := @mul_cons V1 _ o1 b44 (List.nil : V2) b47 (List.nil : V2) b839 (List.nil : V2) b839 e852 e855 (by rfl) e856

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
