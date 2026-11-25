module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart001

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e150 : o1.scale b87 b734=b735 := @scale_cons V1 _ o1 b87 b23 b724 b736 b737 b735 e143 e149 (by rfl)
theorem e151 : o1.scale b87 b732=b733 := @scale_cons V1 _ o1 b87 b22 b723 b734 b735 b733 e142 e150 (by rfl)
theorem e152 : o1.scale b87 b730=b731 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b732 b733 b731 e2 e151 (by rfl)
theorem e153 : o1.scale b87 b728=b729 := @scale_cons V1 _ o1 b87 b21 b717 b730 b731 b729 e141 e152 (by rfl)
theorem e154 : o1.scale b87 b27=b727 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b728 b729 b727 e2 e153 (by rfl)
theorem e155 : o2.add b727 (List.nil : V2)=b727 := by rfl
theorem e156 : o2.mul b610 b27=b727 := @mul_cons V1 _ o1 b87 (List.nil : V2) b27 (List.nil : V2) b727 (List.nil : V2) b727 e140 e154 (by rfl) e155
theorem e157 : o1.mul b86 b21=b711 := by decide
theorem e158 : o1.mul b86 b22=b718 := by decide
theorem e159 : o1.mul b86 b23=b742 := by decide
theorem e160 : o1.mul b86 b24=b743 := by decide
theorem e161 : o1.mul b86 b25=b744 := by decide
theorem e162 : o1.mul b86 b26=b745 := by decide
theorem e163 : o1.scale b86 b740=b753 := @scale_cons V1 _ o1 b86 b26 b745 (List.nil : V2) (List.nil : V2) b753 e162 e26 (by rfl)
theorem e164 : o1.scale b86 b738=b752 := @scale_cons V1 _ o1 b86 b25 b744 b740 b753 b752 e161 e163 (by rfl)
theorem e165 : o1.scale b86 b736=b751 := @scale_cons V1 _ o1 b86 b24 b743 b738 b752 b751 e160 e164 (by rfl)
theorem e166 : o1.scale b86 b734=b750 := @scale_cons V1 _ o1 b86 b23 b742 b736 b751 b750 e159 e165 (by rfl)
theorem e167 : o1.scale b86 b732=b749 := @scale_cons V1 _ o1 b86 b22 b718 b734 b750 b749 e158 e166 (by rfl)
theorem e168 : o1.scale b86 b730=b748 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b732 b749 b748 e19 e167 (by rfl)
theorem e169 : o1.scale b86 b728=b747 := @scale_cons V1 _ o1 b86 b21 b711 b730 b748 b747 e157 e168 (by rfl)
theorem e170 : o1.scale b86 b27=b746 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b728 b747 b746 e19 e169 (by rfl)
theorem e171 : o1.add b711 (List.nil : V1)=b711 := by rfl
theorem e172 : o1.add (List.nil : V1) b717=b717 := by rfl
theorem e173 : o1.add b718 (List.nil : V1)=b718 := by rfl
theorem e174 : o1.add b742 b723=b719 := by decide
theorem e175 : o1.add b743 b724=b720 := by decide
theorem e176 : o1.add b744 b725=b721 := by decide
theorem e177 : o1.add b745 b726=b541 := by decide
theorem e178 : o2.add (List.nil : V2) b741=b741 := by rfl
theorem e179 : o2.add b753 b739=b761 := @add_cons V1 _ o1 b745 b726 b541 (List.nil : V2) b741 b741 b761 e177 e178 (by rfl)
theorem e180 : o2.add b752 b737=b760 := @add_cons V1 _ o1 b744 b725 b721 b753 b739 b761 b760 e176 e179 (by rfl)
theorem e181 : o2.add b751 b735=b759 := @add_cons V1 _ o1 b743 b724 b720 b752 b737 b760 b759 e175 e180 (by rfl)
theorem e182 : o2.add b750 b733=b758 := @add_cons V1 _ o1 b742 b723 b719 b751 b735 b759 b758 e174 e181 (by rfl)
theorem e183 : o2.add b749 b731=b757 := @add_cons V1 _ o1 b718 (List.nil : V1) b718 b750 b733 b758 b757 e173 e182 (by rfl)
theorem e184 : o2.add b748 b729=b756 := @add_cons V1 _ o1 (List.nil : V1) b717 b717 b749 b731 b757 b756 e172 e183 (by rfl)
theorem e185 : o2.add b747 b727=b755 := @add_cons V1 _ o1 b711 (List.nil : V1) b711 b748 b729 b756 b755 e171 e184 (by rfl)
theorem e186 : o2.add b746 b754=b722 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b747 b727 b755 b722 e34 e185 (by rfl)
theorem e187 : o2.mul b603 b27=b722 := @mul_cons V1 _ o1 b86 b610 b27 b727 b746 b754 b722 e156 e170 (by rfl) e186
theorem e188 : o1.mul b85 b21=b705 := by decide
theorem e189 : o1.mul b85 b22=b762 := by decide
theorem e190 : o1.mul b85 b23=b763 := by decide
theorem e191 : o1.mul b85 b24=b764 := by decide
theorem e192 : o1.mul b85 b25=b765 := by decide
theorem e193 : o1.mul b85 b26=b766 := by decide
theorem e194 : o1.scale b85 b740=b774 := @scale_cons V1 _ o1 b85 b26 b766 (List.nil : V2) (List.nil : V2) b774 e193 e57 (by rfl)
theorem e195 : o1.scale b85 b738=b773 := @scale_cons V1 _ o1 b85 b25 b765 b740 b774 b773 e192 e194 (by rfl)
theorem e196 : o1.scale b85 b736=b772 := @scale_cons V1 _ o1 b85 b24 b764 b738 b773 b772 e191 e195 (by rfl)
theorem e197 : o1.scale b85 b734=b771 := @scale_cons V1 _ o1 b85 b23 b763 b736 b772 b771 e190 e196 (by rfl)
theorem e198 : o1.scale b85 b732=b770 := @scale_cons V1 _ o1 b85 b22 b762 b734 b771 b770 e189 e197 (by rfl)
theorem e199 : o1.scale b85 b730=b769 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b732 b770 b769 e50 e198 (by rfl)
theorem e200 : o1.scale b85 b728=b768 := @scale_cons V1 _ o1 b85 b21 b705 b730 b769 b768 e188 e199 (by rfl)
theorem e201 : o1.scale b85 b27=b767 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b728 b768 b767 e50 e200 (by rfl)
theorem e202 : o1.add b705 (List.nil : V1)=b705 := by rfl
theorem e203 : o1.add (List.nil : V1) b711=b711 := by rfl
theorem e204 : o1.add b762 b717=b712 := by decide
theorem e205 : o1.add b763 b718=b713 := by decide
theorem e206 : o1.add b764 b719=b714 := by decide
theorem e207 : o1.add b765 b720=b715 := by decide
theorem e208 : o1.add b766 b721=b540 := by decide
theorem e209 : o2.add (List.nil : V2) b761=b761 := by rfl
theorem e210 : o2.add b774 b760=b782 := @add_cons V1 _ o1 b766 b721 b540 (List.nil : V2) b761 b761 b782 e208 e209 (by rfl)
theorem e211 : o2.add b773 b759=b781 := @add_cons V1 _ o1 b765 b720 b715 b774 b760 b782 b781 e207 e210 (by rfl)
theorem e212 : o2.add b772 b758=b780 := @add_cons V1 _ o1 b764 b719 b714 b773 b759 b781 b780 e206 e211 (by rfl)
theorem e213 : o2.add b771 b757=b779 := @add_cons V1 _ o1 b763 b718 b713 b772 b758 b780 b779 e205 e212 (by rfl)
theorem e214 : o2.add b770 b756=b778 := @add_cons V1 _ o1 b762 b717 b712 b771 b757 b779 b778 e204 e213 (by rfl)
theorem e215 : o2.add b769 b755=b777 := @add_cons V1 _ o1 (List.nil : V1) b711 b711 b770 b756 b778 b777 e203 e214 (by rfl)
theorem e216 : o2.add b768 b722=b776 := @add_cons V1 _ o1 b705 (List.nil : V1) b705 b769 b755 b777 b776 e202 e215 (by rfl)
theorem e217 : o2.add b767 b775=b716 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b768 b722 b776 b716 e34 e216 (by rfl)
theorem e218 : o2.mul b596 b27=b716 := @mul_cons V1 _ o1 b85 b603 b27 b722 b767 b775 b716 e187 e201 (by rfl) e217
theorem e219 : o1.mul b84 b21=b533 := by decide
theorem e220 : o1.mul b84 b22=b783 := by decide
theorem e221 : o1.mul b84 b23=b784 := by decide
theorem e222 : o1.mul b84 b24=b785 := by decide
theorem e223 : o1.mul b84 b25=b786 := by decide
theorem e224 : o1.mul b84 b26=b787 := by decide
theorem e225 : o1.scale b84 b740=b795 := @scale_cons V1 _ o1 b84 b26 b787 (List.nil : V2) (List.nil : V2) b795 e224 e87 (by rfl)
theorem e226 : o1.scale b84 b738=b794 := @scale_cons V1 _ o1 b84 b25 b786 b740 b795 b794 e223 e225 (by rfl)
theorem e227 : o1.scale b84 b736=b793 := @scale_cons V1 _ o1 b84 b24 b785 b738 b794 b793 e222 e226 (by rfl)
theorem e228 : o1.scale b84 b734=b792 := @scale_cons V1 _ o1 b84 b23 b784 b736 b793 b792 e221 e227 (by rfl)
theorem e229 : o1.scale b84 b732=b791 := @scale_cons V1 _ o1 b84 b22 b783 b734 b792 b791 e220 e228 (by rfl)
theorem e230 : o1.scale b84 b730=b790 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b732 b791 b790 e80 e229 (by rfl)
theorem e231 : o1.scale b84 b728=b789 := @scale_cons V1 _ o1 b84 b21 b533 b730 b790 b789 e219 e230 (by rfl)
theorem e232 : o1.scale b84 b27=b788 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b728 b789 b788 e80 e231 (by rfl)
theorem e233 : o1.add b533 (List.nil : V1)=b533 := by rfl
theorem e234 : o1.add (List.nil : V1) b705=b705 := by rfl
theorem e235 : o1.add b783 b711=b706 := by decide
theorem e236 : o1.add b784 b712=b707 := by decide
theorem e237 : o1.add b785 b713=b708 := by decide
theorem e238 : o1.add b786 b714=b709 := by decide
theorem e239 : o1.add b787 b715=b539 := by decide
theorem e240 : o2.add (List.nil : V2) b782=b782 := by rfl
theorem e241 : o2.add b795 b781=b803 := @add_cons V1 _ o1 b787 b715 b539 (List.nil : V2) b782 b782 b803 e239 e240 (by rfl)
theorem e242 : o2.add b794 b780=b802 := @add_cons V1 _ o1 b786 b714 b709 b795 b781 b803 b802 e238 e241 (by rfl)
theorem e243 : o2.add b793 b779=b801 := @add_cons V1 _ o1 b785 b713 b708 b794 b780 b802 b801 e237 e242 (by rfl)
theorem e244 : o2.add b792 b778=b800 := @add_cons V1 _ o1 b784 b712 b707 b793 b779 b801 b800 e236 e243 (by rfl)
theorem e245 : o2.add b791 b777=b799 := @add_cons V1 _ o1 b783 b711 b706 b792 b778 b800 b799 e235 e244 (by rfl)
theorem e246 : o2.add b790 b776=b798 := @add_cons V1 _ o1 (List.nil : V1) b705 b705 b791 b777 b799 b798 e234 e245 (by rfl)
theorem e247 : o2.add b789 b716=b797 := @add_cons V1 _ o1 b533 (List.nil : V1) b533 b790 b776 b798 b797 e233 e246 (by rfl)
theorem e248 : o2.add b788 b796=b710 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b789 b716 b797 b710 e34 e247 (by rfl)
theorem e249 : o2.mul b589 b27=b710 := @mul_cons V1 _ o1 b84 b596 b27 b716 b788 b796 b710 e218 e232 (by rfl) e248
theorem e250 : o1.mul b83 b21=b374 := by decide
theorem e251 : o1.mul b83 b22=b804 := by decide
theorem e252 : o1.mul b83 b23=b805 := by decide
theorem e253 : o1.mul b83 b24=b806 := by decide
theorem e254 : o1.mul b83 b25=b807 := by decide
theorem e255 : o1.mul b83 b26=b808 := by decide
theorem e256 : o1.scale b83 b740=b816 := @scale_cons V1 _ o1 b83 b26 b808 (List.nil : V2) (List.nil : V2) b816 e255 e117 (by rfl)
theorem e257 : o1.scale b83 b738=b815 := @scale_cons V1 _ o1 b83 b25 b807 b740 b816 b815 e254 e256 (by rfl)
theorem e258 : o1.scale b83 b736=b814 := @scale_cons V1 _ o1 b83 b24 b806 b738 b815 b814 e253 e257 (by rfl)
theorem e259 : o1.scale b83 b734=b813 := @scale_cons V1 _ o1 b83 b23 b805 b736 b814 b813 e252 e258 (by rfl)
theorem e260 : o1.scale b83 b732=b812 := @scale_cons V1 _ o1 b83 b22 b804 b734 b813 b812 e251 e259 (by rfl)
theorem e261 : o1.scale b83 b730=b811 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b732 b812 b811 e110 e260 (by rfl)
theorem e262 : o1.scale b83 b728=b810 := @scale_cons V1 _ o1 b83 b21 b374 b730 b811 b810 e250 e261 (by rfl)
theorem e263 : o1.scale b83 b27=b809 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b728 b810 b809 e110 e262 (by rfl)
theorem e264 : o1.add b374 (List.nil : V1)=b374 := by rfl
theorem e265 : o1.add (List.nil : V1) b533=b533 := by rfl
theorem e266 : o1.add b804 b705=b534 := by decide
theorem e267 : o1.add b805 b706=b535 := by decide
theorem e268 : o1.add b806 b707=b536 := by decide
theorem e269 : o1.add b807 b708=b537 := by decide
theorem e270 : o1.add b808 b709=b538 := by decide
theorem e271 : o2.add (List.nil : V2) b803=b803 := by rfl
theorem e272 : o2.add b816 b802=b824 := @add_cons V1 _ o1 b808 b709 b538 (List.nil : V2) b803 b803 b824 e270 e271 (by rfl)
theorem e273 : o2.add b815 b801=b823 := @add_cons V1 _ o1 b807 b708 b537 b816 b802 b824 b823 e269 e272 (by rfl)
theorem e274 : o2.add b814 b800=b822 := @add_cons V1 _ o1 b806 b707 b536 b815 b801 b823 b822 e268 e273 (by rfl)
theorem e275 : o2.add b813 b799=b821 := @add_cons V1 _ o1 b805 b706 b535 b814 b800 b822 b821 e267 e274 (by rfl)
theorem e276 : o2.add b812 b798=b820 := @add_cons V1 _ o1 b804 b705 b534 b813 b799 b821 b820 e266 e275 (by rfl)
theorem e277 : o2.add b811 b797=b819 := @add_cons V1 _ o1 (List.nil : V1) b533 b533 b812 b798 b820 b819 e265 e276 (by rfl)
theorem e278 : o2.add b810 b710=b818 := @add_cons V1 _ o1 b374 (List.nil : V1) b374 b811 b797 b819 b818 e264 e277 (by rfl)
theorem e279 : o2.add b809 b817=b543 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b810 b710 b818 b543 e34 e278 (by rfl)
theorem e280 : o2.mul b88 b27=b543 := @mul_cons V1 _ o1 b83 b589 b27 b710 b809 b817 b543 e249 e263 (by rfl) e279
theorem e281 : o2.mul (List.nil : V2) b34=(List.nil : V2) := by rfl
theorem e282 : o1.mul b87 b28=b845 := by decide
theorem e283 : o1.mul b87 b29=b840 := by decide
theorem e284 : o1.mul b87 b30=b846 := by decide
theorem e285 : o1.mul b87 b31=b847 := by decide
theorem e286 : o1.mul b87 b32=b848 := by decide
theorem e287 : o1.mul b87 b33=b553 := by decide
theorem e288 : o1.scale b87 b864=b865 := @scale_cons V1 _ o1 b87 b33 b553 (List.nil : V2) (List.nil : V2) b865 e287 e9 (by rfl)
theorem e289 : o1.scale b87 b862=b863 := @scale_cons V1 _ o1 b87 b32 b848 b864 b865 b863 e286 e288 (by rfl)
theorem e290 : o1.scale b87 b860=b861 := @scale_cons V1 _ o1 b87 b31 b847 b862 b863 b861 e285 e289 (by rfl)
theorem e291 : o1.scale b87 b858=b859 := @scale_cons V1 _ o1 b87 b30 b846 b860 b861 b859 e284 e290 (by rfl)
theorem e292 : o1.scale b87 b856=b857 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b858 b859 b857 e2 e291 (by rfl)
theorem e293 : o1.scale b87 b854=b855 := @scale_cons V1 _ o1 b87 b29 b840 b856 b857 b855 e283 e292 (by rfl)
theorem e294 : o1.scale b87 b852=b853 := @scale_cons V1 _ o1 b87 b28 b845 b854 b855 b853 e282 e293 (by rfl)
theorem e295 : o1.scale b87 b850=b851 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b852 b853 b851 e2 e294 (by rfl)
theorem e296 : o1.scale b87 b34=b849 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b850 b851 b849 e2 e295 (by rfl)
theorem e297 : o2.add b849 (List.nil : V2)=b849 := by rfl
theorem e298 : o2.mul b610 b34=b849 := @mul_cons V1 _ o1 b87 (List.nil : V2) b34 (List.nil : V2) b849 (List.nil : V2) b849 e281 e296 (by rfl) e297
theorem e299 : o1.mul b86 b28=b839 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
