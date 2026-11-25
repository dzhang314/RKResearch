module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart008

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e800 : o1.add b950 b882=b872 := by decide
theorem e801 : o1.add b951 b883=b873 := by decide
theorem e802 : o1.add b952 b884=b874 := by decide
theorem e803 : o1.add b953 b885=b875 := by decide
theorem e804 : o1.add b954 b886=b876 := by decide
theorem e805 : o1.add b955 b887=b877 := by decide
theorem e806 : o1.add b956 b888=b753 := by decide
theorem e807 : o2.add (List.nil : V2) b947=b947 := by rfl
theorem e808 : o2.add b966 b946=b976 := @add_cons V1 _ o1 b956 b888 b753 (List.nil : V2) b947 b947 b976 e806 e807 (by rfl)
theorem e809 : o2.add b965 b945=b975 := @add_cons V1 _ o1 b955 b887 b877 b966 b946 b976 b975 e805 e808 (by rfl)
theorem e810 : o2.add b964 b944=b974 := @add_cons V1 _ o1 b954 b886 b876 b965 b945 b975 b974 e804 e809 (by rfl)
theorem e811 : o2.add b963 b943=b973 := @add_cons V1 _ o1 b953 b885 b875 b964 b944 b974 b973 e803 e810 (by rfl)
theorem e812 : o2.add b962 b942=b972 := @add_cons V1 _ o1 b952 b884 b874 b963 b943 b973 b972 e802 e811 (by rfl)
theorem e813 : o2.add b961 b941=b971 := @add_cons V1 _ o1 b951 b883 b873 b962 b942 b972 b971 e801 e812 (by rfl)
theorem e814 : o2.add b960 b940=b970 := @add_cons V1 _ o1 b950 b882 b872 b961 b941 b971 b970 e800 e813 (by rfl)
theorem e815 : o2.add b959 b939=b969 := @add_cons V1 _ o1 b949 b881 b871 b960 b940 b970 b969 e799 e814 (by rfl)
theorem e816 : o2.add b958 b889=b968 := @add_cons V1 _ o1 b948 b880 b870 b959 b939 b969 b968 e798 e815 (by rfl)
theorem e817 : o2.add b957 b967=b878 := @add_cons V1 _ o1 b869 (List.nil : V1) b869 b958 b889 b968 b878 e797 e816 (by rfl)
theorem e818 : o2.mul b868 b16=b878 := @mul_cons V1 _ o1 b82 b879 b16 b889 b957 b967 b878 e775 e796 (by rfl) e817
theorem e819 : o1.mul b81 b6=b858 := by decide
theorem e820 : o1.mul b81 b7=b977 := by decide
theorem e821 : o1.mul b81 b8=b978 := by decide
theorem e822 : o1.mul b81 b9=b979 := by decide
theorem e823 : o1.mul b81 b10=b980 := by decide
theorem e824 : o1.mul b81 b11=b981 := by decide
theorem e825 : o1.mul b81 b12=b982 := by decide
theorem e826 : o1.mul b81 b13=b983 := by decide
theorem e827 : o1.mul b81 b14=b984 := by decide
theorem e828 : o1.mul b81 b15=b985 := by decide
theorem e829 : o1.scale b81 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e830 : o1.scale b81 b917=b995 := @scale_cons V1 _ o1 b81 b15 b985 (List.nil : V2) (List.nil : V2) b995 e828 e829 (by rfl)
theorem e831 : o1.scale b81 b915=b994 := @scale_cons V1 _ o1 b81 b14 b984 b917 b995 b994 e827 e830 (by rfl)
theorem e832 : o1.scale b81 b913=b993 := @scale_cons V1 _ o1 b81 b13 b983 b915 b994 b993 e826 e831 (by rfl)
theorem e833 : o1.scale b81 b911=b992 := @scale_cons V1 _ o1 b81 b12 b982 b913 b993 b992 e825 e832 (by rfl)
theorem e834 : o1.scale b81 b909=b991 := @scale_cons V1 _ o1 b81 b11 b981 b911 b992 b991 e824 e833 (by rfl)
theorem e835 : o1.scale b81 b907=b990 := @scale_cons V1 _ o1 b81 b10 b980 b909 b991 b990 e823 e834 (by rfl)
theorem e836 : o1.scale b81 b905=b989 := @scale_cons V1 _ o1 b81 b9 b979 b907 b990 b989 e822 e835 (by rfl)
theorem e837 : o1.scale b81 b903=b988 := @scale_cons V1 _ o1 b81 b8 b978 b905 b989 b988 e821 e836 (by rfl)
theorem e838 : o1.scale b81 b901=b987 := @scale_cons V1 _ o1 b81 b7 b977 b903 b988 b987 e820 e837 (by rfl)
theorem e839 : o1.scale b81 b16=b986 := @scale_cons V1 _ o1 b81 b6 b858 b901 b987 b986 e819 e838 (by rfl)
theorem e840 : o1.add b858 (List.nil : V1)=b858 := by rfl
theorem e841 : o1.add b977 b869=b859 := by decide
theorem e842 : o1.add b978 b870=b860 := by decide
theorem e843 : o1.add b979 b871=b861 := by decide
theorem e844 : o1.add b980 b872=b862 := by decide
theorem e845 : o1.add b981 b873=b863 := by decide
theorem e846 : o1.add b982 b874=b864 := by decide
theorem e847 : o1.add b983 b875=b865 := by decide
theorem e848 : o1.add b984 b876=b866 := by decide
theorem e849 : o1.add b985 b877=b752 := by decide
theorem e850 : o2.add (List.nil : V2) b976=b976 := by rfl
theorem e851 : o2.add b995 b975=b1005 := @add_cons V1 _ o1 b985 b877 b752 (List.nil : V2) b976 b976 b1005 e849 e850 (by rfl)
theorem e852 : o2.add b994 b974=b1004 := @add_cons V1 _ o1 b984 b876 b866 b995 b975 b1005 b1004 e848 e851 (by rfl)
theorem e853 : o2.add b993 b973=b1003 := @add_cons V1 _ o1 b983 b875 b865 b994 b974 b1004 b1003 e847 e852 (by rfl)
theorem e854 : o2.add b992 b972=b1002 := @add_cons V1 _ o1 b982 b874 b864 b993 b973 b1003 b1002 e846 e853 (by rfl)
theorem e855 : o2.add b991 b971=b1001 := @add_cons V1 _ o1 b981 b873 b863 b992 b972 b1002 b1001 e845 e854 (by rfl)
theorem e856 : o2.add b990 b970=b1000 := @add_cons V1 _ o1 b980 b872 b862 b991 b971 b1001 b1000 e844 e855 (by rfl)
theorem e857 : o2.add b989 b969=b999 := @add_cons V1 _ o1 b979 b871 b861 b990 b970 b1000 b999 e843 e856 (by rfl)
theorem e858 : o2.add b988 b968=b998 := @add_cons V1 _ o1 b978 b870 b860 b989 b969 b999 b998 e842 e857 (by rfl)
theorem e859 : o2.add b987 b878=b997 := @add_cons V1 _ o1 b977 b869 b859 b988 b968 b998 b997 e841 e858 (by rfl)
theorem e860 : o2.add b986 b996=b867 := @add_cons V1 _ o1 b858 (List.nil : V1) b858 b987 b878 b997 b867 e840 e859 (by rfl)
theorem e861 : o2.mul b857 b16=b867 := @mul_cons V1 _ o1 b81 b868 b16 b878 b986 b996 b867 e818 e839 (by rfl) e860
theorem e862 : o1.mul b80 b6=b847 := by decide
theorem e863 : o1.mul b80 b7=b1006 := by decide
theorem e864 : o1.mul b80 b8=b1007 := by decide
theorem e865 : o1.mul b80 b9=b1008 := by decide
theorem e866 : o1.mul b80 b10=b1009 := by decide
theorem e867 : o1.mul b80 b11=b1010 := by decide
theorem e868 : o1.mul b80 b12=b1011 := by decide
theorem e869 : o1.mul b80 b13=b1012 := by decide
theorem e870 : o1.mul b80 b14=b1013 := by decide
theorem e871 : o1.mul b80 b15=b1014 := by decide
theorem e872 : o1.scale b80 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e873 : o1.scale b80 b917=b1024 := @scale_cons V1 _ o1 b80 b15 b1014 (List.nil : V2) (List.nil : V2) b1024 e871 e872 (by rfl)
theorem e874 : o1.scale b80 b915=b1023 := @scale_cons V1 _ o1 b80 b14 b1013 b917 b1024 b1023 e870 e873 (by rfl)
theorem e875 : o1.scale b80 b913=b1022 := @scale_cons V1 _ o1 b80 b13 b1012 b915 b1023 b1022 e869 e874 (by rfl)
theorem e876 : o1.scale b80 b911=b1021 := @scale_cons V1 _ o1 b80 b12 b1011 b913 b1022 b1021 e868 e875 (by rfl)
theorem e877 : o1.scale b80 b909=b1020 := @scale_cons V1 _ o1 b80 b11 b1010 b911 b1021 b1020 e867 e876 (by rfl)
theorem e878 : o1.scale b80 b907=b1019 := @scale_cons V1 _ o1 b80 b10 b1009 b909 b1020 b1019 e866 e877 (by rfl)
theorem e879 : o1.scale b80 b905=b1018 := @scale_cons V1 _ o1 b80 b9 b1008 b907 b1019 b1018 e865 e878 (by rfl)
theorem e880 : o1.scale b80 b903=b1017 := @scale_cons V1 _ o1 b80 b8 b1007 b905 b1018 b1017 e864 e879 (by rfl)
theorem e881 : o1.scale b80 b901=b1016 := @scale_cons V1 _ o1 b80 b7 b1006 b903 b1017 b1016 e863 e880 (by rfl)
theorem e882 : o1.scale b80 b16=b1015 := @scale_cons V1 _ o1 b80 b6 b847 b901 b1016 b1015 e862 e881 (by rfl)
theorem e883 : o1.add b847 (List.nil : V1)=b847 := by rfl
theorem e884 : o1.add b1006 b858=b848 := by decide
theorem e885 : o1.add b1007 b859=b849 := by decide
theorem e886 : o1.add b1008 b860=b850 := by decide
theorem e887 : o1.add b1009 b861=b851 := by decide
theorem e888 : o1.add b1010 b862=b852 := by decide
theorem e889 : o1.add b1011 b863=b853 := by decide
theorem e890 : o1.add b1012 b864=b854 := by decide
theorem e891 : o1.add b1013 b865=b855 := by decide
theorem e892 : o1.add b1014 b866=b751 := by decide
theorem e893 : o2.add (List.nil : V2) b1005=b1005 := by rfl
theorem e894 : o2.add b1024 b1004=b1034 := @add_cons V1 _ o1 b1014 b866 b751 (List.nil : V2) b1005 b1005 b1034 e892 e893 (by rfl)
theorem e895 : o2.add b1023 b1003=b1033 := @add_cons V1 _ o1 b1013 b865 b855 b1024 b1004 b1034 b1033 e891 e894 (by rfl)
theorem e896 : o2.add b1022 b1002=b1032 := @add_cons V1 _ o1 b1012 b864 b854 b1023 b1003 b1033 b1032 e890 e895 (by rfl)
theorem e897 : o2.add b1021 b1001=b1031 := @add_cons V1 _ o1 b1011 b863 b853 b1022 b1002 b1032 b1031 e889 e896 (by rfl)
theorem e898 : o2.add b1020 b1000=b1030 := @add_cons V1 _ o1 b1010 b862 b852 b1021 b1001 b1031 b1030 e888 e897 (by rfl)
theorem e899 : o2.add b1019 b999=b1029 := @add_cons V1 _ o1 b1009 b861 b851 b1020 b1000 b1030 b1029 e887 e898 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticDAG
