module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart009

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e900 : o2.add b1018 b998=b1028 := @add_cons V1 _ o1 b1008 b860 b850 b1019 b999 b1029 b1028 e886 e899 (by rfl)
theorem e901 : o2.add b1017 b997=b1027 := @add_cons V1 _ o1 b1007 b859 b849 b1018 b998 b1028 b1027 e885 e900 (by rfl)
theorem e902 : o2.add b1016 b867=b1026 := @add_cons V1 _ o1 b1006 b858 b848 b1017 b997 b1027 b1026 e884 e901 (by rfl)
theorem e903 : o2.add b1015 b1025=b856 := @add_cons V1 _ o1 b847 (List.nil : V1) b847 b1016 b867 b1026 b856 e883 e902 (by rfl)
theorem e904 : o2.mul b846 b16=b856 := @mul_cons V1 _ o1 b80 b857 b16 b867 b1015 b1025 b856 e861 e882 (by rfl) e903
theorem e905 : o1.mul b79 b6=b836 := by decide
theorem e906 : o1.mul b79 b7=b1035 := by decide
theorem e907 : o1.mul b79 b8=b1036 := by decide
theorem e908 : o1.mul b79 b9=b1037 := by decide
theorem e909 : o1.mul b79 b10=b1038 := by decide
theorem e910 : o1.mul b79 b11=b1039 := by decide
theorem e911 : o1.mul b79 b12=b1040 := by decide
theorem e912 : o1.mul b79 b13=b1041 := by decide
theorem e913 : o1.mul b79 b14=b1042 := by decide
theorem e914 : o1.mul b79 b15=b1043 := by decide
theorem e915 : o1.scale b79 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e916 : o1.scale b79 b917=b1053 := @scale_cons V1 _ o1 b79 b15 b1043 (List.nil : V2) (List.nil : V2) b1053 e914 e915 (by rfl)
theorem e917 : o1.scale b79 b915=b1052 := @scale_cons V1 _ o1 b79 b14 b1042 b917 b1053 b1052 e913 e916 (by rfl)
theorem e918 : o1.scale b79 b913=b1051 := @scale_cons V1 _ o1 b79 b13 b1041 b915 b1052 b1051 e912 e917 (by rfl)
theorem e919 : o1.scale b79 b911=b1050 := @scale_cons V1 _ o1 b79 b12 b1040 b913 b1051 b1050 e911 e918 (by rfl)
theorem e920 : o1.scale b79 b909=b1049 := @scale_cons V1 _ o1 b79 b11 b1039 b911 b1050 b1049 e910 e919 (by rfl)
theorem e921 : o1.scale b79 b907=b1048 := @scale_cons V1 _ o1 b79 b10 b1038 b909 b1049 b1048 e909 e920 (by rfl)
theorem e922 : o1.scale b79 b905=b1047 := @scale_cons V1 _ o1 b79 b9 b1037 b907 b1048 b1047 e908 e921 (by rfl)
theorem e923 : o1.scale b79 b903=b1046 := @scale_cons V1 _ o1 b79 b8 b1036 b905 b1047 b1046 e907 e922 (by rfl)
theorem e924 : o1.scale b79 b901=b1045 := @scale_cons V1 _ o1 b79 b7 b1035 b903 b1046 b1045 e906 e923 (by rfl)
theorem e925 : o1.scale b79 b16=b1044 := @scale_cons V1 _ o1 b79 b6 b836 b901 b1045 b1044 e905 e924 (by rfl)
theorem e926 : o1.add b836 (List.nil : V1)=b836 := by rfl
theorem e927 : o1.add b1035 b847=b837 := by decide
theorem e928 : o1.add b1036 b848=b838 := by decide
theorem e929 : o1.add b1037 b849=b839 := by decide
theorem e930 : o1.add b1038 b850=b840 := by decide
theorem e931 : o1.add b1039 b851=b841 := by decide
theorem e932 : o1.add b1040 b852=b842 := by decide
theorem e933 : o1.add b1041 b853=b843 := by decide
theorem e934 : o1.add b1042 b854=b844 := by decide
theorem e935 : o1.add b1043 b855=b750 := by decide
theorem e936 : o2.add (List.nil : V2) b1034=b1034 := by rfl
theorem e937 : o2.add b1053 b1033=b1063 := @add_cons V1 _ o1 b1043 b855 b750 (List.nil : V2) b1034 b1034 b1063 e935 e936 (by rfl)
theorem e938 : o2.add b1052 b1032=b1062 := @add_cons V1 _ o1 b1042 b854 b844 b1053 b1033 b1063 b1062 e934 e937 (by rfl)
theorem e939 : o2.add b1051 b1031=b1061 := @add_cons V1 _ o1 b1041 b853 b843 b1052 b1032 b1062 b1061 e933 e938 (by rfl)
theorem e940 : o2.add b1050 b1030=b1060 := @add_cons V1 _ o1 b1040 b852 b842 b1051 b1031 b1061 b1060 e932 e939 (by rfl)
theorem e941 : o2.add b1049 b1029=b1059 := @add_cons V1 _ o1 b1039 b851 b841 b1050 b1030 b1060 b1059 e931 e940 (by rfl)
theorem e942 : o2.add b1048 b1028=b1058 := @add_cons V1 _ o1 b1038 b850 b840 b1049 b1029 b1059 b1058 e930 e941 (by rfl)
theorem e943 : o2.add b1047 b1027=b1057 := @add_cons V1 _ o1 b1037 b849 b839 b1048 b1028 b1058 b1057 e929 e942 (by rfl)
theorem e944 : o2.add b1046 b1026=b1056 := @add_cons V1 _ o1 b1036 b848 b838 b1047 b1027 b1057 b1056 e928 e943 (by rfl)
theorem e945 : o2.add b1045 b856=b1055 := @add_cons V1 _ o1 b1035 b847 b837 b1046 b1026 b1056 b1055 e927 e944 (by rfl)
theorem e946 : o2.add b1044 b1054=b845 := @add_cons V1 _ o1 b836 (List.nil : V1) b836 b1045 b856 b1055 b845 e926 e945 (by rfl)
theorem e947 : o2.mul b835 b16=b845 := @mul_cons V1 _ o1 b79 b846 b16 b856 b1044 b1054 b845 e904 e925 (by rfl) e946
theorem e948 : o1.mul b78 b6=b825 := by decide
theorem e949 : o1.mul b78 b7=b1064 := by decide
theorem e950 : o1.mul b78 b8=b1065 := by decide
theorem e951 : o1.mul b78 b9=b1066 := by decide
theorem e952 : o1.mul b78 b10=b1067 := by decide
theorem e953 : o1.mul b78 b11=b1068 := by decide
theorem e954 : o1.mul b78 b12=b1069 := by decide
theorem e955 : o1.mul b78 b13=b1070 := by decide
theorem e956 : o1.mul b78 b14=b1071 := by decide
theorem e957 : o1.mul b78 b15=b1072 := by decide
theorem e958 : o1.scale b78 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e959 : o1.scale b78 b917=b1082 := @scale_cons V1 _ o1 b78 b15 b1072 (List.nil : V2) (List.nil : V2) b1082 e957 e958 (by rfl)
theorem e960 : o1.scale b78 b915=b1081 := @scale_cons V1 _ o1 b78 b14 b1071 b917 b1082 b1081 e956 e959 (by rfl)
theorem e961 : o1.scale b78 b913=b1080 := @scale_cons V1 _ o1 b78 b13 b1070 b915 b1081 b1080 e955 e960 (by rfl)
theorem e962 : o1.scale b78 b911=b1079 := @scale_cons V1 _ o1 b78 b12 b1069 b913 b1080 b1079 e954 e961 (by rfl)
theorem e963 : o1.scale b78 b909=b1078 := @scale_cons V1 _ o1 b78 b11 b1068 b911 b1079 b1078 e953 e962 (by rfl)
theorem e964 : o1.scale b78 b907=b1077 := @scale_cons V1 _ o1 b78 b10 b1067 b909 b1078 b1077 e952 e963 (by rfl)
theorem e965 : o1.scale b78 b905=b1076 := @scale_cons V1 _ o1 b78 b9 b1066 b907 b1077 b1076 e951 e964 (by rfl)
theorem e966 : o1.scale b78 b903=b1075 := @scale_cons V1 _ o1 b78 b8 b1065 b905 b1076 b1075 e950 e965 (by rfl)
theorem e967 : o1.scale b78 b901=b1074 := @scale_cons V1 _ o1 b78 b7 b1064 b903 b1075 b1074 e949 e966 (by rfl)
theorem e968 : o1.scale b78 b16=b1073 := @scale_cons V1 _ o1 b78 b6 b825 b901 b1074 b1073 e948 e967 (by rfl)
theorem e969 : o1.add b825 (List.nil : V1)=b825 := by rfl
theorem e970 : o1.add b1064 b836=b826 := by decide
theorem e971 : o1.add b1065 b837=b827 := by decide
theorem e972 : o1.add b1066 b838=b828 := by decide
theorem e973 : o1.add b1067 b839=b829 := by decide
theorem e974 : o1.add b1068 b840=b830 := by decide
theorem e975 : o1.add b1069 b841=b831 := by decide
theorem e976 : o1.add b1070 b842=b832 := by decide
theorem e977 : o1.add b1071 b843=b833 := by decide
theorem e978 : o1.add b1072 b844=b749 := by decide
theorem e979 : o2.add (List.nil : V2) b1063=b1063 := by rfl
theorem e980 : o2.add b1082 b1062=b1092 := @add_cons V1 _ o1 b1072 b844 b749 (List.nil : V2) b1063 b1063 b1092 e978 e979 (by rfl)
theorem e981 : o2.add b1081 b1061=b1091 := @add_cons V1 _ o1 b1071 b843 b833 b1082 b1062 b1092 b1091 e977 e980 (by rfl)
theorem e982 : o2.add b1080 b1060=b1090 := @add_cons V1 _ o1 b1070 b842 b832 b1081 b1061 b1091 b1090 e976 e981 (by rfl)
theorem e983 : o2.add b1079 b1059=b1089 := @add_cons V1 _ o1 b1069 b841 b831 b1080 b1060 b1090 b1089 e975 e982 (by rfl)
theorem e984 : o2.add b1078 b1058=b1088 := @add_cons V1 _ o1 b1068 b840 b830 b1079 b1059 b1089 b1088 e974 e983 (by rfl)
theorem e985 : o2.add b1077 b1057=b1087 := @add_cons V1 _ o1 b1067 b839 b829 b1078 b1058 b1088 b1087 e973 e984 (by rfl)
theorem e986 : o2.add b1076 b1056=b1086 := @add_cons V1 _ o1 b1066 b838 b828 b1077 b1057 b1087 b1086 e972 e985 (by rfl)
theorem e987 : o2.add b1075 b1055=b1085 := @add_cons V1 _ o1 b1065 b837 b827 b1076 b1056 b1086 b1085 e971 e986 (by rfl)
theorem e988 : o2.add b1074 b845=b1084 := @add_cons V1 _ o1 b1064 b836 b826 b1075 b1055 b1085 b1084 e970 e987 (by rfl)
theorem e989 : o2.add b1073 b1083=b834 := @add_cons V1 _ o1 b825 (List.nil : V1) b825 b1074 b845 b1084 b834 e969 e988 (by rfl)
theorem e990 : o2.mul b824 b16=b834 := @mul_cons V1 _ o1 b78 b835 b16 b845 b1073 b1083 b834 e947 e968 (by rfl) e989
theorem e991 : o1.mul b77 b6=b814 := by decide
theorem e992 : o1.mul b77 b7=b1093 := by decide
theorem e993 : o1.mul b77 b8=b1094 := by decide
theorem e994 : o1.mul b77 b9=b1095 := by decide
theorem e995 : o1.mul b77 b10=b1096 := by decide
theorem e996 : o1.mul b77 b11=b1097 := by decide
theorem e997 : o1.mul b77 b12=b1098 := by decide
theorem e998 : o1.mul b77 b13=b1099 := by decide
theorem e999 : o1.mul b77 b14=b1100 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
