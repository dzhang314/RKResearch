module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart010

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1000 : o1.mul b77 b15=b1101 := by decide
theorem e1001 : o1.scale b77 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1002 : o1.scale b77 b917=b1111 := @scale_cons V1 _ o1 b77 b15 b1101 (List.nil : V2) (List.nil : V2) b1111 e1000 e1001 (by rfl)
theorem e1003 : o1.scale b77 b915=b1110 := @scale_cons V1 _ o1 b77 b14 b1100 b917 b1111 b1110 e999 e1002 (by rfl)
theorem e1004 : o1.scale b77 b913=b1109 := @scale_cons V1 _ o1 b77 b13 b1099 b915 b1110 b1109 e998 e1003 (by rfl)
theorem e1005 : o1.scale b77 b911=b1108 := @scale_cons V1 _ o1 b77 b12 b1098 b913 b1109 b1108 e997 e1004 (by rfl)
theorem e1006 : o1.scale b77 b909=b1107 := @scale_cons V1 _ o1 b77 b11 b1097 b911 b1108 b1107 e996 e1005 (by rfl)
theorem e1007 : o1.scale b77 b907=b1106 := @scale_cons V1 _ o1 b77 b10 b1096 b909 b1107 b1106 e995 e1006 (by rfl)
theorem e1008 : o1.scale b77 b905=b1105 := @scale_cons V1 _ o1 b77 b9 b1095 b907 b1106 b1105 e994 e1007 (by rfl)
theorem e1009 : o1.scale b77 b903=b1104 := @scale_cons V1 _ o1 b77 b8 b1094 b905 b1105 b1104 e993 e1008 (by rfl)
theorem e1010 : o1.scale b77 b901=b1103 := @scale_cons V1 _ o1 b77 b7 b1093 b903 b1104 b1103 e992 e1009 (by rfl)
theorem e1011 : o1.scale b77 b16=b1102 := @scale_cons V1 _ o1 b77 b6 b814 b901 b1103 b1102 e991 e1010 (by rfl)
theorem e1012 : o1.add b814 (List.nil : V1)=b814 := by rfl
theorem e1013 : o1.add b1093 b825=b815 := by decide
theorem e1014 : o1.add b1094 b826=b816 := by decide
theorem e1015 : o1.add b1095 b827=b817 := by decide
theorem e1016 : o1.add b1096 b828=b818 := by decide
theorem e1017 : o1.add b1097 b829=b819 := by decide
theorem e1018 : o1.add b1098 b830=b820 := by decide
theorem e1019 : o1.add b1099 b831=b821 := by decide
theorem e1020 : o1.add b1100 b832=b822 := by decide
theorem e1021 : o1.add b1101 b833=b748 := by decide
theorem e1022 : o2.add (List.nil : V2) b1092=b1092 := by rfl
theorem e1023 : o2.add b1111 b1091=b1121 := @add_cons V1 _ o1 b1101 b833 b748 (List.nil : V2) b1092 b1092 b1121 e1021 e1022 (by rfl)
theorem e1024 : o2.add b1110 b1090=b1120 := @add_cons V1 _ o1 b1100 b832 b822 b1111 b1091 b1121 b1120 e1020 e1023 (by rfl)
theorem e1025 : o2.add b1109 b1089=b1119 := @add_cons V1 _ o1 b1099 b831 b821 b1110 b1090 b1120 b1119 e1019 e1024 (by rfl)
theorem e1026 : o2.add b1108 b1088=b1118 := @add_cons V1 _ o1 b1098 b830 b820 b1109 b1089 b1119 b1118 e1018 e1025 (by rfl)
theorem e1027 : o2.add b1107 b1087=b1117 := @add_cons V1 _ o1 b1097 b829 b819 b1108 b1088 b1118 b1117 e1017 e1026 (by rfl)
theorem e1028 : o2.add b1106 b1086=b1116 := @add_cons V1 _ o1 b1096 b828 b818 b1107 b1087 b1117 b1116 e1016 e1027 (by rfl)
theorem e1029 : o2.add b1105 b1085=b1115 := @add_cons V1 _ o1 b1095 b827 b817 b1106 b1086 b1116 b1115 e1015 e1028 (by rfl)
theorem e1030 : o2.add b1104 b1084=b1114 := @add_cons V1 _ o1 b1094 b826 b816 b1105 b1085 b1115 b1114 e1014 e1029 (by rfl)
theorem e1031 : o2.add b1103 b834=b1113 := @add_cons V1 _ o1 b1093 b825 b815 b1104 b1084 b1114 b1113 e1013 e1030 (by rfl)
theorem e1032 : o2.add b1102 b1112=b823 := @add_cons V1 _ o1 b814 (List.nil : V1) b814 b1103 b834 b1113 b823 e1012 e1031 (by rfl)
theorem e1033 : o2.mul b813 b16=b823 := @mul_cons V1 _ o1 b77 b824 b16 b834 b1102 b1112 b823 e990 e1011 (by rfl) e1032
theorem e1034 : o1.mul b76 b6=b803 := by decide
theorem e1035 : o1.mul b76 b7=b1122 := by decide
theorem e1036 : o1.mul b76 b8=b1123 := by decide
theorem e1037 : o1.mul b76 b9=b1124 := by decide
theorem e1038 : o1.mul b76 b10=b1125 := by decide
theorem e1039 : o1.mul b76 b11=b1126 := by decide
theorem e1040 : o1.mul b76 b12=b1127 := by decide
theorem e1041 : o1.mul b76 b13=b1128 := by decide
theorem e1042 : o1.mul b76 b14=b1129 := by decide
theorem e1043 : o1.mul b76 b15=b1130 := by decide
theorem e1044 : o1.scale b76 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1045 : o1.scale b76 b917=b1140 := @scale_cons V1 _ o1 b76 b15 b1130 (List.nil : V2) (List.nil : V2) b1140 e1043 e1044 (by rfl)
theorem e1046 : o1.scale b76 b915=b1139 := @scale_cons V1 _ o1 b76 b14 b1129 b917 b1140 b1139 e1042 e1045 (by rfl)
theorem e1047 : o1.scale b76 b913=b1138 := @scale_cons V1 _ o1 b76 b13 b1128 b915 b1139 b1138 e1041 e1046 (by rfl)
theorem e1048 : o1.scale b76 b911=b1137 := @scale_cons V1 _ o1 b76 b12 b1127 b913 b1138 b1137 e1040 e1047 (by rfl)
theorem e1049 : o1.scale b76 b909=b1136 := @scale_cons V1 _ o1 b76 b11 b1126 b911 b1137 b1136 e1039 e1048 (by rfl)
theorem e1050 : o1.scale b76 b907=b1135 := @scale_cons V1 _ o1 b76 b10 b1125 b909 b1136 b1135 e1038 e1049 (by rfl)
theorem e1051 : o1.scale b76 b905=b1134 := @scale_cons V1 _ o1 b76 b9 b1124 b907 b1135 b1134 e1037 e1050 (by rfl)
theorem e1052 : o1.scale b76 b903=b1133 := @scale_cons V1 _ o1 b76 b8 b1123 b905 b1134 b1133 e1036 e1051 (by rfl)
theorem e1053 : o1.scale b76 b901=b1132 := @scale_cons V1 _ o1 b76 b7 b1122 b903 b1133 b1132 e1035 e1052 (by rfl)
theorem e1054 : o1.scale b76 b16=b1131 := @scale_cons V1 _ o1 b76 b6 b803 b901 b1132 b1131 e1034 e1053 (by rfl)
theorem e1055 : o1.add b803 (List.nil : V1)=b803 := by rfl
theorem e1056 : o1.add b1122 b814=b804 := by decide
theorem e1057 : o1.add b1123 b815=b805 := by decide
theorem e1058 : o1.add b1124 b816=b806 := by decide
theorem e1059 : o1.add b1125 b817=b807 := by decide
theorem e1060 : o1.add b1126 b818=b808 := by decide
theorem e1061 : o1.add b1127 b819=b809 := by decide
theorem e1062 : o1.add b1128 b820=b810 := by decide
theorem e1063 : o1.add b1129 b821=b811 := by decide
theorem e1064 : o1.add b1130 b822=b747 := by decide
theorem e1065 : o2.add (List.nil : V2) b1121=b1121 := by rfl
theorem e1066 : o2.add b1140 b1120=b1150 := @add_cons V1 _ o1 b1130 b822 b747 (List.nil : V2) b1121 b1121 b1150 e1064 e1065 (by rfl)
theorem e1067 : o2.add b1139 b1119=b1149 := @add_cons V1 _ o1 b1129 b821 b811 b1140 b1120 b1150 b1149 e1063 e1066 (by rfl)
theorem e1068 : o2.add b1138 b1118=b1148 := @add_cons V1 _ o1 b1128 b820 b810 b1139 b1119 b1149 b1148 e1062 e1067 (by rfl)
theorem e1069 : o2.add b1137 b1117=b1147 := @add_cons V1 _ o1 b1127 b819 b809 b1138 b1118 b1148 b1147 e1061 e1068 (by rfl)
theorem e1070 : o2.add b1136 b1116=b1146 := @add_cons V1 _ o1 b1126 b818 b808 b1137 b1117 b1147 b1146 e1060 e1069 (by rfl)
theorem e1071 : o2.add b1135 b1115=b1145 := @add_cons V1 _ o1 b1125 b817 b807 b1136 b1116 b1146 b1145 e1059 e1070 (by rfl)
theorem e1072 : o2.add b1134 b1114=b1144 := @add_cons V1 _ o1 b1124 b816 b806 b1135 b1115 b1145 b1144 e1058 e1071 (by rfl)
theorem e1073 : o2.add b1133 b1113=b1143 := @add_cons V1 _ o1 b1123 b815 b805 b1134 b1114 b1144 b1143 e1057 e1072 (by rfl)
theorem e1074 : o2.add b1132 b823=b1142 := @add_cons V1 _ o1 b1122 b814 b804 b1133 b1113 b1143 b1142 e1056 e1073 (by rfl)
theorem e1075 : o2.add b1131 b1141=b812 := @add_cons V1 _ o1 b803 (List.nil : V1) b803 b1132 b823 b1142 b812 e1055 e1074 (by rfl)
theorem e1076 : o2.mul b802 b16=b812 := @mul_cons V1 _ o1 b76 b813 b16 b823 b1131 b1141 b812 e1033 e1054 (by rfl) e1075
theorem e1077 : o1.mul b75 b6=b792 := by decide
theorem e1078 : o1.mul b75 b7=b1151 := by decide
theorem e1079 : o1.mul b75 b8=b1152 := by decide
theorem e1080 : o1.mul b75 b9=b1153 := by decide
theorem e1081 : o1.mul b75 b10=b1154 := by decide
theorem e1082 : o1.mul b75 b11=b1155 := by decide
theorem e1083 : o1.mul b75 b12=b1156 := by decide
theorem e1084 : o1.mul b75 b13=b1157 := by decide
theorem e1085 : o1.mul b75 b14=b1158 := by decide
theorem e1086 : o1.mul b75 b15=b1159 := by decide
theorem e1087 : o1.scale b75 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1088 : o1.scale b75 b917=b1169 := @scale_cons V1 _ o1 b75 b15 b1159 (List.nil : V2) (List.nil : V2) b1169 e1086 e1087 (by rfl)
theorem e1089 : o1.scale b75 b915=b1168 := @scale_cons V1 _ o1 b75 b14 b1158 b917 b1169 b1168 e1085 e1088 (by rfl)
theorem e1090 : o1.scale b75 b913=b1167 := @scale_cons V1 _ o1 b75 b13 b1157 b915 b1168 b1167 e1084 e1089 (by rfl)
theorem e1091 : o1.scale b75 b911=b1166 := @scale_cons V1 _ o1 b75 b12 b1156 b913 b1167 b1166 e1083 e1090 (by rfl)
theorem e1092 : o1.scale b75 b909=b1165 := @scale_cons V1 _ o1 b75 b11 b1155 b911 b1166 b1165 e1082 e1091 (by rfl)
theorem e1093 : o1.scale b75 b907=b1164 := @scale_cons V1 _ o1 b75 b10 b1154 b909 b1165 b1164 e1081 e1092 (by rfl)
theorem e1094 : o1.scale b75 b905=b1163 := @scale_cons V1 _ o1 b75 b9 b1153 b907 b1164 b1163 e1080 e1093 (by rfl)
theorem e1095 : o1.scale b75 b903=b1162 := @scale_cons V1 _ o1 b75 b8 b1152 b905 b1163 b1162 e1079 e1094 (by rfl)
theorem e1096 : o1.scale b75 b901=b1161 := @scale_cons V1 _ o1 b75 b7 b1151 b903 b1162 b1161 e1078 e1095 (by rfl)
theorem e1097 : o1.scale b75 b16=b1160 := @scale_cons V1 _ o1 b75 b6 b792 b901 b1161 b1160 e1077 e1096 (by rfl)
theorem e1098 : o1.add b792 (List.nil : V1)=b792 := by rfl
theorem e1099 : o1.add b1151 b803=b793 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
