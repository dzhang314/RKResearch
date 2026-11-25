module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart011

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1100 : o1.add b1152 b804=b794 := by decide
theorem e1101 : o1.add b1153 b805=b795 := by decide
theorem e1102 : o1.add b1154 b806=b796 := by decide
theorem e1103 : o1.add b1155 b807=b797 := by decide
theorem e1104 : o1.add b1156 b808=b798 := by decide
theorem e1105 : o1.add b1157 b809=b799 := by decide
theorem e1106 : o1.add b1158 b810=b800 := by decide
theorem e1107 : o1.add b1159 b811=b746 := by decide
theorem e1108 : o2.add (List.nil : V2) b1150=b1150 := by rfl
theorem e1109 : o2.add b1169 b1149=b1179 := @add_cons V1 _ o1 b1159 b811 b746 (List.nil : V2) b1150 b1150 b1179 e1107 e1108 (by rfl)
theorem e1110 : o2.add b1168 b1148=b1178 := @add_cons V1 _ o1 b1158 b810 b800 b1169 b1149 b1179 b1178 e1106 e1109 (by rfl)
theorem e1111 : o2.add b1167 b1147=b1177 := @add_cons V1 _ o1 b1157 b809 b799 b1168 b1148 b1178 b1177 e1105 e1110 (by rfl)
theorem e1112 : o2.add b1166 b1146=b1176 := @add_cons V1 _ o1 b1156 b808 b798 b1167 b1147 b1177 b1176 e1104 e1111 (by rfl)
theorem e1113 : o2.add b1165 b1145=b1175 := @add_cons V1 _ o1 b1155 b807 b797 b1166 b1146 b1176 b1175 e1103 e1112 (by rfl)
theorem e1114 : o2.add b1164 b1144=b1174 := @add_cons V1 _ o1 b1154 b806 b796 b1165 b1145 b1175 b1174 e1102 e1113 (by rfl)
theorem e1115 : o2.add b1163 b1143=b1173 := @add_cons V1 _ o1 b1153 b805 b795 b1164 b1144 b1174 b1173 e1101 e1114 (by rfl)
theorem e1116 : o2.add b1162 b1142=b1172 := @add_cons V1 _ o1 b1152 b804 b794 b1163 b1143 b1173 b1172 e1100 e1115 (by rfl)
theorem e1117 : o2.add b1161 b812=b1171 := @add_cons V1 _ o1 b1151 b803 b793 b1162 b1142 b1172 b1171 e1099 e1116 (by rfl)
theorem e1118 : o2.add b1160 b1170=b801 := @add_cons V1 _ o1 b792 (List.nil : V1) b792 b1161 b812 b1171 b801 e1098 e1117 (by rfl)
theorem e1119 : o2.mul b791 b16=b801 := @mul_cons V1 _ o1 b75 b802 b16 b812 b1160 b1170 b801 e1076 e1097 (by rfl) e1118
theorem e1120 : o1.mul b74 b6=b781 := by decide
theorem e1121 : o1.mul b74 b7=b1180 := by decide
theorem e1122 : o1.mul b74 b8=b1181 := by decide
theorem e1123 : o1.mul b74 b9=b1182 := by decide
theorem e1124 : o1.mul b74 b10=b1183 := by decide
theorem e1125 : o1.mul b74 b11=b1184 := by decide
theorem e1126 : o1.mul b74 b12=b1185 := by decide
theorem e1127 : o1.mul b74 b13=b1186 := by decide
theorem e1128 : o1.mul b74 b14=b1187 := by decide
theorem e1129 : o1.mul b74 b15=b1188 := by decide
theorem e1130 : o1.scale b74 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1131 : o1.scale b74 b917=b1198 := @scale_cons V1 _ o1 b74 b15 b1188 (List.nil : V2) (List.nil : V2) b1198 e1129 e1130 (by rfl)
theorem e1132 : o1.scale b74 b915=b1197 := @scale_cons V1 _ o1 b74 b14 b1187 b917 b1198 b1197 e1128 e1131 (by rfl)
theorem e1133 : o1.scale b74 b913=b1196 := @scale_cons V1 _ o1 b74 b13 b1186 b915 b1197 b1196 e1127 e1132 (by rfl)
theorem e1134 : o1.scale b74 b911=b1195 := @scale_cons V1 _ o1 b74 b12 b1185 b913 b1196 b1195 e1126 e1133 (by rfl)
theorem e1135 : o1.scale b74 b909=b1194 := @scale_cons V1 _ o1 b74 b11 b1184 b911 b1195 b1194 e1125 e1134 (by rfl)
theorem e1136 : o1.scale b74 b907=b1193 := @scale_cons V1 _ o1 b74 b10 b1183 b909 b1194 b1193 e1124 e1135 (by rfl)
theorem e1137 : o1.scale b74 b905=b1192 := @scale_cons V1 _ o1 b74 b9 b1182 b907 b1193 b1192 e1123 e1136 (by rfl)
theorem e1138 : o1.scale b74 b903=b1191 := @scale_cons V1 _ o1 b74 b8 b1181 b905 b1192 b1191 e1122 e1137 (by rfl)
theorem e1139 : o1.scale b74 b901=b1190 := @scale_cons V1 _ o1 b74 b7 b1180 b903 b1191 b1190 e1121 e1138 (by rfl)
theorem e1140 : o1.scale b74 b16=b1189 := @scale_cons V1 _ o1 b74 b6 b781 b901 b1190 b1189 e1120 e1139 (by rfl)
theorem e1141 : o1.add b781 (List.nil : V1)=b781 := by rfl
theorem e1142 : o1.add b1180 b792=b782 := by decide
theorem e1143 : o1.add b1181 b793=b783 := by decide
theorem e1144 : o1.add b1182 b794=b784 := by decide
theorem e1145 : o1.add b1183 b795=b785 := by decide
theorem e1146 : o1.add b1184 b796=b786 := by decide
theorem e1147 : o1.add b1185 b797=b787 := by decide
theorem e1148 : o1.add b1186 b798=b788 := by decide
theorem e1149 : o1.add b1187 b799=b789 := by decide
theorem e1150 : o1.add b1188 b800=b745 := by decide
theorem e1151 : o2.add (List.nil : V2) b1179=b1179 := by rfl
theorem e1152 : o2.add b1198 b1178=b1208 := @add_cons V1 _ o1 b1188 b800 b745 (List.nil : V2) b1179 b1179 b1208 e1150 e1151 (by rfl)
theorem e1153 : o2.add b1197 b1177=b1207 := @add_cons V1 _ o1 b1187 b799 b789 b1198 b1178 b1208 b1207 e1149 e1152 (by rfl)
theorem e1154 : o2.add b1196 b1176=b1206 := @add_cons V1 _ o1 b1186 b798 b788 b1197 b1177 b1207 b1206 e1148 e1153 (by rfl)
theorem e1155 : o2.add b1195 b1175=b1205 := @add_cons V1 _ o1 b1185 b797 b787 b1196 b1176 b1206 b1205 e1147 e1154 (by rfl)
theorem e1156 : o2.add b1194 b1174=b1204 := @add_cons V1 _ o1 b1184 b796 b786 b1195 b1175 b1205 b1204 e1146 e1155 (by rfl)
theorem e1157 : o2.add b1193 b1173=b1203 := @add_cons V1 _ o1 b1183 b795 b785 b1194 b1174 b1204 b1203 e1145 e1156 (by rfl)
theorem e1158 : o2.add b1192 b1172=b1202 := @add_cons V1 _ o1 b1182 b794 b784 b1193 b1173 b1203 b1202 e1144 e1157 (by rfl)
theorem e1159 : o2.add b1191 b1171=b1201 := @add_cons V1 _ o1 b1181 b793 b783 b1192 b1172 b1202 b1201 e1143 e1158 (by rfl)
theorem e1160 : o2.add b1190 b801=b1200 := @add_cons V1 _ o1 b1180 b792 b782 b1191 b1171 b1201 b1200 e1142 e1159 (by rfl)
theorem e1161 : o2.add b1189 b1199=b790 := @add_cons V1 _ o1 b781 (List.nil : V1) b781 b1190 b801 b1200 b790 e1141 e1160 (by rfl)
theorem e1162 : o2.mul b780 b16=b790 := @mul_cons V1 _ o1 b74 b791 b16 b801 b1189 b1199 b790 e1119 e1140 (by rfl) e1161
theorem e1163 : o1.mul b73 b6=b770 := by decide
theorem e1164 : o1.mul b73 b7=b1209 := by decide
theorem e1165 : o1.mul b73 b8=b1210 := by decide
theorem e1166 : o1.mul b73 b9=b1211 := by decide
theorem e1167 : o1.mul b73 b10=b1212 := by decide
theorem e1168 : o1.mul b73 b11=b1213 := by decide
theorem e1169 : o1.mul b73 b12=b1214 := by decide
theorem e1170 : o1.mul b73 b13=b1215 := by decide
theorem e1171 : o1.mul b73 b14=b1216 := by decide
theorem e1172 : o1.mul b73 b15=b1217 := by decide
theorem e1173 : o1.scale b73 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1174 : o1.scale b73 b917=b1227 := @scale_cons V1 _ o1 b73 b15 b1217 (List.nil : V2) (List.nil : V2) b1227 e1172 e1173 (by rfl)
theorem e1175 : o1.scale b73 b915=b1226 := @scale_cons V1 _ o1 b73 b14 b1216 b917 b1227 b1226 e1171 e1174 (by rfl)
theorem e1176 : o1.scale b73 b913=b1225 := @scale_cons V1 _ o1 b73 b13 b1215 b915 b1226 b1225 e1170 e1175 (by rfl)
theorem e1177 : o1.scale b73 b911=b1224 := @scale_cons V1 _ o1 b73 b12 b1214 b913 b1225 b1224 e1169 e1176 (by rfl)
theorem e1178 : o1.scale b73 b909=b1223 := @scale_cons V1 _ o1 b73 b11 b1213 b911 b1224 b1223 e1168 e1177 (by rfl)
theorem e1179 : o1.scale b73 b907=b1222 := @scale_cons V1 _ o1 b73 b10 b1212 b909 b1223 b1222 e1167 e1178 (by rfl)
theorem e1180 : o1.scale b73 b905=b1221 := @scale_cons V1 _ o1 b73 b9 b1211 b907 b1222 b1221 e1166 e1179 (by rfl)
theorem e1181 : o1.scale b73 b903=b1220 := @scale_cons V1 _ o1 b73 b8 b1210 b905 b1221 b1220 e1165 e1180 (by rfl)
theorem e1182 : o1.scale b73 b901=b1219 := @scale_cons V1 _ o1 b73 b7 b1209 b903 b1220 b1219 e1164 e1181 (by rfl)
theorem e1183 : o1.scale b73 b16=b1218 := @scale_cons V1 _ o1 b73 b6 b770 b901 b1219 b1218 e1163 e1182 (by rfl)
theorem e1184 : o1.add b770 (List.nil : V1)=b770 := by rfl
theorem e1185 : o1.add b1209 b781=b771 := by decide
theorem e1186 : o1.add b1210 b782=b772 := by decide
theorem e1187 : o1.add b1211 b783=b773 := by decide
theorem e1188 : o1.add b1212 b784=b774 := by decide
theorem e1189 : o1.add b1213 b785=b775 := by decide
theorem e1190 : o1.add b1214 b786=b776 := by decide
theorem e1191 : o1.add b1215 b787=b777 := by decide
theorem e1192 : o1.add b1216 b788=b778 := by decide
theorem e1193 : o1.add b1217 b789=b744 := by decide
theorem e1194 : o2.add (List.nil : V2) b1208=b1208 := by rfl
theorem e1195 : o2.add b1227 b1207=b1237 := @add_cons V1 _ o1 b1217 b789 b744 (List.nil : V2) b1208 b1208 b1237 e1193 e1194 (by rfl)
theorem e1196 : o2.add b1226 b1206=b1236 := @add_cons V1 _ o1 b1216 b788 b778 b1227 b1207 b1237 b1236 e1192 e1195 (by rfl)
theorem e1197 : o2.add b1225 b1205=b1235 := @add_cons V1 _ o1 b1215 b787 b777 b1226 b1206 b1236 b1235 e1191 e1196 (by rfl)
theorem e1198 : o2.add b1224 b1204=b1234 := @add_cons V1 _ o1 b1214 b786 b776 b1225 b1205 b1235 b1234 e1190 e1197 (by rfl)
theorem e1199 : o2.add b1223 b1203=b1233 := @add_cons V1 _ o1 b1213 b785 b775 b1224 b1204 b1234 b1233 e1189 e1198 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticDAG
