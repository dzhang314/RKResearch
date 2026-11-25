module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart004

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e600 : o1.scale b87 b1130=b1131 := @scale_cons V1 _ o1 b87 b43 b1117 b1132 b1133 b1131 e592 e599 (by rfl)
theorem e601 : o1.scale b87 b1128=b1129 := @scale_cons V1 _ o1 b87 b42 b1116 b1130 b1131 b1129 e591 e600 (by rfl)
theorem e602 : o1.scale b87 b1126=b1127 := @scale_cons V1 _ o1 b87 b18 b615 b1128 b1129 b1127 e7 e601 (by rfl)
theorem e603 : o1.scale b87 b1124=b1125 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1126 b1127 b1125 e2 e602 (by rfl)
theorem e604 : o1.scale b87 b1122=b1123 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1124 b1125 b1123 e2 e603 (by rfl)
theorem e605 : o1.scale b87 b1120=b1121 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1122 b1123 b1121 e2 e604 (by rfl)
theorem e606 : o1.scale b87 b47=b1119 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1120 b1121 b1119 e2 e605 (by rfl)
theorem e607 : o2.add b1119 (List.nil : V2)=b1119 := by rfl
theorem e608 : o2.mul b610 b47=b1119 := @mul_cons V1 _ o1 b87 (List.nil : V2) b47 (List.nil : V2) b1119 (List.nil : V2) b1119 e590 e606 (by rfl) e607
theorem e609 : o1.mul b86 b42=b1140 := by decide
theorem e610 : o1.mul b86 b43=b1141 := by decide
theorem e611 : o1.mul b86 b44=b1142 := by decide
theorem e612 : o1.mul b86 b45=b1114 := by decide
theorem e613 : o1.mul b86 b46=b1143 := by decide
theorem e614 : o1.scale b86 b1138=b1154 := @scale_cons V1 _ o1 b86 b46 b1143 (List.nil : V2) (List.nil : V2) b1154 e613 e26 (by rfl)
theorem e615 : o1.scale b86 b1136=b1153 := @scale_cons V1 _ o1 b86 b45 b1114 b1138 b1154 b1153 e612 e614 (by rfl)
theorem e616 : o1.scale b86 b1134=b1152 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1136 b1153 b1152 e19 e615 (by rfl)
theorem e617 : o1.scale b86 b1132=b1151 := @scale_cons V1 _ o1 b86 b44 b1142 b1134 b1152 b1151 e611 e616 (by rfl)
theorem e618 : o1.scale b86 b1130=b1150 := @scale_cons V1 _ o1 b86 b43 b1141 b1132 b1151 b1150 e610 e617 (by rfl)
theorem e619 : o1.scale b86 b1128=b1149 := @scale_cons V1 _ o1 b86 b42 b1140 b1130 b1150 b1149 e609 e618 (by rfl)
theorem e620 : o1.scale b86 b1126=b1148 := @scale_cons V1 _ o1 b86 b18 b632 b1128 b1149 b1148 e24 e619 (by rfl)
theorem e621 : o1.scale b86 b1124=b1147 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1126 b1148 b1147 e19 e620 (by rfl)
theorem e622 : o1.scale b86 b1122=b1146 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1124 b1147 b1146 e19 e621 (by rfl)
theorem e623 : o1.scale b86 b1120=b1145 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1122 b1146 b1145 e19 e622 (by rfl)
theorem e624 : o1.scale b86 b47=b1144 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1120 b1145 b1144 e19 e623 (by rfl)
theorem e625 : o1.add b632 (List.nil : V1)=b632 := by rfl
theorem e626 : o1.add b1140 b615=b1111 := by decide
theorem e627 : o1.add b1141 b1116=b1112 := by decide
theorem e628 : o1.add b1142 b1117=b1108 := by decide
theorem e629 : o1.add (List.nil : V1) b1113=b1113 := by rfl
theorem e630 : o1.add b1114 (List.nil : V1)=b1114 := by rfl
theorem e631 : o1.add b1143 b1118=b574 := by decide
theorem e632 : o2.add (List.nil : V2) b1139=b1139 := by rfl
theorem e633 : o2.add b1154 b1137=b1165 := @add_cons V1 _ o1 b1143 b1118 b574 (List.nil : V2) b1139 b1139 b1165 e631 e632 (by rfl)
theorem e634 : o2.add b1153 b1135=b1164 := @add_cons V1 _ o1 b1114 (List.nil : V1) b1114 b1154 b1137 b1165 b1164 e630 e633 (by rfl)
theorem e635 : o2.add b1152 b1133=b1163 := @add_cons V1 _ o1 (List.nil : V1) b1113 b1113 b1153 b1135 b1164 b1163 e629 e634 (by rfl)
theorem e636 : o2.add b1151 b1131=b1162 := @add_cons V1 _ o1 b1142 b1117 b1108 b1152 b1133 b1163 b1162 e628 e635 (by rfl)
theorem e637 : o2.add b1150 b1129=b1161 := @add_cons V1 _ o1 b1141 b1116 b1112 b1151 b1131 b1162 b1161 e627 e636 (by rfl)
theorem e638 : o2.add b1149 b1127=b1160 := @add_cons V1 _ o1 b1140 b615 b1111 b1150 b1129 b1161 b1160 e626 e637 (by rfl)
theorem e639 : o2.add b1148 b1125=b1159 := @add_cons V1 _ o1 b632 (List.nil : V1) b632 b1149 b1127 b1160 b1159 e625 e638 (by rfl)
theorem e640 : o2.add b1147 b1123=b1158 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1148 b1125 b1159 b1158 e34 e639 (by rfl)
theorem e641 : o2.add b1146 b1121=b1157 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1147 b1123 b1158 b1157 e34 e640 (by rfl)
theorem e642 : o2.add b1145 b1119=b1156 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1146 b1121 b1157 b1156 e34 e641 (by rfl)
theorem e643 : o2.add b1144 b1155=b1115 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1145 b1119 b1156 b1115 e34 e642 (by rfl)
theorem e644 : o2.mul b603 b47=b1115 := @mul_cons V1 _ o1 b86 b610 b47 b1119 b1144 b1155 b1115 e608 e624 (by rfl) e643
theorem e645 : o1.mul b85 b42=b1166 := by decide
theorem e646 : o1.mul b85 b43=b1167 := by decide
theorem e647 : o1.mul b85 b44=b1168 := by decide
theorem e648 : o1.mul b85 b45=b1169 := by decide
theorem e649 : o1.mul b85 b46=b1170 := by decide
theorem e650 : o1.scale b85 b1138=b1181 := @scale_cons V1 _ o1 b85 b46 b1170 (List.nil : V2) (List.nil : V2) b1181 e649 e57 (by rfl)
theorem e651 : o1.scale b85 b1136=b1180 := @scale_cons V1 _ o1 b85 b45 b1169 b1138 b1181 b1180 e648 e650 (by rfl)
theorem e652 : o1.scale b85 b1134=b1179 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1136 b1180 b1179 e50 e651 (by rfl)
theorem e653 : o1.scale b85 b1132=b1178 := @scale_cons V1 _ o1 b85 b44 b1168 b1134 b1179 b1178 e647 e652 (by rfl)
theorem e654 : o1.scale b85 b1130=b1177 := @scale_cons V1 _ o1 b85 b43 b1167 b1132 b1178 b1177 e646 e653 (by rfl)
theorem e655 : o1.scale b85 b1128=b1176 := @scale_cons V1 _ o1 b85 b42 b1166 b1130 b1177 b1176 e645 e654 (by rfl)
theorem e656 : o1.scale b85 b1126=b1175 := @scale_cons V1 _ o1 b85 b18 b651 b1128 b1176 b1175 e55 e655 (by rfl)
theorem e657 : o1.scale b85 b1124=b1174 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1126 b1175 b1174 e50 e656 (by rfl)
theorem e658 : o1.scale b85 b1122=b1173 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1124 b1174 b1173 e50 e657 (by rfl)
theorem e659 : o1.scale b85 b1120=b1172 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1122 b1173 b1172 e50 e658 (by rfl)
theorem e660 : o1.scale b85 b47=b1171 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1120 b1172 b1171 e50 e659 (by rfl)
theorem e661 : o1.add b651 (List.nil : V1)=b651 := by rfl
theorem e662 : o1.add b1166 b632=b1106 := by decide
theorem e663 : o1.add b1167 b1111=b1107 := by decide
theorem e664 : o1.add b1168 b1112=b1103 := by decide
theorem e665 : o1.add (List.nil : V1) b1108=b1108 := by rfl
theorem e666 : o1.add b1169 b1113=b1109 := by decide
theorem e667 : o1.add b1170 b1114=b573 := by decide
theorem e668 : o2.add (List.nil : V2) b1165=b1165 := by rfl
theorem e669 : o2.add b1181 b1164=b1192 := @add_cons V1 _ o1 b1170 b1114 b573 (List.nil : V2) b1165 b1165 b1192 e667 e668 (by rfl)
theorem e670 : o2.add b1180 b1163=b1191 := @add_cons V1 _ o1 b1169 b1113 b1109 b1181 b1164 b1192 b1191 e666 e669 (by rfl)
theorem e671 : o2.add b1179 b1162=b1190 := @add_cons V1 _ o1 (List.nil : V1) b1108 b1108 b1180 b1163 b1191 b1190 e665 e670 (by rfl)
theorem e672 : o2.add b1178 b1161=b1189 := @add_cons V1 _ o1 b1168 b1112 b1103 b1179 b1162 b1190 b1189 e664 e671 (by rfl)
theorem e673 : o2.add b1177 b1160=b1188 := @add_cons V1 _ o1 b1167 b1111 b1107 b1178 b1161 b1189 b1188 e663 e672 (by rfl)
theorem e674 : o2.add b1176 b1159=b1187 := @add_cons V1 _ o1 b1166 b632 b1106 b1177 b1160 b1188 b1187 e662 e673 (by rfl)
theorem e675 : o2.add b1175 b1158=b1186 := @add_cons V1 _ o1 b651 (List.nil : V1) b651 b1176 b1159 b1187 b1186 e661 e674 (by rfl)
theorem e676 : o2.add b1174 b1157=b1185 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1175 b1158 b1186 b1185 e34 e675 (by rfl)
theorem e677 : o2.add b1173 b1156=b1184 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1174 b1157 b1185 b1184 e34 e676 (by rfl)
theorem e678 : o2.add b1172 b1115=b1183 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1173 b1156 b1184 b1183 e34 e677 (by rfl)
theorem e679 : o2.add b1171 b1182=b1110 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1172 b1115 b1183 b1110 e34 e678 (by rfl)
theorem e680 : o2.mul b596 b47=b1110 := @mul_cons V1 _ o1 b85 b603 b47 b1115 b1171 b1182 b1110 e644 e660 (by rfl) e679
theorem e681 : o1.mul b84 b42=b1193 := by decide
theorem e682 : o1.mul b84 b43=b1194 := by decide
theorem e683 : o1.mul b84 b44=b1195 := by decide
theorem e684 : o1.mul b84 b45=b1196 := by decide
theorem e685 : o1.mul b84 b46=b1197 := by decide
theorem e686 : o1.scale b84 b1138=b1208 := @scale_cons V1 _ o1 b84 b46 b1197 (List.nil : V2) (List.nil : V2) b1208 e685 e87 (by rfl)
theorem e687 : o1.scale b84 b1136=b1207 := @scale_cons V1 _ o1 b84 b45 b1196 b1138 b1208 b1207 e684 e686 (by rfl)
theorem e688 : o1.scale b84 b1134=b1206 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1136 b1207 b1206 e80 e687 (by rfl)
theorem e689 : o1.scale b84 b1132=b1205 := @scale_cons V1 _ o1 b84 b44 b1195 b1134 b1206 b1205 e683 e688 (by rfl)
theorem e690 : o1.scale b84 b1130=b1204 := @scale_cons V1 _ o1 b84 b43 b1194 b1132 b1205 b1204 e682 e689 (by rfl)
theorem e691 : o1.scale b84 b1128=b1203 := @scale_cons V1 _ o1 b84 b42 b1193 b1130 b1204 b1203 e681 e690 (by rfl)
theorem e692 : o1.scale b84 b1126=b1202 := @scale_cons V1 _ o1 b84 b18 b670 b1128 b1203 b1202 e85 e691 (by rfl)
theorem e693 : o1.scale b84 b1124=b1201 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1126 b1202 b1201 e80 e692 (by rfl)
theorem e694 : o1.scale b84 b1122=b1200 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1124 b1201 b1200 e80 e693 (by rfl)
theorem e695 : o1.scale b84 b1120=b1199 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1122 b1200 b1199 e80 e694 (by rfl)
theorem e696 : o1.scale b84 b47=b1198 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1120 b1199 b1198 e80 e695 (by rfl)
theorem e697 : o1.add b670 (List.nil : V1)=b670 := by rfl
theorem e698 : o1.add b1193 b651=b1101 := by decide
theorem e699 : o1.add b1194 b1106=b1102 := by decide
theorem e700 : o1.add b1195 b1107=b569 := by decide
theorem e701 : o1.add (List.nil : V1) b1103=b1103 := by rfl
theorem e702 : o1.add b1196 b1108=b1104 := by decide
theorem e703 : o1.add b1197 b1109=b572 := by decide
theorem e704 : o2.add (List.nil : V2) b1192=b1192 := by rfl
theorem e705 : o2.add b1208 b1191=b1219 := @add_cons V1 _ o1 b1197 b1109 b572 (List.nil : V2) b1192 b1192 b1219 e703 e704 (by rfl)
theorem e706 : o2.add b1207 b1190=b1218 := @add_cons V1 _ o1 b1196 b1108 b1104 b1208 b1191 b1219 b1218 e702 e705 (by rfl)
theorem e707 : o2.add b1206 b1189=b1217 := @add_cons V1 _ o1 (List.nil : V1) b1103 b1103 b1207 b1190 b1218 b1217 e701 e706 (by rfl)
theorem e708 : o2.add b1205 b1188=b1216 := @add_cons V1 _ o1 b1195 b1107 b569 b1206 b1189 b1217 b1216 e700 e707 (by rfl)
theorem e709 : o2.add b1204 b1187=b1215 := @add_cons V1 _ o1 b1194 b1106 b1102 b1205 b1188 b1216 b1215 e699 e708 (by rfl)
theorem e710 : o2.add b1203 b1186=b1214 := @add_cons V1 _ o1 b1193 b651 b1101 b1204 b1187 b1215 b1214 e698 e709 (by rfl)
theorem e711 : o2.add b1202 b1185=b1213 := @add_cons V1 _ o1 b670 (List.nil : V1) b670 b1203 b1186 b1214 b1213 e697 e710 (by rfl)
theorem e712 : o2.add b1201 b1184=b1212 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1202 b1185 b1213 b1212 e34 e711 (by rfl)
theorem e713 : o2.add b1200 b1183=b1211 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1201 b1184 b1212 b1211 e34 e712 (by rfl)
theorem e714 : o2.add b1199 b1110=b1210 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1200 b1183 b1211 b1210 e34 e713 (by rfl)
theorem e715 : o2.add b1198 b1209=b1105 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1199 b1110 b1210 b1105 e34 e714 (by rfl)
theorem e716 : o2.mul b589 b47=b1105 := @mul_cons V1 _ o1 b84 b596 b47 b1110 b1198 b1209 b1105 e680 e696 (by rfl) e715
theorem e717 : o1.mul b83 b42=b1220 := by decide
theorem e718 : o1.mul b83 b43=b1221 := by decide
theorem e719 : o1.mul b83 b44=b1222 := by decide
theorem e720 : o1.mul b83 b45=b1223 := by decide
theorem e721 : o1.mul b83 b46=b1224 := by decide
theorem e722 : o1.scale b83 b1138=b1235 := @scale_cons V1 _ o1 b83 b46 b1224 (List.nil : V2) (List.nil : V2) b1235 e721 e117 (by rfl)
theorem e723 : o1.scale b83 b1136=b1234 := @scale_cons V1 _ o1 b83 b45 b1223 b1138 b1235 b1234 e720 e722 (by rfl)
theorem e724 : o1.scale b83 b1134=b1233 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1136 b1234 b1233 e110 e723 (by rfl)
theorem e725 : o1.scale b83 b1132=b1232 := @scale_cons V1 _ o1 b83 b44 b1222 b1134 b1233 b1232 e719 e724 (by rfl)
theorem e726 : o1.scale b83 b1130=b1231 := @scale_cons V1 _ o1 b83 b43 b1221 b1132 b1232 b1231 e718 e725 (by rfl)
theorem e727 : o1.scale b83 b1128=b1230 := @scale_cons V1 _ o1 b83 b42 b1220 b1130 b1231 b1230 e717 e726 (by rfl)
theorem e728 : o1.scale b83 b1126=b1229 := @scale_cons V1 _ o1 b83 b18 b416 b1128 b1230 b1229 e115 e727 (by rfl)
theorem e729 : o1.scale b83 b1124=b1228 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1126 b1229 b1228 e110 e728 (by rfl)
theorem e730 : o1.scale b83 b1122=b1227 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1124 b1228 b1227 e110 e729 (by rfl)
theorem e731 : o1.scale b83 b1120=b1226 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1122 b1227 b1226 e110 e730 (by rfl)
theorem e732 : o1.scale b83 b47=b1225 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1120 b1226 b1225 e110 e731 (by rfl)
theorem e733 : o1.add b416 (List.nil : V1)=b416 := by rfl
theorem e734 : o1.add b1220 b670=b566 := by decide
theorem e735 : o1.add b1221 b1101=b567 := by decide
theorem e736 : o1.add b1222 b1102=b568 := by decide
theorem e737 : o1.add (List.nil : V1) b569=b569 := by rfl
theorem e738 : o1.add b1223 b1103=b570 := by decide
theorem e739 : o1.add b1224 b1104=b571 := by decide
theorem e740 : o2.add (List.nil : V2) b1219=b1219 := by rfl
theorem e741 : o2.add b1235 b1218=b1246 := @add_cons V1 _ o1 b1224 b1104 b571 (List.nil : V2) b1219 b1219 b1246 e739 e740 (by rfl)
theorem e742 : o2.add b1234 b1217=b1245 := @add_cons V1 _ o1 b1223 b1103 b570 b1235 b1218 b1246 b1245 e738 e741 (by rfl)
theorem e743 : o2.add b1233 b1216=b1244 := @add_cons V1 _ o1 (List.nil : V1) b569 b569 b1234 b1217 b1245 b1244 e737 e742 (by rfl)
theorem e744 : o2.add b1232 b1215=b1243 := @add_cons V1 _ o1 b1222 b1102 b568 b1233 b1216 b1244 b1243 e736 e743 (by rfl)
theorem e745 : o2.add b1231 b1214=b1242 := @add_cons V1 _ o1 b1221 b1101 b567 b1232 b1215 b1243 b1242 e735 e744 (by rfl)
theorem e746 : o2.add b1230 b1213=b1241 := @add_cons V1 _ o1 b1220 b670 b566 b1231 b1214 b1242 b1241 e734 e745 (by rfl)
theorem e747 : o2.add b1229 b1212=b1240 := @add_cons V1 _ o1 b416 (List.nil : V1) b416 b1230 b1213 b1241 b1240 e733 e746 (by rfl)
theorem e748 : o2.add b1228 b1211=b1239 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1229 b1212 b1240 b1239 e34 e747 (by rfl)
theorem e749 : o2.add b1227 b1210=b1238 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1228 b1211 b1239 b1238 e34 e748 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
