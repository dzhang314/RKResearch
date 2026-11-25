module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart012

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1200 : o2.add b1222 b1202=b1232 := @add_cons V1 _ o1 b1212 b784 b774 b1223 b1203 b1233 b1232 e1188 e1199 (by rfl)
theorem e1201 : o2.add b1221 b1201=b1231 := @add_cons V1 _ o1 b1211 b783 b773 b1222 b1202 b1232 b1231 e1187 e1200 (by rfl)
theorem e1202 : o2.add b1220 b1200=b1230 := @add_cons V1 _ o1 b1210 b782 b772 b1221 b1201 b1231 b1230 e1186 e1201 (by rfl)
theorem e1203 : o2.add b1219 b790=b1229 := @add_cons V1 _ o1 b1209 b781 b771 b1220 b1200 b1230 b1229 e1185 e1202 (by rfl)
theorem e1204 : o2.add b1218 b1228=b779 := @add_cons V1 _ o1 b770 (List.nil : V1) b770 b1219 b790 b1229 b779 e1184 e1203 (by rfl)
theorem e1205 : o2.mul b769 b16=b779 := @mul_cons V1 _ o1 b73 b780 b16 b790 b1218 b1228 b779 e1162 e1183 (by rfl) e1204
theorem e1206 : o1.mul b72 b6=b759 := by decide
theorem e1207 : o1.mul b72 b7=b1238 := by decide
theorem e1208 : o1.mul b72 b8=b1239 := by decide
theorem e1209 : o1.mul b72 b9=b1240 := by decide
theorem e1210 : o1.mul b72 b10=b1241 := by decide
theorem e1211 : o1.mul b72 b11=b1242 := by decide
theorem e1212 : o1.mul b72 b12=b1243 := by decide
theorem e1213 : o1.mul b72 b13=b1244 := by decide
theorem e1214 : o1.mul b72 b14=b1245 := by decide
theorem e1215 : o1.mul b72 b15=b1246 := by decide
theorem e1216 : o1.scale b72 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1217 : o1.scale b72 b917=b1256 := @scale_cons V1 _ o1 b72 b15 b1246 (List.nil : V2) (List.nil : V2) b1256 e1215 e1216 (by rfl)
theorem e1218 : o1.scale b72 b915=b1255 := @scale_cons V1 _ o1 b72 b14 b1245 b917 b1256 b1255 e1214 e1217 (by rfl)
theorem e1219 : o1.scale b72 b913=b1254 := @scale_cons V1 _ o1 b72 b13 b1244 b915 b1255 b1254 e1213 e1218 (by rfl)
theorem e1220 : o1.scale b72 b911=b1253 := @scale_cons V1 _ o1 b72 b12 b1243 b913 b1254 b1253 e1212 e1219 (by rfl)
theorem e1221 : o1.scale b72 b909=b1252 := @scale_cons V1 _ o1 b72 b11 b1242 b911 b1253 b1252 e1211 e1220 (by rfl)
theorem e1222 : o1.scale b72 b907=b1251 := @scale_cons V1 _ o1 b72 b10 b1241 b909 b1252 b1251 e1210 e1221 (by rfl)
theorem e1223 : o1.scale b72 b905=b1250 := @scale_cons V1 _ o1 b72 b9 b1240 b907 b1251 b1250 e1209 e1222 (by rfl)
theorem e1224 : o1.scale b72 b903=b1249 := @scale_cons V1 _ o1 b72 b8 b1239 b905 b1250 b1249 e1208 e1223 (by rfl)
theorem e1225 : o1.scale b72 b901=b1248 := @scale_cons V1 _ o1 b72 b7 b1238 b903 b1249 b1248 e1207 e1224 (by rfl)
theorem e1226 : o1.scale b72 b16=b1247 := @scale_cons V1 _ o1 b72 b6 b759 b901 b1248 b1247 e1206 e1225 (by rfl)
theorem e1227 : o1.add b759 (List.nil : V1)=b759 := by rfl
theorem e1228 : o1.add b1238 b770=b760 := by decide
theorem e1229 : o1.add b1239 b771=b761 := by decide
theorem e1230 : o1.add b1240 b772=b762 := by decide
theorem e1231 : o1.add b1241 b773=b763 := by decide
theorem e1232 : o1.add b1242 b774=b764 := by decide
theorem e1233 : o1.add b1243 b775=b765 := by decide
theorem e1234 : o1.add b1244 b776=b766 := by decide
theorem e1235 : o1.add b1245 b777=b767 := by decide
theorem e1236 : o1.add b1246 b778=b743 := by decide
theorem e1237 : o2.add (List.nil : V2) b1237=b1237 := by rfl
theorem e1238 : o2.add b1256 b1236=b1266 := @add_cons V1 _ o1 b1246 b778 b743 (List.nil : V2) b1237 b1237 b1266 e1236 e1237 (by rfl)
theorem e1239 : o2.add b1255 b1235=b1265 := @add_cons V1 _ o1 b1245 b777 b767 b1256 b1236 b1266 b1265 e1235 e1238 (by rfl)
theorem e1240 : o2.add b1254 b1234=b1264 := @add_cons V1 _ o1 b1244 b776 b766 b1255 b1235 b1265 b1264 e1234 e1239 (by rfl)
theorem e1241 : o2.add b1253 b1233=b1263 := @add_cons V1 _ o1 b1243 b775 b765 b1254 b1234 b1264 b1263 e1233 e1240 (by rfl)
theorem e1242 : o2.add b1252 b1232=b1262 := @add_cons V1 _ o1 b1242 b774 b764 b1253 b1233 b1263 b1262 e1232 e1241 (by rfl)
theorem e1243 : o2.add b1251 b1231=b1261 := @add_cons V1 _ o1 b1241 b773 b763 b1252 b1232 b1262 b1261 e1231 e1242 (by rfl)
theorem e1244 : o2.add b1250 b1230=b1260 := @add_cons V1 _ o1 b1240 b772 b762 b1251 b1231 b1261 b1260 e1230 e1243 (by rfl)
theorem e1245 : o2.add b1249 b1229=b1259 := @add_cons V1 _ o1 b1239 b771 b761 b1250 b1230 b1260 b1259 e1229 e1244 (by rfl)
theorem e1246 : o2.add b1248 b779=b1258 := @add_cons V1 _ o1 b1238 b770 b760 b1249 b1229 b1259 b1258 e1228 e1245 (by rfl)
theorem e1247 : o2.add b1247 b1257=b768 := @add_cons V1 _ o1 b759 (List.nil : V1) b759 b1248 b779 b1258 b768 e1227 e1246 (by rfl)
theorem e1248 : o2.mul b758 b16=b768 := @mul_cons V1 _ o1 b72 b769 b16 b779 b1247 b1257 b768 e1205 e1226 (by rfl) e1247
theorem e1249 : o1.mul b71 b6=b733 := by decide
theorem e1250 : o1.mul b71 b7=b1267 := by decide
theorem e1251 : o1.mul b71 b8=b1268 := by decide
theorem e1252 : o1.mul b71 b9=b1269 := by decide
theorem e1253 : o1.mul b71 b10=b1270 := by decide
theorem e1254 : o1.mul b71 b11=b1271 := by decide
theorem e1255 : o1.mul b71 b12=b1272 := by decide
theorem e1256 : o1.mul b71 b13=b1273 := by decide
theorem e1257 : o1.mul b71 b14=b1274 := by decide
theorem e1258 : o1.mul b71 b15=b1275 := by decide
theorem e1259 : o1.scale b71 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1260 : o1.scale b71 b917=b1285 := @scale_cons V1 _ o1 b71 b15 b1275 (List.nil : V2) (List.nil : V2) b1285 e1258 e1259 (by rfl)
theorem e1261 : o1.scale b71 b915=b1284 := @scale_cons V1 _ o1 b71 b14 b1274 b917 b1285 b1284 e1257 e1260 (by rfl)
theorem e1262 : o1.scale b71 b913=b1283 := @scale_cons V1 _ o1 b71 b13 b1273 b915 b1284 b1283 e1256 e1261 (by rfl)
theorem e1263 : o1.scale b71 b911=b1282 := @scale_cons V1 _ o1 b71 b12 b1272 b913 b1283 b1282 e1255 e1262 (by rfl)
theorem e1264 : o1.scale b71 b909=b1281 := @scale_cons V1 _ o1 b71 b11 b1271 b911 b1282 b1281 e1254 e1263 (by rfl)
theorem e1265 : o1.scale b71 b907=b1280 := @scale_cons V1 _ o1 b71 b10 b1270 b909 b1281 b1280 e1253 e1264 (by rfl)
theorem e1266 : o1.scale b71 b905=b1279 := @scale_cons V1 _ o1 b71 b9 b1269 b907 b1280 b1279 e1252 e1265 (by rfl)
theorem e1267 : o1.scale b71 b903=b1278 := @scale_cons V1 _ o1 b71 b8 b1268 b905 b1279 b1278 e1251 e1266 (by rfl)
theorem e1268 : o1.scale b71 b901=b1277 := @scale_cons V1 _ o1 b71 b7 b1267 b903 b1278 b1277 e1250 e1267 (by rfl)
theorem e1269 : o1.scale b71 b16=b1276 := @scale_cons V1 _ o1 b71 b6 b733 b901 b1277 b1276 e1249 e1268 (by rfl)
theorem e1270 : o1.add b733 (List.nil : V1)=b733 := by rfl
theorem e1271 : o1.add b1267 b759=b734 := by decide
theorem e1272 : o1.add b1268 b760=b735 := by decide
theorem e1273 : o1.add b1269 b761=b736 := by decide
theorem e1274 : o1.add b1270 b762=b737 := by decide
theorem e1275 : o1.add b1271 b763=b738 := by decide
theorem e1276 : o1.add b1272 b764=b739 := by decide
theorem e1277 : o1.add b1273 b765=b740 := by decide
theorem e1278 : o1.add b1274 b766=b741 := by decide
theorem e1279 : o1.add b1275 b767=b742 := by decide
theorem e1280 : o2.add (List.nil : V2) b1266=b1266 := by rfl
theorem e1281 : o2.add b1285 b1265=b1295 := @add_cons V1 _ o1 b1275 b767 b742 (List.nil : V2) b1266 b1266 b1295 e1279 e1280 (by rfl)
theorem e1282 : o2.add b1284 b1264=b1294 := @add_cons V1 _ o1 b1274 b766 b741 b1285 b1265 b1295 b1294 e1278 e1281 (by rfl)
theorem e1283 : o2.add b1283 b1263=b1293 := @add_cons V1 _ o1 b1273 b765 b740 b1284 b1264 b1294 b1293 e1277 e1282 (by rfl)
theorem e1284 : o2.add b1282 b1262=b1292 := @add_cons V1 _ o1 b1272 b764 b739 b1283 b1263 b1293 b1292 e1276 e1283 (by rfl)
theorem e1285 : o2.add b1281 b1261=b1291 := @add_cons V1 _ o1 b1271 b763 b738 b1282 b1262 b1292 b1291 e1275 e1284 (by rfl)
theorem e1286 : o2.add b1280 b1260=b1290 := @add_cons V1 _ o1 b1270 b762 b737 b1281 b1261 b1291 b1290 e1274 e1285 (by rfl)
theorem e1287 : o2.add b1279 b1259=b1289 := @add_cons V1 _ o1 b1269 b761 b736 b1280 b1260 b1290 b1289 e1273 e1286 (by rfl)
theorem e1288 : o2.add b1278 b1258=b1288 := @add_cons V1 _ o1 b1268 b760 b735 b1279 b1259 b1289 b1288 e1272 e1287 (by rfl)
theorem e1289 : o2.add b1277 b768=b1287 := @add_cons V1 _ o1 b1267 b759 b734 b1278 b1258 b1288 b1287 e1271 e1288 (by rfl)
theorem e1290 : o2.add b1276 b1286=b756 := @add_cons V1 _ o1 b733 (List.nil : V1) b733 b1277 b768 b1287 b756 e1270 e1289 (by rfl)
theorem e1291 : o2.mul b85 b16=b756 := @mul_cons V1 _ o1 b71 b758 b16 b768 b1276 b1286 b756 e1248 e1269 (by rfl) e1290
theorem e1292 : o2.scale b85 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e1293 : o2.scale b85 b17=b757 := @scale_cons V2 _ o2 b85 b16 b756 (List.nil : V3) (List.nil : V3) b757 e1291 e1292 (by rfl)
theorem e1294 : o3.add b757 (List.nil : V3)=b757 := by rfl
theorem e1295 : o3.mul b86 b17=b757 := @mul_cons V2 _ o2 b85 (List.nil : V3) b17 (List.nil : V3) b757 (List.nil : V3) b757 e708 e1293 (by rfl) e1294
theorem e1296 : o3.mul (List.nil : V3) (List.nil : V3)=(List.nil : V3) := by rfl
theorem e1297 : o1.add b620 b733=b1296 := by decide
theorem e1298 : o1.add b621 b734=b88 := by decide
theorem e1299 : o1.add b622 b735=b89 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
