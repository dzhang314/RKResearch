module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart005

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e750 : o2.add b1226 b1105=b1237 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1227 b1210 b1238 b1237 e34 e749 (by rfl)
theorem e751 : o2.add b1225 b1236=b576 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1226 b1105 b1237 b576 e34 e750 (by rfl)
theorem e752 : o2.mul b88 b47=b576 := @mul_cons V1 _ o1 b83 b589 b47 b1105 b1225 b1236 b576 e716 e732 (by rfl) e751
theorem e753 : o2.mul (List.nil : V2) b53=(List.nil : V2) := by rfl
theorem e754 : o1.mul b87 b48=b1264 := by decide
theorem e755 : o1.mul b87 b49=b1265 := by decide
theorem e756 : o1.mul b87 b50=b1266 := by decide
theorem e757 : o1.mul b87 b51=b1262 := by decide
theorem e758 : o1.mul b87 b52=b586 := by decide
theorem e759 : o1.scale b87 b1288=b1289 := @scale_cons V1 _ o1 b87 b52 b586 (List.nil : V2) (List.nil : V2) b1289 e758 e9 (by rfl)
theorem e760 : o1.scale b87 b1286=b1287 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1288 b1289 b1287 e2 e759 (by rfl)
theorem e761 : o1.scale b87 b1284=b1285 := @scale_cons V1 _ o1 b87 b51 b1262 b1286 b1287 b1285 e757 e760 (by rfl)
theorem e762 : o1.scale b87 b1282=b1283 := @scale_cons V1 _ o1 b87 b50 b1266 b1284 b1285 b1283 e756 e761 (by rfl)
theorem e763 : o1.scale b87 b1280=b1281 := @scale_cons V1 _ o1 b87 b49 b1265 b1282 b1283 b1281 e755 e762 (by rfl)
theorem e764 : o1.scale b87 b1278=b1279 := @scale_cons V1 _ o1 b87 b48 b1264 b1280 b1281 b1279 e754 e763 (by rfl)
theorem e765 : o1.scale b87 b1276=b1277 := @scale_cons V1 _ o1 b87 b17 b614 b1278 b1279 b1277 e6 e764 (by rfl)
theorem e766 : o1.scale b87 b1274=b1275 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1276 b1277 b1275 e2 e765 (by rfl)
theorem e767 : o1.scale b87 b1272=b1273 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1274 b1275 b1273 e2 e766 (by rfl)
theorem e768 : o1.scale b87 b1270=b1271 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1272 b1273 b1271 e2 e767 (by rfl)
theorem e769 : o1.scale b87 b1268=b1269 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1270 b1271 b1269 e2 e768 (by rfl)
theorem e770 : o1.scale b87 b53=b1267 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1268 b1269 b1267 e2 e769 (by rfl)
theorem e771 : o2.add b1267 (List.nil : V2)=b1267 := by rfl
theorem e772 : o2.mul b610 b53=b1267 := @mul_cons V1 _ o1 b87 (List.nil : V2) b53 (List.nil : V2) b1267 (List.nil : V2) b1267 e753 e770 (by rfl) e771
theorem e773 : o1.mul b86 b48=b1290 := by decide
theorem e774 : o1.mul b86 b49=b1291 := by decide
theorem e775 : o1.mul b86 b50=b1292 := by decide
theorem e776 : o1.mul b86 b51=b1293 := by decide
theorem e777 : o1.mul b86 b52=b585 := by decide
theorem e778 : o1.scale b86 b1288=b1305 := @scale_cons V1 _ o1 b86 b52 b585 (List.nil : V2) (List.nil : V2) b1305 e777 e26 (by rfl)
theorem e779 : o1.scale b86 b1286=b1304 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1288 b1305 b1304 e19 e778 (by rfl)
theorem e780 : o1.scale b86 b1284=b1303 := @scale_cons V1 _ o1 b86 b51 b1293 b1286 b1304 b1303 e776 e779 (by rfl)
theorem e781 : o1.scale b86 b1282=b1302 := @scale_cons V1 _ o1 b86 b50 b1292 b1284 b1303 b1302 e775 e780 (by rfl)
theorem e782 : o1.scale b86 b1280=b1301 := @scale_cons V1 _ o1 b86 b49 b1291 b1282 b1302 b1301 e774 e781 (by rfl)
theorem e783 : o1.scale b86 b1278=b1300 := @scale_cons V1 _ o1 b86 b48 b1290 b1280 b1301 b1300 e773 e782 (by rfl)
theorem e784 : o1.scale b86 b1276=b1299 := @scale_cons V1 _ o1 b86 b17 b631 b1278 b1300 b1299 e23 e783 (by rfl)
theorem e785 : o1.scale b86 b1274=b1298 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1276 b1299 b1298 e19 e784 (by rfl)
theorem e786 : o1.scale b86 b1272=b1297 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1274 b1298 b1297 e19 e785 (by rfl)
theorem e787 : o1.scale b86 b1270=b1296 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1272 b1297 b1296 e19 e786 (by rfl)
theorem e788 : o1.scale b86 b1268=b1295 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1270 b1296 b1295 e19 e787 (by rfl)
theorem e789 : o1.scale b86 b53=b1294 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1268 b1295 b1294 e19 e788 (by rfl)
theorem e790 : o1.add b631 (List.nil : V1)=b631 := by rfl
theorem e791 : o1.add b1290 b614=b1259 := by decide
theorem e792 : o1.add b1291 b1264=b1260 := by decide
theorem e793 : o1.add b1292 b1265=b1261 := by decide
theorem e794 : o1.add b1293 b1266=b1257 := by decide
theorem e795 : o1.add (List.nil : V1) b1262=b1262 := by rfl
theorem e796 : o1.add b585 (List.nil : V1)=b585 := by rfl
theorem e797 : o2.add (List.nil : V2) b1289=b1289 := by rfl
theorem e798 : o2.add b1305 b1287=b1317 := @add_cons V1 _ o1 b585 (List.nil : V1) b585 (List.nil : V2) b1289 b1289 b1317 e796 e797 (by rfl)
theorem e799 : o2.add b1304 b1285=b1316 := @add_cons V1 _ o1 (List.nil : V1) b1262 b1262 b1305 b1287 b1317 b1316 e795 e798 (by rfl)
theorem e800 : o2.add b1303 b1283=b1315 := @add_cons V1 _ o1 b1293 b1266 b1257 b1304 b1285 b1316 b1315 e794 e799 (by rfl)
theorem e801 : o2.add b1302 b1281=b1314 := @add_cons V1 _ o1 b1292 b1265 b1261 b1303 b1283 b1315 b1314 e793 e800 (by rfl)
theorem e802 : o2.add b1301 b1279=b1313 := @add_cons V1 _ o1 b1291 b1264 b1260 b1302 b1281 b1314 b1313 e792 e801 (by rfl)
theorem e803 : o2.add b1300 b1277=b1312 := @add_cons V1 _ o1 b1290 b614 b1259 b1301 b1279 b1313 b1312 e791 e802 (by rfl)
theorem e804 : o2.add b1299 b1275=b1311 := @add_cons V1 _ o1 b631 (List.nil : V1) b631 b1300 b1277 b1312 b1311 e790 e803 (by rfl)
theorem e805 : o2.add b1298 b1273=b1310 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1299 b1275 b1311 b1310 e34 e804 (by rfl)
theorem e806 : o2.add b1297 b1271=b1309 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1298 b1273 b1310 b1309 e34 e805 (by rfl)
theorem e807 : o2.add b1296 b1269=b1308 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1297 b1271 b1309 b1308 e34 e806 (by rfl)
theorem e808 : o2.add b1295 b1267=b1307 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1296 b1269 b1308 b1307 e34 e807 (by rfl)
theorem e809 : o2.add b1294 b1306=b1263 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1295 b1267 b1307 b1263 e34 e808 (by rfl)
theorem e810 : o2.mul b603 b53=b1263 := @mul_cons V1 _ o1 b86 b610 b53 b1267 b1294 b1306 b1263 e772 e789 (by rfl) e809
theorem e811 : o1.mul b85 b48=b1318 := by decide
theorem e812 : o1.mul b85 b49=b1319 := by decide
theorem e813 : o1.mul b85 b50=b1320 := by decide
theorem e814 : o1.mul b85 b51=b1321 := by decide
theorem e815 : o1.mul b85 b52=b1322 := by decide
theorem e816 : o1.scale b85 b1288=b1334 := @scale_cons V1 _ o1 b85 b52 b1322 (List.nil : V2) (List.nil : V2) b1334 e815 e57 (by rfl)
theorem e817 : o1.scale b85 b1286=b1333 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1288 b1334 b1333 e50 e816 (by rfl)
theorem e818 : o1.scale b85 b1284=b1332 := @scale_cons V1 _ o1 b85 b51 b1321 b1286 b1333 b1332 e814 e817 (by rfl)
theorem e819 : o1.scale b85 b1282=b1331 := @scale_cons V1 _ o1 b85 b50 b1320 b1284 b1332 b1331 e813 e818 (by rfl)
theorem e820 : o1.scale b85 b1280=b1330 := @scale_cons V1 _ o1 b85 b49 b1319 b1282 b1331 b1330 e812 e819 (by rfl)
theorem e821 : o1.scale b85 b1278=b1329 := @scale_cons V1 _ o1 b85 b48 b1318 b1280 b1330 b1329 e811 e820 (by rfl)
theorem e822 : o1.scale b85 b1276=b1328 := @scale_cons V1 _ o1 b85 b17 b650 b1278 b1329 b1328 e54 e821 (by rfl)
theorem e823 : o1.scale b85 b1274=b1327 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1276 b1328 b1327 e50 e822 (by rfl)
theorem e824 : o1.scale b85 b1272=b1326 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1274 b1327 b1326 e50 e823 (by rfl)
theorem e825 : o1.scale b85 b1270=b1325 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1272 b1326 b1325 e50 e824 (by rfl)
theorem e826 : o1.scale b85 b1268=b1324 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1270 b1325 b1324 e50 e825 (by rfl)
theorem e827 : o1.scale b85 b53=b1323 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1268 b1324 b1323 e50 e826 (by rfl)
theorem e828 : o1.add b650 (List.nil : V1)=b650 := by rfl
theorem e829 : o1.add b1318 b631=b1254 := by decide
theorem e830 : o1.add b1319 b1259=b1255 := by decide
theorem e831 : o1.add b1320 b1260=b1256 := by decide
theorem e832 : o1.add b1321 b1261=b1252 := by decide
theorem e833 : o1.add (List.nil : V1) b1257=b1257 := by rfl
theorem e834 : o1.add b1322 b1262=b584 := by decide
theorem e835 : o2.add (List.nil : V2) b1317=b1317 := by rfl
theorem e836 : o2.add b1334 b1316=b1346 := @add_cons V1 _ o1 b1322 b1262 b584 (List.nil : V2) b1317 b1317 b1346 e834 e835 (by rfl)
theorem e837 : o2.add b1333 b1315=b1345 := @add_cons V1 _ o1 (List.nil : V1) b1257 b1257 b1334 b1316 b1346 b1345 e833 e836 (by rfl)
theorem e838 : o2.add b1332 b1314=b1344 := @add_cons V1 _ o1 b1321 b1261 b1252 b1333 b1315 b1345 b1344 e832 e837 (by rfl)
theorem e839 : o2.add b1331 b1313=b1343 := @add_cons V1 _ o1 b1320 b1260 b1256 b1332 b1314 b1344 b1343 e831 e838 (by rfl)
theorem e840 : o2.add b1330 b1312=b1342 := @add_cons V1 _ o1 b1319 b1259 b1255 b1331 b1313 b1343 b1342 e830 e839 (by rfl)
theorem e841 : o2.add b1329 b1311=b1341 := @add_cons V1 _ o1 b1318 b631 b1254 b1330 b1312 b1342 b1341 e829 e840 (by rfl)
theorem e842 : o2.add b1328 b1310=b1340 := @add_cons V1 _ o1 b650 (List.nil : V1) b650 b1329 b1311 b1341 b1340 e828 e841 (by rfl)
theorem e843 : o2.add b1327 b1309=b1339 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1328 b1310 b1340 b1339 e34 e842 (by rfl)
theorem e844 : o2.add b1326 b1308=b1338 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1327 b1309 b1339 b1338 e34 e843 (by rfl)
theorem e845 : o2.add b1325 b1307=b1337 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1326 b1308 b1338 b1337 e34 e844 (by rfl)
theorem e846 : o2.add b1324 b1263=b1336 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1325 b1307 b1337 b1336 e34 e845 (by rfl)
theorem e847 : o2.add b1323 b1335=b1258 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1324 b1263 b1336 b1258 e34 e846 (by rfl)
theorem e848 : o2.mul b596 b53=b1258 := @mul_cons V1 _ o1 b85 b603 b53 b1263 b1323 b1335 b1258 e810 e827 (by rfl) e847
theorem e849 : o1.mul b84 b48=b1347 := by decide
theorem e850 : o1.mul b84 b49=b1348 := by decide
theorem e851 : o1.mul b84 b50=b1349 := by decide
theorem e852 : o1.mul b84 b51=b1350 := by decide
theorem e853 : o1.mul b84 b52=b1351 := by decide
theorem e854 : o1.scale b84 b1288=b1363 := @scale_cons V1 _ o1 b84 b52 b1351 (List.nil : V2) (List.nil : V2) b1363 e853 e87 (by rfl)
theorem e855 : o1.scale b84 b1286=b1362 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1288 b1363 b1362 e80 e854 (by rfl)
theorem e856 : o1.scale b84 b1284=b1361 := @scale_cons V1 _ o1 b84 b51 b1350 b1286 b1362 b1361 e852 e855 (by rfl)
theorem e857 : o1.scale b84 b1282=b1360 := @scale_cons V1 _ o1 b84 b50 b1349 b1284 b1361 b1360 e851 e856 (by rfl)
theorem e858 : o1.scale b84 b1280=b1359 := @scale_cons V1 _ o1 b84 b49 b1348 b1282 b1360 b1359 e850 e857 (by rfl)
theorem e859 : o1.scale b84 b1278=b1358 := @scale_cons V1 _ o1 b84 b48 b1347 b1280 b1359 b1358 e849 e858 (by rfl)
theorem e860 : o1.scale b84 b1276=b1357 := @scale_cons V1 _ o1 b84 b17 b669 b1278 b1358 b1357 e84 e859 (by rfl)
theorem e861 : o1.scale b84 b1274=b1356 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1276 b1357 b1356 e80 e860 (by rfl)
theorem e862 : o1.scale b84 b1272=b1355 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1274 b1356 b1355 e80 e861 (by rfl)
theorem e863 : o1.scale b84 b1270=b1354 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1272 b1355 b1354 e80 e862 (by rfl)
theorem e864 : o1.scale b84 b1268=b1353 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1270 b1354 b1353 e80 e863 (by rfl)
theorem e865 : o1.scale b84 b53=b1352 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1268 b1353 b1352 e80 e864 (by rfl)
theorem e866 : o1.add b669 (List.nil : V1)=b669 := by rfl
theorem e867 : o1.add b1347 b650=b1249 := by decide
theorem e868 : o1.add b1348 b1254=b1250 := by decide
theorem e869 : o1.add b1349 b1255=b1251 := by decide
theorem e870 : o1.add b1350 b1256=b581 := by decide
theorem e871 : o1.add (List.nil : V1) b1252=b1252 := by rfl
theorem e872 : o1.add b1351 b1257=b583 := by decide
theorem e873 : o2.add (List.nil : V2) b1346=b1346 := by rfl
theorem e874 : o2.add b1363 b1345=b1375 := @add_cons V1 _ o1 b1351 b1257 b583 (List.nil : V2) b1346 b1346 b1375 e872 e873 (by rfl)
theorem e875 : o2.add b1362 b1344=b1374 := @add_cons V1 _ o1 (List.nil : V1) b1252 b1252 b1363 b1345 b1375 b1374 e871 e874 (by rfl)
theorem e876 : o2.add b1361 b1343=b1373 := @add_cons V1 _ o1 b1350 b1256 b581 b1362 b1344 b1374 b1373 e870 e875 (by rfl)
theorem e877 : o2.add b1360 b1342=b1372 := @add_cons V1 _ o1 b1349 b1255 b1251 b1361 b1343 b1373 b1372 e869 e876 (by rfl)
theorem e878 : o2.add b1359 b1341=b1371 := @add_cons V1 _ o1 b1348 b1254 b1250 b1360 b1342 b1372 b1371 e868 e877 (by rfl)
theorem e879 : o2.add b1358 b1340=b1370 := @add_cons V1 _ o1 b1347 b650 b1249 b1359 b1341 b1371 b1370 e867 e878 (by rfl)
theorem e880 : o2.add b1357 b1339=b1369 := @add_cons V1 _ o1 b669 (List.nil : V1) b669 b1358 b1340 b1370 b1369 e866 e879 (by rfl)
theorem e881 : o2.add b1356 b1338=b1368 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1357 b1339 b1369 b1368 e34 e880 (by rfl)
theorem e882 : o2.add b1355 b1337=b1367 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1356 b1338 b1368 b1367 e34 e881 (by rfl)
theorem e883 : o2.add b1354 b1336=b1366 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1355 b1337 b1367 b1366 e34 e882 (by rfl)
theorem e884 : o2.add b1353 b1258=b1365 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1354 b1336 b1366 b1365 e34 e883 (by rfl)
theorem e885 : o2.add b1352 b1364=b1253 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1353 b1258 b1365 b1253 e34 e884 (by rfl)
theorem e886 : o2.mul b589 b53=b1253 := @mul_cons V1 _ o1 b84 b596 b53 b1258 b1352 b1364 b1253 e848 e865 (by rfl) e885
theorem e887 : o1.mul b83 b48=b1376 := by decide
theorem e888 : o1.mul b83 b49=b1377 := by decide
theorem e889 : o1.mul b83 b50=b1378 := by decide
theorem e890 : o1.mul b83 b51=b1379 := by decide
theorem e891 : o1.mul b83 b52=b1380 := by decide
theorem e892 : o1.scale b83 b1288=b1392 := @scale_cons V1 _ o1 b83 b52 b1380 (List.nil : V2) (List.nil : V2) b1392 e891 e117 (by rfl)
theorem e893 : o1.scale b83 b1286=b1391 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1288 b1392 b1391 e110 e892 (by rfl)
theorem e894 : o1.scale b83 b1284=b1390 := @scale_cons V1 _ o1 b83 b51 b1379 b1286 b1391 b1390 e890 e893 (by rfl)
theorem e895 : o1.scale b83 b1282=b1389 := @scale_cons V1 _ o1 b83 b50 b1378 b1284 b1390 b1389 e889 e894 (by rfl)
theorem e896 : o1.scale b83 b1280=b1388 := @scale_cons V1 _ o1 b83 b49 b1377 b1282 b1389 b1388 e888 e895 (by rfl)
theorem e897 : o1.scale b83 b1278=b1387 := @scale_cons V1 _ o1 b83 b48 b1376 b1280 b1388 b1387 e887 e896 (by rfl)
theorem e898 : o1.scale b83 b1276=b1386 := @scale_cons V1 _ o1 b83 b17 b429 b1278 b1387 b1386 e114 e897 (by rfl)
theorem e899 : o1.scale b83 b1274=b1385 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1276 b1386 b1385 e110 e898 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
