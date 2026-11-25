module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart006

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e900 : o1.scale b83 b1272=b1384 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1274 b1385 b1384 e110 e899 (by rfl)
theorem e901 : o1.scale b83 b1270=b1383 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1272 b1384 b1383 e110 e900 (by rfl)
theorem e902 : o1.scale b83 b1268=b1382 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1270 b1383 b1382 e110 e901 (by rfl)
theorem e903 : o1.scale b83 b53=b1381 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1268 b1382 b1381 e110 e902 (by rfl)
theorem e904 : o1.add b429 (List.nil : V1)=b429 := by rfl
theorem e905 : o1.add b1376 b669=b577 := by decide
theorem e906 : o1.add b1377 b1249=b578 := by decide
theorem e907 : o1.add b1378 b1250=b579 := by decide
theorem e908 : o1.add b1379 b1251=b580 := by decide
theorem e909 : o1.add (List.nil : V1) b581=b581 := by rfl
theorem e910 : o1.add b1380 b1252=b582 := by decide
theorem e911 : o2.add (List.nil : V2) b1375=b1375 := by rfl
theorem e912 : o2.add b1392 b1374=b1404 := @add_cons V1 _ o1 b1380 b1252 b582 (List.nil : V2) b1375 b1375 b1404 e910 e911 (by rfl)
theorem e913 : o2.add b1391 b1373=b1403 := @add_cons V1 _ o1 (List.nil : V1) b581 b581 b1392 b1374 b1404 b1403 e909 e912 (by rfl)
theorem e914 : o2.add b1390 b1372=b1402 := @add_cons V1 _ o1 b1379 b1251 b580 b1391 b1373 b1403 b1402 e908 e913 (by rfl)
theorem e915 : o2.add b1389 b1371=b1401 := @add_cons V1 _ o1 b1378 b1250 b579 b1390 b1372 b1402 b1401 e907 e914 (by rfl)
theorem e916 : o2.add b1388 b1370=b1400 := @add_cons V1 _ o1 b1377 b1249 b578 b1389 b1371 b1401 b1400 e906 e915 (by rfl)
theorem e917 : o2.add b1387 b1369=b1399 := @add_cons V1 _ o1 b1376 b669 b577 b1388 b1370 b1400 b1399 e905 e916 (by rfl)
theorem e918 : o2.add b1386 b1368=b1398 := @add_cons V1 _ o1 b429 (List.nil : V1) b429 b1387 b1369 b1399 b1398 e904 e917 (by rfl)
theorem e919 : o2.add b1385 b1367=b1397 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1386 b1368 b1398 b1397 e34 e918 (by rfl)
theorem e920 : o2.add b1384 b1366=b1396 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1385 b1367 b1397 b1396 e34 e919 (by rfl)
theorem e921 : o2.add b1383 b1365=b1395 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1384 b1366 b1396 b1395 e34 e920 (by rfl)
theorem e922 : o2.add b1382 b1253=b1394 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1383 b1365 b1395 b1394 e34 e921 (by rfl)
theorem e923 : o2.add b1381 b1393=b587 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1382 b1253 b1394 b587 e34 e922 (by rfl)
theorem e924 : o2.mul b88 b53=b587 := @mul_cons V1 _ o1 b83 b589 b53 b1253 b1381 b1393 b587 e886 e903 (by rfl) e923
theorem e925 : o2.mul (List.nil : V2) b60=(List.nil : V2) := by rfl
theorem e926 : o1.mul b87 b54=b1425 := by decide
theorem e927 : o1.mul b87 b55=b1426 := by decide
theorem e928 : o1.mul b87 b56=b1427 := by decide
theorem e929 : o1.mul b87 b57=b1428 := by decide
theorem e930 : o1.mul b87 b58=b1429 := by decide
theorem e931 : o1.mul b87 b59=b450 := by decide
theorem e932 : o1.scale b87 b1451=b1452 := @scale_cons V1 _ o1 b87 b59 b450 (List.nil : V2) (List.nil : V2) b1452 e931 e9 (by rfl)
theorem e933 : o1.scale b87 b1449=b1450 := @scale_cons V1 _ o1 b87 b58 b1429 b1451 b1452 b1450 e930 e932 (by rfl)
theorem e934 : o1.scale b87 b1447=b1448 := @scale_cons V1 _ o1 b87 b57 b1428 b1449 b1450 b1448 e929 e933 (by rfl)
theorem e935 : o1.scale b87 b1445=b1446 := @scale_cons V1 _ o1 b87 b56 b1427 b1447 b1448 b1446 e928 e934 (by rfl)
theorem e936 : o1.scale b87 b1443=b1444 := @scale_cons V1 _ o1 b87 b55 b1426 b1445 b1446 b1444 e927 e935 (by rfl)
theorem e937 : o1.scale b87 b1441=b1442 := @scale_cons V1 _ o1 b87 b54 b1425 b1443 b1444 b1442 e926 e936 (by rfl)
theorem e938 : o1.scale b87 b1439=b1440 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1441 b1442 b1440 e2 e937 (by rfl)
theorem e939 : o1.scale b87 b1437=b1438 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1439 b1440 b1438 e2 e938 (by rfl)
theorem e940 : o1.scale b87 b1435=b1436 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1437 b1438 b1436 e2 e939 (by rfl)
theorem e941 : o1.scale b87 b1433=b1434 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1435 b1436 b1434 e2 e940 (by rfl)
theorem e942 : o1.scale b87 b1431=b1432 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1433 b1434 b1432 e2 e941 (by rfl)
theorem e943 : o1.scale b87 b60=b1430 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b1431 b1432 b1430 e2 e942 (by rfl)
theorem e944 : o2.add b1430 (List.nil : V2)=b1430 := by rfl
theorem e945 : o2.mul b610 b60=b1430 := @mul_cons V1 _ o1 b87 (List.nil : V2) b60 (List.nil : V2) b1430 (List.nil : V2) b1430 e925 e943 (by rfl) e944
theorem e946 : o1.mul b86 b54=b1419 := by decide
theorem e947 : o1.mul b86 b55=b1453 := by decide
theorem e948 : o1.mul b86 b56=b1454 := by decide
theorem e949 : o1.mul b86 b57=b1455 := by decide
theorem e950 : o1.mul b86 b58=b1456 := by decide
theorem e951 : o1.mul b86 b59=b1457 := by decide
theorem e952 : o1.scale b86 b1451=b1469 := @scale_cons V1 _ o1 b86 b59 b1457 (List.nil : V2) (List.nil : V2) b1469 e951 e26 (by rfl)
theorem e953 : o1.scale b86 b1449=b1468 := @scale_cons V1 _ o1 b86 b58 b1456 b1451 b1469 b1468 e950 e952 (by rfl)
theorem e954 : o1.scale b86 b1447=b1467 := @scale_cons V1 _ o1 b86 b57 b1455 b1449 b1468 b1467 e949 e953 (by rfl)
theorem e955 : o1.scale b86 b1445=b1466 := @scale_cons V1 _ o1 b86 b56 b1454 b1447 b1467 b1466 e948 e954 (by rfl)
theorem e956 : o1.scale b86 b1443=b1465 := @scale_cons V1 _ o1 b86 b55 b1453 b1445 b1466 b1465 e947 e955 (by rfl)
theorem e957 : o1.scale b86 b1441=b1464 := @scale_cons V1 _ o1 b86 b54 b1419 b1443 b1465 b1464 e946 e956 (by rfl)
theorem e958 : o1.scale b86 b1439=b1463 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1441 b1464 b1463 e19 e957 (by rfl)
theorem e959 : o1.scale b86 b1437=b1462 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1439 b1463 b1462 e19 e958 (by rfl)
theorem e960 : o1.scale b86 b1435=b1461 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1437 b1462 b1461 e19 e959 (by rfl)
theorem e961 : o1.scale b86 b1433=b1460 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1435 b1461 b1460 e19 e960 (by rfl)
theorem e962 : o1.scale b86 b1431=b1459 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1433 b1460 b1459 e19 e961 (by rfl)
theorem e963 : o1.scale b86 b60=b1458 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b1431 b1459 b1458 e19 e962 (by rfl)
theorem e964 : o1.add b1419 (List.nil : V1)=b1419 := by rfl
theorem e965 : o1.add b1453 b1425=b1420 := by decide
theorem e966 : o1.add b1454 b1426=b1421 := by decide
theorem e967 : o1.add b1455 b1427=b1422 := by decide
theorem e968 : o1.add b1456 b1428=b1423 := by decide
theorem e969 : o1.add b1457 b1429=b449 := by decide
theorem e970 : o2.add (List.nil : V2) b1452=b1452 := by rfl
theorem e971 : o2.add b1469 b1450=b1481 := @add_cons V1 _ o1 b1457 b1429 b449 (List.nil : V2) b1452 b1452 b1481 e969 e970 (by rfl)
theorem e972 : o2.add b1468 b1448=b1480 := @add_cons V1 _ o1 b1456 b1428 b1423 b1469 b1450 b1481 b1480 e968 e971 (by rfl)
theorem e973 : o2.add b1467 b1446=b1479 := @add_cons V1 _ o1 b1455 b1427 b1422 b1468 b1448 b1480 b1479 e967 e972 (by rfl)
theorem e974 : o2.add b1466 b1444=b1478 := @add_cons V1 _ o1 b1454 b1426 b1421 b1467 b1446 b1479 b1478 e966 e973 (by rfl)
theorem e975 : o2.add b1465 b1442=b1477 := @add_cons V1 _ o1 b1453 b1425 b1420 b1466 b1444 b1478 b1477 e965 e974 (by rfl)
theorem e976 : o2.add b1464 b1440=b1476 := @add_cons V1 _ o1 b1419 (List.nil : V1) b1419 b1465 b1442 b1477 b1476 e964 e975 (by rfl)
theorem e977 : o2.add b1463 b1438=b1475 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1464 b1440 b1476 b1475 e34 e976 (by rfl)
theorem e978 : o2.add b1462 b1436=b1474 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1463 b1438 b1475 b1474 e34 e977 (by rfl)
theorem e979 : o2.add b1461 b1434=b1473 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1462 b1436 b1474 b1473 e34 e978 (by rfl)
theorem e980 : o2.add b1460 b1432=b1472 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1461 b1434 b1473 b1472 e34 e979 (by rfl)
theorem e981 : o2.add b1459 b1430=b1471 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1460 b1432 b1472 b1471 e34 e980 (by rfl)
theorem e982 : o2.add b1458 b1470=b1424 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1459 b1430 b1471 b1424 e34 e981 (by rfl)
theorem e983 : o2.mul b603 b60=b1424 := @mul_cons V1 _ o1 b86 b610 b60 b1430 b1458 b1470 b1424 e945 e963 (by rfl) e982
theorem e984 : o1.mul b85 b54=b1413 := by decide
theorem e985 : o1.mul b85 b55=b1482 := by decide
theorem e986 : o1.mul b85 b56=b1483 := by decide
theorem e987 : o1.mul b85 b57=b1484 := by decide
theorem e988 : o1.mul b85 b58=b1485 := by decide
theorem e989 : o1.mul b85 b59=b1486 := by decide
theorem e990 : o1.scale b85 b1451=b1498 := @scale_cons V1 _ o1 b85 b59 b1486 (List.nil : V2) (List.nil : V2) b1498 e989 e57 (by rfl)
theorem e991 : o1.scale b85 b1449=b1497 := @scale_cons V1 _ o1 b85 b58 b1485 b1451 b1498 b1497 e988 e990 (by rfl)
theorem e992 : o1.scale b85 b1447=b1496 := @scale_cons V1 _ o1 b85 b57 b1484 b1449 b1497 b1496 e987 e991 (by rfl)
theorem e993 : o1.scale b85 b1445=b1495 := @scale_cons V1 _ o1 b85 b56 b1483 b1447 b1496 b1495 e986 e992 (by rfl)
theorem e994 : o1.scale b85 b1443=b1494 := @scale_cons V1 _ o1 b85 b55 b1482 b1445 b1495 b1494 e985 e993 (by rfl)
theorem e995 : o1.scale b85 b1441=b1493 := @scale_cons V1 _ o1 b85 b54 b1413 b1443 b1494 b1493 e984 e994 (by rfl)
theorem e996 : o1.scale b85 b1439=b1492 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1441 b1493 b1492 e50 e995 (by rfl)
theorem e997 : o1.scale b85 b1437=b1491 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1439 b1492 b1491 e50 e996 (by rfl)
theorem e998 : o1.scale b85 b1435=b1490 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1437 b1491 b1490 e50 e997 (by rfl)
theorem e999 : o1.scale b85 b1433=b1489 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1435 b1490 b1489 e50 e998 (by rfl)
theorem e1000 : o1.scale b85 b1431=b1488 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1433 b1489 b1488 e50 e999 (by rfl)
theorem e1001 : o1.scale b85 b60=b1487 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b1431 b1488 b1487 e50 e1000 (by rfl)
theorem e1002 : o1.add b1413 (List.nil : V1)=b1413 := by rfl
theorem e1003 : o1.add b1482 b1419=b1414 := by decide
theorem e1004 : o1.add b1483 b1420=b1415 := by decide
theorem e1005 : o1.add b1484 b1421=b1416 := by decide
theorem e1006 : o1.add b1485 b1422=b1417 := by decide
theorem e1007 : o1.add b1486 b1423=b448 := by decide
theorem e1008 : o2.add (List.nil : V2) b1481=b1481 := by rfl
theorem e1009 : o2.add b1498 b1480=b1510 := @add_cons V1 _ o1 b1486 b1423 b448 (List.nil : V2) b1481 b1481 b1510 e1007 e1008 (by rfl)
theorem e1010 : o2.add b1497 b1479=b1509 := @add_cons V1 _ o1 b1485 b1422 b1417 b1498 b1480 b1510 b1509 e1006 e1009 (by rfl)
theorem e1011 : o2.add b1496 b1478=b1508 := @add_cons V1 _ o1 b1484 b1421 b1416 b1497 b1479 b1509 b1508 e1005 e1010 (by rfl)
theorem e1012 : o2.add b1495 b1477=b1507 := @add_cons V1 _ o1 b1483 b1420 b1415 b1496 b1478 b1508 b1507 e1004 e1011 (by rfl)
theorem e1013 : o2.add b1494 b1476=b1506 := @add_cons V1 _ o1 b1482 b1419 b1414 b1495 b1477 b1507 b1506 e1003 e1012 (by rfl)
theorem e1014 : o2.add b1493 b1475=b1505 := @add_cons V1 _ o1 b1413 (List.nil : V1) b1413 b1494 b1476 b1506 b1505 e1002 e1013 (by rfl)
theorem e1015 : o2.add b1492 b1474=b1504 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1493 b1475 b1505 b1504 e34 e1014 (by rfl)
theorem e1016 : o2.add b1491 b1473=b1503 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1492 b1474 b1504 b1503 e34 e1015 (by rfl)
theorem e1017 : o2.add b1490 b1472=b1502 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1491 b1473 b1503 b1502 e34 e1016 (by rfl)
theorem e1018 : o2.add b1489 b1471=b1501 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1490 b1472 b1502 b1501 e34 e1017 (by rfl)
theorem e1019 : o2.add b1488 b1424=b1500 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1489 b1471 b1501 b1500 e34 e1018 (by rfl)
theorem e1020 : o2.add b1487 b1499=b1418 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1488 b1424 b1500 b1418 e34 e1019 (by rfl)
theorem e1021 : o2.mul b596 b60=b1418 := @mul_cons V1 _ o1 b85 b603 b60 b1424 b1487 b1499 b1418 e983 e1001 (by rfl) e1020
theorem e1022 : o1.mul b84 b54=b1407 := by decide
theorem e1023 : o1.mul b84 b55=b1511 := by decide
theorem e1024 : o1.mul b84 b56=b1512 := by decide
theorem e1025 : o1.mul b84 b57=b1513 := by decide
theorem e1026 : o1.mul b84 b58=b1514 := by decide
theorem e1027 : o1.mul b84 b59=b1515 := by decide
theorem e1028 : o1.scale b84 b1451=b1527 := @scale_cons V1 _ o1 b84 b59 b1515 (List.nil : V2) (List.nil : V2) b1527 e1027 e87 (by rfl)
theorem e1029 : o1.scale b84 b1449=b1526 := @scale_cons V1 _ o1 b84 b58 b1514 b1451 b1527 b1526 e1026 e1028 (by rfl)
theorem e1030 : o1.scale b84 b1447=b1525 := @scale_cons V1 _ o1 b84 b57 b1513 b1449 b1526 b1525 e1025 e1029 (by rfl)
theorem e1031 : o1.scale b84 b1445=b1524 := @scale_cons V1 _ o1 b84 b56 b1512 b1447 b1525 b1524 e1024 e1030 (by rfl)
theorem e1032 : o1.scale b84 b1443=b1523 := @scale_cons V1 _ o1 b84 b55 b1511 b1445 b1524 b1523 e1023 e1031 (by rfl)
theorem e1033 : o1.scale b84 b1441=b1522 := @scale_cons V1 _ o1 b84 b54 b1407 b1443 b1523 b1522 e1022 e1032 (by rfl)
theorem e1034 : o1.scale b84 b1439=b1521 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1441 b1522 b1521 e80 e1033 (by rfl)
theorem e1035 : o1.scale b84 b1437=b1520 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1439 b1521 b1520 e80 e1034 (by rfl)
theorem e1036 : o1.scale b84 b1435=b1519 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1437 b1520 b1519 e80 e1035 (by rfl)
theorem e1037 : o1.scale b84 b1433=b1518 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1435 b1519 b1518 e80 e1036 (by rfl)
theorem e1038 : o1.scale b84 b1431=b1517 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1433 b1518 b1517 e80 e1037 (by rfl)
theorem e1039 : o1.scale b84 b60=b1516 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b1431 b1517 b1516 e80 e1038 (by rfl)
theorem e1040 : o1.add b1407 (List.nil : V1)=b1407 := by rfl
theorem e1041 : o1.add b1511 b1413=b1408 := by decide
theorem e1042 : o1.add b1512 b1414=b1409 := by decide
theorem e1043 : o1.add b1513 b1415=b1410 := by decide
theorem e1044 : o1.add b1514 b1416=b1411 := by decide
theorem e1045 : o1.add b1515 b1417=b447 := by decide
theorem e1046 : o2.add (List.nil : V2) b1510=b1510 := by rfl
theorem e1047 : o2.add b1527 b1509=b1539 := @add_cons V1 _ o1 b1515 b1417 b447 (List.nil : V2) b1510 b1510 b1539 e1045 e1046 (by rfl)
theorem e1048 : o2.add b1526 b1508=b1538 := @add_cons V1 _ o1 b1514 b1416 b1411 b1527 b1509 b1539 b1538 e1044 e1047 (by rfl)
theorem e1049 : o2.add b1525 b1507=b1537 := @add_cons V1 _ o1 b1513 b1415 b1410 b1526 b1508 b1538 b1537 e1043 e1048 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
