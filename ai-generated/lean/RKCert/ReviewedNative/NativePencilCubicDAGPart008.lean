module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart007

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1050 : o2.add b1524 b1506=b1536 := @add_cons V1 _ o1 b1512 b1414 b1409 b1525 b1507 b1537 b1536 e1042 e1049 (by rfl)
theorem e1051 : o2.add b1523 b1505=b1535 := @add_cons V1 _ o1 b1511 b1413 b1408 b1524 b1506 b1536 b1535 e1041 e1050 (by rfl)
theorem e1052 : o2.add b1522 b1504=b1534 := @add_cons V1 _ o1 b1407 (List.nil : V1) b1407 b1523 b1505 b1535 b1534 e1040 e1051 (by rfl)
theorem e1053 : o2.add b1521 b1503=b1533 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1522 b1504 b1534 b1533 e34 e1052 (by rfl)
theorem e1054 : o2.add b1520 b1502=b1532 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1521 b1503 b1533 b1532 e34 e1053 (by rfl)
theorem e1055 : o2.add b1519 b1501=b1531 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1520 b1502 b1532 b1531 e34 e1054 (by rfl)
theorem e1056 : o2.add b1518 b1500=b1530 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1519 b1501 b1531 b1530 e34 e1055 (by rfl)
theorem e1057 : o2.add b1517 b1418=b1529 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1518 b1500 b1530 b1529 e34 e1056 (by rfl)
theorem e1058 : o2.add b1516 b1528=b1412 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1517 b1418 b1529 b1412 e34 e1057 (by rfl)
theorem e1059 : o2.mul b589 b60=b1412 := @mul_cons V1 _ o1 b84 b596 b60 b1418 b1516 b1528 b1412 e1021 e1039 (by rfl) e1058
theorem e1060 : o1.mul b83 b54=b441 := by decide
theorem e1061 : o1.mul b83 b55=b1540 := by decide
theorem e1062 : o1.mul b83 b56=b1541 := by decide
theorem e1063 : o1.mul b83 b57=b1542 := by decide
theorem e1064 : o1.mul b83 b58=b1543 := by decide
theorem e1065 : o1.mul b83 b59=b1544 := by decide
theorem e1066 : o1.scale b83 b1451=b1556 := @scale_cons V1 _ o1 b83 b59 b1544 (List.nil : V2) (List.nil : V2) b1556 e1065 e117 (by rfl)
theorem e1067 : o1.scale b83 b1449=b1555 := @scale_cons V1 _ o1 b83 b58 b1543 b1451 b1556 b1555 e1064 e1066 (by rfl)
theorem e1068 : o1.scale b83 b1447=b1554 := @scale_cons V1 _ o1 b83 b57 b1542 b1449 b1555 b1554 e1063 e1067 (by rfl)
theorem e1069 : o1.scale b83 b1445=b1553 := @scale_cons V1 _ o1 b83 b56 b1541 b1447 b1554 b1553 e1062 e1068 (by rfl)
theorem e1070 : o1.scale b83 b1443=b1552 := @scale_cons V1 _ o1 b83 b55 b1540 b1445 b1553 b1552 e1061 e1069 (by rfl)
theorem e1071 : o1.scale b83 b1441=b1551 := @scale_cons V1 _ o1 b83 b54 b441 b1443 b1552 b1551 e1060 e1070 (by rfl)
theorem e1072 : o1.scale b83 b1439=b1550 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1441 b1551 b1550 e110 e1071 (by rfl)
theorem e1073 : o1.scale b83 b1437=b1549 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1439 b1550 b1549 e110 e1072 (by rfl)
theorem e1074 : o1.scale b83 b1435=b1548 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1437 b1549 b1548 e110 e1073 (by rfl)
theorem e1075 : o1.scale b83 b1433=b1547 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1435 b1548 b1547 e110 e1074 (by rfl)
theorem e1076 : o1.scale b83 b1431=b1546 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1433 b1547 b1546 e110 e1075 (by rfl)
theorem e1077 : o1.scale b83 b60=b1545 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b1431 b1546 b1545 e110 e1076 (by rfl)
theorem e1078 : o1.add b441 (List.nil : V1)=b441 := by rfl
theorem e1079 : o1.add b1540 b1407=b442 := by decide
theorem e1080 : o1.add b1541 b1408=b443 := by decide
theorem e1081 : o1.add b1542 b1409=b444 := by decide
theorem e1082 : o1.add b1543 b1410=b445 := by decide
theorem e1083 : o1.add b1544 b1411=b446 := by decide
theorem e1084 : o2.add (List.nil : V2) b1539=b1539 := by rfl
theorem e1085 : o2.add b1556 b1538=b1568 := @add_cons V1 _ o1 b1544 b1411 b446 (List.nil : V2) b1539 b1539 b1568 e1083 e1084 (by rfl)
theorem e1086 : o2.add b1555 b1537=b1567 := @add_cons V1 _ o1 b1543 b1410 b445 b1556 b1538 b1568 b1567 e1082 e1085 (by rfl)
theorem e1087 : o2.add b1554 b1536=b1566 := @add_cons V1 _ o1 b1542 b1409 b444 b1555 b1537 b1567 b1566 e1081 e1086 (by rfl)
theorem e1088 : o2.add b1553 b1535=b1565 := @add_cons V1 _ o1 b1541 b1408 b443 b1554 b1536 b1566 b1565 e1080 e1087 (by rfl)
theorem e1089 : o2.add b1552 b1534=b1564 := @add_cons V1 _ o1 b1540 b1407 b442 b1553 b1535 b1565 b1564 e1079 e1088 (by rfl)
theorem e1090 : o2.add b1551 b1533=b1563 := @add_cons V1 _ o1 b441 (List.nil : V1) b441 b1552 b1534 b1564 b1563 e1078 e1089 (by rfl)
theorem e1091 : o2.add b1550 b1532=b1562 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1551 b1533 b1563 b1562 e34 e1090 (by rfl)
theorem e1092 : o2.add b1549 b1531=b1561 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1550 b1532 b1562 b1561 e34 e1091 (by rfl)
theorem e1093 : o2.add b1548 b1530=b1560 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1549 b1531 b1561 b1560 e34 e1092 (by rfl)
theorem e1094 : o2.add b1547 b1529=b1559 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1548 b1530 b1560 b1559 e34 e1093 (by rfl)
theorem e1095 : o2.add b1546 b1412=b1558 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1547 b1529 b1559 b1558 e34 e1094 (by rfl)
theorem e1096 : o2.add b1545 b1557=b451 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1546 b1412 b1558 b451 e34 e1095 (by rfl)
theorem e1097 : o2.mul b88 b60=b451 := @mul_cons V1 _ o1 b83 b589 b60 b1412 b1545 b1557 b451 e1059 e1077 (by rfl) e1096
theorem e1098 : o2.scale b88 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e1099 : o2.scale b88 b1405=b1406 := @scale_cons V2 _ o2 b88 b60 b451 (List.nil : V3) (List.nil : V3) b1406 e1097 e1098 (by rfl)
theorem e1100 : o2.scale b88 b1247=b1248 := @scale_cons V2 _ o2 b88 b53 b587 b1405 b1406 b1248 e924 e1099 (by rfl)
theorem e1101 : o2.scale b88 b1099=b1100 := @scale_cons V2 _ o2 b88 b47 b576 b1247 b1248 b1100 e752 e1100 (by rfl)
theorem e1102 : o2.scale b88 b957=b958 := @scale_cons V2 _ o2 b88 b41 b565 b1099 b1100 b958 e589 e1101 (by rfl)
theorem e1103 : o2.scale b88 b825=b826 := @scale_cons V2 _ o2 b88 b34 b554 b957 b958 b826 e430 e1102 (by rfl)
theorem e1104 : o2.scale b88 b703=b704 := @scale_cons V2 _ o2 b88 b27 b543 b825 b826 b704 e280 e1103 (by rfl)
theorem e1105 : o2.scale b88 b61=b588 := @scale_cons V2 _ o2 b88 b20 b532 b703 b704 b588 e139 e1104 (by rfl)
theorem e1106 : o3.add b588 (List.nil : V3)=b588 := by rfl
theorem e1107 : o3.mul b521 b61=b588 := @mul_cons V2 _ o2 b88 (List.nil : V3) b61 (List.nil : V3) b588 (List.nil : V3) b588 e0 e1105 (by rfl) e1106
theorem e1108 : o1.mul b81 (List.nil : V1)=(List.nil : V1) := by decide
theorem e1109 : o1.mul b81 b14=b1658 := by decide
theorem e1110 : o1.mul b81 b15=b1659 := by decide
theorem e1111 : o1.mul b81 b16=b1660 := by decide
theorem e1112 : o1.mul b81 b17=b1661 := by decide
theorem e1113 : o1.mul b81 b18=b1662 := by decide
theorem e1114 : o1.mul b81 b19=b463 := by decide
theorem e1115 : o1.scale b81 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1116 : o1.scale b81 b627=b1669 := @scale_cons V1 _ o1 b81 b19 b463 (List.nil : V2) (List.nil : V2) b1669 e1114 e1115 (by rfl)
theorem e1117 : o1.scale b81 b625=b1668 := @scale_cons V1 _ o1 b81 b18 b1662 b627 b1669 b1668 e1113 e1116 (by rfl)
theorem e1118 : o1.scale b81 b623=b1667 := @scale_cons V1 _ o1 b81 b17 b1661 b625 b1668 b1667 e1112 e1117 (by rfl)
theorem e1119 : o1.scale b81 b621=b1666 := @scale_cons V1 _ o1 b81 b16 b1660 b623 b1667 b1666 e1111 e1118 (by rfl)
theorem e1120 : o1.scale b81 b619=b1665 := @scale_cons V1 _ o1 b81 b15 b1659 b621 b1666 b1665 e1110 e1119 (by rfl)
theorem e1121 : o1.scale b81 b617=b1664 := @scale_cons V1 _ o1 b81 b14 b1658 b619 b1665 b1664 e1109 e1120 (by rfl)
theorem e1122 : o1.scale b81 b20=b1663 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b617 b1664 b1663 e1108 e1121 (by rfl)
theorem e1123 : o2.add b1663 (List.nil : V2)=b1663 := by rfl
theorem e1124 : o2.mul b1657 b20=b1663 := @mul_cons V1 _ o1 b81 (List.nil : V2) b20 (List.nil : V2) b1663 (List.nil : V2) b1663 e1 e1122 (by rfl) e1123
theorem e1125 : o1.mul b80 (List.nil : V1)=(List.nil : V1) := by decide
theorem e1126 : o1.mul b80 b14=b1651 := by decide
theorem e1127 : o1.mul b80 b15=b1670 := by decide
theorem e1128 : o1.mul b80 b16=b1671 := by decide
theorem e1129 : o1.mul b80 b17=b1672 := by decide
theorem e1130 : o1.mul b80 b18=b1673 := by decide
theorem e1131 : o1.mul b80 b19=b1674 := by decide
theorem e1132 : o1.scale b80 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1133 : o1.scale b80 b627=b1681 := @scale_cons V1 _ o1 b80 b19 b1674 (List.nil : V2) (List.nil : V2) b1681 e1131 e1132 (by rfl)
theorem e1134 : o1.scale b80 b625=b1680 := @scale_cons V1 _ o1 b80 b18 b1673 b627 b1681 b1680 e1130 e1133 (by rfl)
theorem e1135 : o1.scale b80 b623=b1679 := @scale_cons V1 _ o1 b80 b17 b1672 b625 b1680 b1679 e1129 e1134 (by rfl)
theorem e1136 : o1.scale b80 b621=b1678 := @scale_cons V1 _ o1 b80 b16 b1671 b623 b1679 b1678 e1128 e1135 (by rfl)
theorem e1137 : o1.scale b80 b619=b1677 := @scale_cons V1 _ o1 b80 b15 b1670 b621 b1678 b1677 e1127 e1136 (by rfl)
theorem e1138 : o1.scale b80 b617=b1676 := @scale_cons V1 _ o1 b80 b14 b1651 b619 b1677 b1676 e1126 e1137 (by rfl)
theorem e1139 : o1.scale b80 b20=b1675 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b617 b1676 b1675 e1125 e1138 (by rfl)
theorem e1140 : o1.add b1651 (List.nil : V1)=b1651 := by rfl
theorem e1141 : o1.add b1670 b1658=b1652 := by decide
theorem e1142 : o1.add b1671 b1659=b1653 := by decide
theorem e1143 : o1.add b1672 b1660=b1654 := by decide
theorem e1144 : o1.add b1673 b1661=b1655 := by decide
theorem e1145 : o1.add b1674 b1662=b462 := by decide
theorem e1146 : o2.add (List.nil : V2) b1669=b1669 := by rfl
theorem e1147 : o2.add b1681 b1668=b1688 := @add_cons V1 _ o1 b1674 b1662 b462 (List.nil : V2) b1669 b1669 b1688 e1145 e1146 (by rfl)
theorem e1148 : o2.add b1680 b1667=b1687 := @add_cons V1 _ o1 b1673 b1661 b1655 b1681 b1668 b1688 b1687 e1144 e1147 (by rfl)
theorem e1149 : o2.add b1679 b1666=b1686 := @add_cons V1 _ o1 b1672 b1660 b1654 b1680 b1667 b1687 b1686 e1143 e1148 (by rfl)
theorem e1150 : o2.add b1678 b1665=b1685 := @add_cons V1 _ o1 b1671 b1659 b1653 b1679 b1666 b1686 b1685 e1142 e1149 (by rfl)
theorem e1151 : o2.add b1677 b1664=b1684 := @add_cons V1 _ o1 b1670 b1658 b1652 b1678 b1665 b1685 b1684 e1141 e1150 (by rfl)
theorem e1152 : o2.add b1676 b1663=b1683 := @add_cons V1 _ o1 b1651 (List.nil : V1) b1651 b1677 b1664 b1684 b1683 e1140 e1151 (by rfl)
theorem e1153 : o2.add b1675 b1682=b1656 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1676 b1663 b1683 b1656 e34 e1152 (by rfl)
theorem e1154 : o2.mul b1650 b20=b1656 := @mul_cons V1 _ o1 b80 b1657 b20 b1663 b1675 b1682 b1656 e1124 e1139 (by rfl) e1153
theorem e1155 : o1.mul b79 (List.nil : V1)=(List.nil : V1) := by decide
theorem e1156 : o1.mul b79 b14=b1644 := by decide
theorem e1157 : o1.mul b79 b15=b1689 := by decide
theorem e1158 : o1.mul b79 b16=b1690 := by decide
theorem e1159 : o1.mul b79 b17=b1691 := by decide
theorem e1160 : o1.mul b79 b18=b1692 := by decide
theorem e1161 : o1.mul b79 b19=b1693 := by decide
theorem e1162 : o1.scale b79 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1163 : o1.scale b79 b627=b1700 := @scale_cons V1 _ o1 b79 b19 b1693 (List.nil : V2) (List.nil : V2) b1700 e1161 e1162 (by rfl)
theorem e1164 : o1.scale b79 b625=b1699 := @scale_cons V1 _ o1 b79 b18 b1692 b627 b1700 b1699 e1160 e1163 (by rfl)
theorem e1165 : o1.scale b79 b623=b1698 := @scale_cons V1 _ o1 b79 b17 b1691 b625 b1699 b1698 e1159 e1164 (by rfl)
theorem e1166 : o1.scale b79 b621=b1697 := @scale_cons V1 _ o1 b79 b16 b1690 b623 b1698 b1697 e1158 e1165 (by rfl)
theorem e1167 : o1.scale b79 b619=b1696 := @scale_cons V1 _ o1 b79 b15 b1689 b621 b1697 b1696 e1157 e1166 (by rfl)
theorem e1168 : o1.scale b79 b617=b1695 := @scale_cons V1 _ o1 b79 b14 b1644 b619 b1696 b1695 e1156 e1167 (by rfl)
theorem e1169 : o1.scale b79 b20=b1694 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b617 b1695 b1694 e1155 e1168 (by rfl)
theorem e1170 : o1.add b1644 (List.nil : V1)=b1644 := by rfl
theorem e1171 : o1.add b1689 b1651=b1645 := by decide
theorem e1172 : o1.add b1690 b1652=b1646 := by decide
theorem e1173 : o1.add b1691 b1653=b1647 := by decide
theorem e1174 : o1.add b1692 b1654=b1648 := by decide
theorem e1175 : o1.add b1693 b1655=b461 := by decide
theorem e1176 : o2.add (List.nil : V2) b1688=b1688 := by rfl
theorem e1177 : o2.add b1700 b1687=b1707 := @add_cons V1 _ o1 b1693 b1655 b461 (List.nil : V2) b1688 b1688 b1707 e1175 e1176 (by rfl)
theorem e1178 : o2.add b1699 b1686=b1706 := @add_cons V1 _ o1 b1692 b1654 b1648 b1700 b1687 b1707 b1706 e1174 e1177 (by rfl)
theorem e1179 : o2.add b1698 b1685=b1705 := @add_cons V1 _ o1 b1691 b1653 b1647 b1699 b1686 b1706 b1705 e1173 e1178 (by rfl)
theorem e1180 : o2.add b1697 b1684=b1704 := @add_cons V1 _ o1 b1690 b1652 b1646 b1698 b1685 b1705 b1704 e1172 e1179 (by rfl)
theorem e1181 : o2.add b1696 b1683=b1703 := @add_cons V1 _ o1 b1689 b1651 b1645 b1697 b1684 b1704 b1703 e1171 e1180 (by rfl)
theorem e1182 : o2.add b1695 b1656=b1702 := @add_cons V1 _ o1 b1644 (List.nil : V1) b1644 b1696 b1683 b1703 b1702 e1170 e1181 (by rfl)
theorem e1183 : o2.add b1694 b1701=b1649 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1695 b1656 b1702 b1649 e34 e1182 (by rfl)
theorem e1184 : o2.mul b1643 b20=b1649 := @mul_cons V1 _ o1 b79 b1650 b20 b1656 b1694 b1701 b1649 e1154 e1169 (by rfl) e1183
theorem e1185 : o1.mul b78 (List.nil : V1)=(List.nil : V1) := by decide
theorem e1186 : o1.mul b78 b14=b1637 := by decide
theorem e1187 : o1.mul b78 b15=b1708 := by decide
theorem e1188 : o1.mul b78 b16=b1709 := by decide
theorem e1189 : o1.mul b78 b17=b1710 := by decide
theorem e1190 : o1.mul b78 b18=b1711 := by decide
theorem e1191 : o1.mul b78 b19=b1712 := by decide
theorem e1192 : o1.scale b78 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1193 : o1.scale b78 b627=b1719 := @scale_cons V1 _ o1 b78 b19 b1712 (List.nil : V2) (List.nil : V2) b1719 e1191 e1192 (by rfl)
theorem e1194 : o1.scale b78 b625=b1718 := @scale_cons V1 _ o1 b78 b18 b1711 b627 b1719 b1718 e1190 e1193 (by rfl)
theorem e1195 : o1.scale b78 b623=b1717 := @scale_cons V1 _ o1 b78 b17 b1710 b625 b1718 b1717 e1189 e1194 (by rfl)
theorem e1196 : o1.scale b78 b621=b1716 := @scale_cons V1 _ o1 b78 b16 b1709 b623 b1717 b1716 e1188 e1195 (by rfl)
theorem e1197 : o1.scale b78 b619=b1715 := @scale_cons V1 _ o1 b78 b15 b1708 b621 b1716 b1715 e1187 e1196 (by rfl)
theorem e1198 : o1.scale b78 b617=b1714 := @scale_cons V1 _ o1 b78 b14 b1637 b619 b1715 b1714 e1186 e1197 (by rfl)
theorem e1199 : o1.scale b78 b20=b1713 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b617 b1714 b1713 e1185 e1198 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
