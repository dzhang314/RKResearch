module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart008

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1200 : o1.add b1637 (List.nil : V1)=b1637 := by rfl
theorem e1201 : o1.add b1708 b1644=b1638 := by decide
theorem e1202 : o1.add b1709 b1645=b1639 := by decide
theorem e1203 : o1.add b1710 b1646=b1640 := by decide
theorem e1204 : o1.add b1711 b1647=b1641 := by decide
theorem e1205 : o1.add b1712 b1648=b460 := by decide
theorem e1206 : o2.add (List.nil : V2) b1707=b1707 := by rfl
theorem e1207 : o2.add b1719 b1706=b1726 := @add_cons V1 _ o1 b1712 b1648 b460 (List.nil : V2) b1707 b1707 b1726 e1205 e1206 (by rfl)
theorem e1208 : o2.add b1718 b1705=b1725 := @add_cons V1 _ o1 b1711 b1647 b1641 b1719 b1706 b1726 b1725 e1204 e1207 (by rfl)
theorem e1209 : o2.add b1717 b1704=b1724 := @add_cons V1 _ o1 b1710 b1646 b1640 b1718 b1705 b1725 b1724 e1203 e1208 (by rfl)
theorem e1210 : o2.add b1716 b1703=b1723 := @add_cons V1 _ o1 b1709 b1645 b1639 b1717 b1704 b1724 b1723 e1202 e1209 (by rfl)
theorem e1211 : o2.add b1715 b1702=b1722 := @add_cons V1 _ o1 b1708 b1644 b1638 b1716 b1703 b1723 b1722 e1201 e1210 (by rfl)
theorem e1212 : o2.add b1714 b1649=b1721 := @add_cons V1 _ o1 b1637 (List.nil : V1) b1637 b1715 b1702 b1722 b1721 e1200 e1211 (by rfl)
theorem e1213 : o2.add b1713 b1720=b1642 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1714 b1649 b1721 b1642 e34 e1212 (by rfl)
theorem e1214 : o2.mul b1636 b20=b1642 := @mul_cons V1 _ o1 b78 b1643 b20 b1649 b1713 b1720 b1642 e1184 e1199 (by rfl) e1213
theorem e1215 : o1.mul b77 (List.nil : V1)=(List.nil : V1) := by decide
theorem e1216 : o1.mul b77 b14=b454 := by decide
theorem e1217 : o1.mul b77 b15=b1727 := by decide
theorem e1218 : o1.mul b77 b16=b1728 := by decide
theorem e1219 : o1.mul b77 b17=b1613 := by decide
theorem e1220 : o1.mul b77 b18=b1602 := by decide
theorem e1221 : o1.mul b77 b19=b1729 := by decide
theorem e1222 : o1.scale b77 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e1223 : o1.scale b77 b627=b1736 := @scale_cons V1 _ o1 b77 b19 b1729 (List.nil : V2) (List.nil : V2) b1736 e1221 e1222 (by rfl)
theorem e1224 : o1.scale b77 b625=b1735 := @scale_cons V1 _ o1 b77 b18 b1602 b627 b1736 b1735 e1220 e1223 (by rfl)
theorem e1225 : o1.scale b77 b623=b1734 := @scale_cons V1 _ o1 b77 b17 b1613 b625 b1735 b1734 e1219 e1224 (by rfl)
theorem e1226 : o1.scale b77 b621=b1733 := @scale_cons V1 _ o1 b77 b16 b1728 b623 b1734 b1733 e1218 e1225 (by rfl)
theorem e1227 : o1.scale b77 b619=b1732 := @scale_cons V1 _ o1 b77 b15 b1727 b621 b1733 b1732 e1217 e1226 (by rfl)
theorem e1228 : o1.scale b77 b617=b1731 := @scale_cons V1 _ o1 b77 b14 b454 b619 b1732 b1731 e1216 e1227 (by rfl)
theorem e1229 : o1.scale b77 b20=b1730 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b617 b1731 b1730 e1215 e1228 (by rfl)
theorem e1230 : o1.add b454 (List.nil : V1)=b454 := by rfl
theorem e1231 : o1.add b1727 b1637=b455 := by decide
theorem e1232 : o1.add b1728 b1638=b456 := by decide
theorem e1233 : o1.add b1613 b1639=b457 := by decide
theorem e1234 : o1.add b1602 b1640=b458 := by decide
theorem e1235 : o1.add b1729 b1641=b459 := by decide
theorem e1236 : o2.add (List.nil : V2) b1726=b1726 := by rfl
theorem e1237 : o2.add b1736 b1725=b1743 := @add_cons V1 _ o1 b1729 b1641 b459 (List.nil : V2) b1726 b1726 b1743 e1235 e1236 (by rfl)
theorem e1238 : o2.add b1735 b1724=b1742 := @add_cons V1 _ o1 b1602 b1640 b458 b1736 b1725 b1743 b1742 e1234 e1237 (by rfl)
theorem e1239 : o2.add b1734 b1723=b1741 := @add_cons V1 _ o1 b1613 b1639 b457 b1735 b1724 b1742 b1741 e1233 e1238 (by rfl)
theorem e1240 : o2.add b1733 b1722=b1740 := @add_cons V1 _ o1 b1728 b1638 b456 b1734 b1723 b1741 b1740 e1232 e1239 (by rfl)
theorem e1241 : o2.add b1732 b1721=b1739 := @add_cons V1 _ o1 b1727 b1637 b455 b1733 b1722 b1740 b1739 e1231 e1240 (by rfl)
theorem e1242 : o2.add b1731 b1642=b1738 := @add_cons V1 _ o1 b454 (List.nil : V1) b454 b1732 b1721 b1739 b1738 e1230 e1241 (by rfl)
theorem e1243 : o2.add b1730 b1737=b464 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1731 b1642 b1738 b464 e34 e1242 (by rfl)
theorem e1244 : o2.mul b82 b20=b464 := @mul_cons V1 _ o1 b77 b1636 b20 b1642 b1730 b1737 b464 e1214 e1229 (by rfl) e1243
theorem e1245 : o1.mul b81 b21=b1757 := by decide
theorem e1246 : o1.mul b81 b22=b1763 := by decide
theorem e1247 : o1.mul b81 b23=b1764 := by decide
theorem e1248 : o1.mul b81 b24=b1765 := by decide
theorem e1249 : o1.mul b81 b25=b1766 := by decide
theorem e1250 : o1.mul b81 b26=b474 := by decide
theorem e1251 : o1.scale b81 b740=b1774 := @scale_cons V1 _ o1 b81 b26 b474 (List.nil : V2) (List.nil : V2) b1774 e1250 e1115 (by rfl)
theorem e1252 : o1.scale b81 b738=b1773 := @scale_cons V1 _ o1 b81 b25 b1766 b740 b1774 b1773 e1249 e1251 (by rfl)
theorem e1253 : o1.scale b81 b736=b1772 := @scale_cons V1 _ o1 b81 b24 b1765 b738 b1773 b1772 e1248 e1252 (by rfl)
theorem e1254 : o1.scale b81 b734=b1771 := @scale_cons V1 _ o1 b81 b23 b1764 b736 b1772 b1771 e1247 e1253 (by rfl)
theorem e1255 : o1.scale b81 b732=b1770 := @scale_cons V1 _ o1 b81 b22 b1763 b734 b1771 b1770 e1246 e1254 (by rfl)
theorem e1256 : o1.scale b81 b730=b1769 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b732 b1770 b1769 e1108 e1255 (by rfl)
theorem e1257 : o1.scale b81 b728=b1768 := @scale_cons V1 _ o1 b81 b21 b1757 b730 b1769 b1768 e1245 e1256 (by rfl)
theorem e1258 : o1.scale b81 b27=b1767 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b728 b1768 b1767 e1108 e1257 (by rfl)
theorem e1259 : o2.add b1767 (List.nil : V2)=b1767 := by rfl
theorem e1260 : o2.mul b1657 b27=b1767 := @mul_cons V1 _ o1 b81 (List.nil : V2) b27 (List.nil : V2) b1767 (List.nil : V2) b1767 e140 e1258 (by rfl) e1259
theorem e1261 : o1.mul b80 b21=b1751 := by decide
theorem e1262 : o1.mul b80 b22=b1758 := by decide
theorem e1263 : o1.mul b80 b23=b1775 := by decide
theorem e1264 : o1.mul b80 b24=b1776 := by decide
theorem e1265 : o1.mul b80 b25=b1777 := by decide
theorem e1266 : o1.mul b80 b26=b1778 := by decide
theorem e1267 : o1.scale b80 b740=b1786 := @scale_cons V1 _ o1 b80 b26 b1778 (List.nil : V2) (List.nil : V2) b1786 e1266 e1132 (by rfl)
theorem e1268 : o1.scale b80 b738=b1785 := @scale_cons V1 _ o1 b80 b25 b1777 b740 b1786 b1785 e1265 e1267 (by rfl)
theorem e1269 : o1.scale b80 b736=b1784 := @scale_cons V1 _ o1 b80 b24 b1776 b738 b1785 b1784 e1264 e1268 (by rfl)
theorem e1270 : o1.scale b80 b734=b1783 := @scale_cons V1 _ o1 b80 b23 b1775 b736 b1784 b1783 e1263 e1269 (by rfl)
theorem e1271 : o1.scale b80 b732=b1782 := @scale_cons V1 _ o1 b80 b22 b1758 b734 b1783 b1782 e1262 e1270 (by rfl)
theorem e1272 : o1.scale b80 b730=b1781 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b732 b1782 b1781 e1125 e1271 (by rfl)
theorem e1273 : o1.scale b80 b728=b1780 := @scale_cons V1 _ o1 b80 b21 b1751 b730 b1781 b1780 e1261 e1272 (by rfl)
theorem e1274 : o1.scale b80 b27=b1779 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b728 b1780 b1779 e1125 e1273 (by rfl)
theorem e1275 : o1.add b1751 (List.nil : V1)=b1751 := by rfl
theorem e1276 : o1.add (List.nil : V1) b1757=b1757 := by rfl
theorem e1277 : o1.add b1758 (List.nil : V1)=b1758 := by rfl
theorem e1278 : o1.add b1775 b1763=b1759 := by decide
theorem e1279 : o1.add b1776 b1764=b1760 := by decide
theorem e1280 : o1.add b1777 b1765=b1761 := by decide
theorem e1281 : o1.add b1778 b1766=b1578 := by decide
theorem e1282 : o2.add (List.nil : V2) b1774=b1774 := by rfl
theorem e1283 : o2.add b1786 b1773=b1794 := @add_cons V1 _ o1 b1778 b1766 b1578 (List.nil : V2) b1774 b1774 b1794 e1281 e1282 (by rfl)
theorem e1284 : o2.add b1785 b1772=b1793 := @add_cons V1 _ o1 b1777 b1765 b1761 b1786 b1773 b1794 b1793 e1280 e1283 (by rfl)
theorem e1285 : o2.add b1784 b1771=b1792 := @add_cons V1 _ o1 b1776 b1764 b1760 b1785 b1772 b1793 b1792 e1279 e1284 (by rfl)
theorem e1286 : o2.add b1783 b1770=b1791 := @add_cons V1 _ o1 b1775 b1763 b1759 b1784 b1771 b1792 b1791 e1278 e1285 (by rfl)
theorem e1287 : o2.add b1782 b1769=b1790 := @add_cons V1 _ o1 b1758 (List.nil : V1) b1758 b1783 b1770 b1791 b1790 e1277 e1286 (by rfl)
theorem e1288 : o2.add b1781 b1768=b1789 := @add_cons V1 _ o1 (List.nil : V1) b1757 b1757 b1782 b1769 b1790 b1789 e1276 e1287 (by rfl)
theorem e1289 : o2.add b1780 b1767=b1788 := @add_cons V1 _ o1 b1751 (List.nil : V1) b1751 b1781 b1768 b1789 b1788 e1275 e1288 (by rfl)
theorem e1290 : o2.add b1779 b1787=b1762 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1780 b1767 b1788 b1762 e34 e1289 (by rfl)
theorem e1291 : o2.mul b1650 b27=b1762 := @mul_cons V1 _ o1 b80 b1657 b27 b1767 b1779 b1787 b1762 e1260 e1274 (by rfl) e1290
theorem e1292 : o1.mul b79 b21=b1745 := by decide
theorem e1293 : o1.mul b79 b22=b1795 := by decide
theorem e1294 : o1.mul b79 b23=b1796 := by decide
theorem e1295 : o1.mul b79 b24=b1797 := by decide
theorem e1296 : o1.mul b79 b25=b1798 := by decide
theorem e1297 : o1.mul b79 b26=b1799 := by decide
theorem e1298 : o1.scale b79 b740=b1807 := @scale_cons V1 _ o1 b79 b26 b1799 (List.nil : V2) (List.nil : V2) b1807 e1297 e1162 (by rfl)
theorem e1299 : o1.scale b79 b738=b1806 := @scale_cons V1 _ o1 b79 b25 b1798 b740 b1807 b1806 e1296 e1298 (by rfl)
theorem e1300 : o1.scale b79 b736=b1805 := @scale_cons V1 _ o1 b79 b24 b1797 b738 b1806 b1805 e1295 e1299 (by rfl)
theorem e1301 : o1.scale b79 b734=b1804 := @scale_cons V1 _ o1 b79 b23 b1796 b736 b1805 b1804 e1294 e1300 (by rfl)
theorem e1302 : o1.scale b79 b732=b1803 := @scale_cons V1 _ o1 b79 b22 b1795 b734 b1804 b1803 e1293 e1301 (by rfl)
theorem e1303 : o1.scale b79 b730=b1802 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b732 b1803 b1802 e1155 e1302 (by rfl)
theorem e1304 : o1.scale b79 b728=b1801 := @scale_cons V1 _ o1 b79 b21 b1745 b730 b1802 b1801 e1292 e1303 (by rfl)
theorem e1305 : o1.scale b79 b27=b1800 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b728 b1801 b1800 e1155 e1304 (by rfl)
theorem e1306 : o1.add b1745 (List.nil : V1)=b1745 := by rfl
theorem e1307 : o1.add (List.nil : V1) b1751=b1751 := by rfl
theorem e1308 : o1.add b1795 b1757=b1752 := by decide
theorem e1309 : o1.add b1796 b1758=b1753 := by decide
theorem e1310 : o1.add b1797 b1759=b1754 := by decide
theorem e1311 : o1.add b1798 b1760=b1755 := by decide
theorem e1312 : o1.add b1799 b1761=b1577 := by decide
theorem e1313 : o2.add (List.nil : V2) b1794=b1794 := by rfl
theorem e1314 : o2.add b1807 b1793=b1815 := @add_cons V1 _ o1 b1799 b1761 b1577 (List.nil : V2) b1794 b1794 b1815 e1312 e1313 (by rfl)
theorem e1315 : o2.add b1806 b1792=b1814 := @add_cons V1 _ o1 b1798 b1760 b1755 b1807 b1793 b1815 b1814 e1311 e1314 (by rfl)
theorem e1316 : o2.add b1805 b1791=b1813 := @add_cons V1 _ o1 b1797 b1759 b1754 b1806 b1792 b1814 b1813 e1310 e1315 (by rfl)
theorem e1317 : o2.add b1804 b1790=b1812 := @add_cons V1 _ o1 b1796 b1758 b1753 b1805 b1791 b1813 b1812 e1309 e1316 (by rfl)
theorem e1318 : o2.add b1803 b1789=b1811 := @add_cons V1 _ o1 b1795 b1757 b1752 b1804 b1790 b1812 b1811 e1308 e1317 (by rfl)
theorem e1319 : o2.add b1802 b1788=b1810 := @add_cons V1 _ o1 (List.nil : V1) b1751 b1751 b1803 b1789 b1811 b1810 e1307 e1318 (by rfl)
theorem e1320 : o2.add b1801 b1762=b1809 := @add_cons V1 _ o1 b1745 (List.nil : V1) b1745 b1802 b1788 b1810 b1809 e1306 e1319 (by rfl)
theorem e1321 : o2.add b1800 b1808=b1756 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1801 b1762 b1809 b1756 e34 e1320 (by rfl)
theorem e1322 : o2.mul b1643 b27=b1756 := @mul_cons V1 _ o1 b79 b1650 b27 b1762 b1800 b1808 b1756 e1291 e1305 (by rfl) e1321
theorem e1323 : o1.mul b78 b21=b1570 := by decide
theorem e1324 : o1.mul b78 b22=b1816 := by decide
theorem e1325 : o1.mul b78 b23=b1817 := by decide
theorem e1326 : o1.mul b78 b24=b1818 := by decide
theorem e1327 : o1.mul b78 b25=b1819 := by decide
theorem e1328 : o1.mul b78 b26=b1820 := by decide
theorem e1329 : o1.scale b78 b740=b1828 := @scale_cons V1 _ o1 b78 b26 b1820 (List.nil : V2) (List.nil : V2) b1828 e1328 e1192 (by rfl)
theorem e1330 : o1.scale b78 b738=b1827 := @scale_cons V1 _ o1 b78 b25 b1819 b740 b1828 b1827 e1327 e1329 (by rfl)
theorem e1331 : o1.scale b78 b736=b1826 := @scale_cons V1 _ o1 b78 b24 b1818 b738 b1827 b1826 e1326 e1330 (by rfl)
theorem e1332 : o1.scale b78 b734=b1825 := @scale_cons V1 _ o1 b78 b23 b1817 b736 b1826 b1825 e1325 e1331 (by rfl)
theorem e1333 : o1.scale b78 b732=b1824 := @scale_cons V1 _ o1 b78 b22 b1816 b734 b1825 b1824 e1324 e1332 (by rfl)
theorem e1334 : o1.scale b78 b730=b1823 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b732 b1824 b1823 e1185 e1333 (by rfl)
theorem e1335 : o1.scale b78 b728=b1822 := @scale_cons V1 _ o1 b78 b21 b1570 b730 b1823 b1822 e1323 e1334 (by rfl)
theorem e1336 : o1.scale b78 b27=b1821 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b728 b1822 b1821 e1185 e1335 (by rfl)
theorem e1337 : o1.add b1570 (List.nil : V1)=b1570 := by rfl
theorem e1338 : o1.add (List.nil : V1) b1745=b1745 := by rfl
theorem e1339 : o1.add b1816 b1751=b1746 := by decide
theorem e1340 : o1.add b1817 b1752=b1747 := by decide
theorem e1341 : o1.add b1818 b1753=b1748 := by decide
theorem e1342 : o1.add b1819 b1754=b1749 := by decide
theorem e1343 : o1.add b1820 b1755=b1576 := by decide
theorem e1344 : o2.add (List.nil : V2) b1815=b1815 := by rfl
theorem e1345 : o2.add b1828 b1814=b1836 := @add_cons V1 _ o1 b1820 b1755 b1576 (List.nil : V2) b1815 b1815 b1836 e1343 e1344 (by rfl)
theorem e1346 : o2.add b1827 b1813=b1835 := @add_cons V1 _ o1 b1819 b1754 b1749 b1828 b1814 b1836 b1835 e1342 e1345 (by rfl)
theorem e1347 : o2.add b1826 b1812=b1834 := @add_cons V1 _ o1 b1818 b1753 b1748 b1827 b1813 b1835 b1834 e1341 e1346 (by rfl)
theorem e1348 : o2.add b1825 b1811=b1833 := @add_cons V1 _ o1 b1817 b1752 b1747 b1826 b1812 b1834 b1833 e1340 e1347 (by rfl)
theorem e1349 : o2.add b1824 b1810=b1832 := @add_cons V1 _ o1 b1816 b1751 b1746 b1825 b1811 b1833 b1832 e1339 e1348 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
