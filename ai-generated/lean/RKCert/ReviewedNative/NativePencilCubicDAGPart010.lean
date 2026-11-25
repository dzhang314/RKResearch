module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart009

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1350 : o2.add b1823 b1809=b1831 := @add_cons V1 _ o1 (List.nil : V1) b1745 b1745 b1824 b1810 b1832 b1831 e1338 e1349 (by rfl)
theorem e1351 : o2.add b1822 b1756=b1830 := @add_cons V1 _ o1 b1570 (List.nil : V1) b1570 b1823 b1809 b1831 b1830 e1337 e1350 (by rfl)
theorem e1352 : o2.add b1821 b1829=b1750 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1822 b1756 b1830 b1750 e34 e1351 (by rfl)
theorem e1353 : o2.mul b1636 b27=b1750 := @mul_cons V1 _ o1 b78 b1643 b27 b1756 b1821 b1829 b1750 e1322 e1336 (by rfl) e1352
theorem e1354 : o1.mul b77 b21=b1569 := by decide
theorem e1355 : o1.mul b77 b22=b1837 := by decide
theorem e1356 : o1.mul b77 b23=b1838 := by decide
theorem e1357 : o1.mul b77 b24=b1839 := by decide
theorem e1358 : o1.mul b77 b25=b1840 := by decide
theorem e1359 : o1.mul b77 b26=b1841 := by decide
theorem e1360 : o1.scale b77 b740=b1849 := @scale_cons V1 _ o1 b77 b26 b1841 (List.nil : V2) (List.nil : V2) b1849 e1359 e1222 (by rfl)
theorem e1361 : o1.scale b77 b738=b1848 := @scale_cons V1 _ o1 b77 b25 b1840 b740 b1849 b1848 e1358 e1360 (by rfl)
theorem e1362 : o1.scale b77 b736=b1847 := @scale_cons V1 _ o1 b77 b24 b1839 b738 b1848 b1847 e1357 e1361 (by rfl)
theorem e1363 : o1.scale b77 b734=b1846 := @scale_cons V1 _ o1 b77 b23 b1838 b736 b1847 b1846 e1356 e1362 (by rfl)
theorem e1364 : o1.scale b77 b732=b1845 := @scale_cons V1 _ o1 b77 b22 b1837 b734 b1846 b1845 e1355 e1363 (by rfl)
theorem e1365 : o1.scale b77 b730=b1844 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b732 b1845 b1844 e1215 e1364 (by rfl)
theorem e1366 : o1.scale b77 b728=b1843 := @scale_cons V1 _ o1 b77 b21 b1569 b730 b1844 b1843 e1354 e1365 (by rfl)
theorem e1367 : o1.scale b77 b27=b1842 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b728 b1843 b1842 e1215 e1366 (by rfl)
theorem e1368 : o1.add b1569 (List.nil : V1)=b1569 := by rfl
theorem e1369 : o1.add (List.nil : V1) b1570=b1570 := by rfl
theorem e1370 : o1.add b1837 b1745=b1571 := by decide
theorem e1371 : o1.add b1838 b1746=b1572 := by decide
theorem e1372 : o1.add b1839 b1747=b1573 := by decide
theorem e1373 : o1.add b1840 b1748=b1574 := by decide
theorem e1374 : o1.add b1841 b1749=b1575 := by decide
theorem e1375 : o2.add (List.nil : V2) b1836=b1836 := by rfl
theorem e1376 : o2.add b1849 b1835=b1857 := @add_cons V1 _ o1 b1841 b1749 b1575 (List.nil : V2) b1836 b1836 b1857 e1374 e1375 (by rfl)
theorem e1377 : o2.add b1848 b1834=b1856 := @add_cons V1 _ o1 b1840 b1748 b1574 b1849 b1835 b1857 b1856 e1373 e1376 (by rfl)
theorem e1378 : o2.add b1847 b1833=b1855 := @add_cons V1 _ o1 b1839 b1747 b1573 b1848 b1834 b1856 b1855 e1372 e1377 (by rfl)
theorem e1379 : o2.add b1846 b1832=b1854 := @add_cons V1 _ o1 b1838 b1746 b1572 b1847 b1833 b1855 b1854 e1371 e1378 (by rfl)
theorem e1380 : o2.add b1845 b1831=b1853 := @add_cons V1 _ o1 b1837 b1745 b1571 b1846 b1832 b1854 b1853 e1370 e1379 (by rfl)
theorem e1381 : o2.add b1844 b1830=b1852 := @add_cons V1 _ o1 (List.nil : V1) b1570 b1570 b1845 b1831 b1853 b1852 e1369 e1380 (by rfl)
theorem e1382 : o2.add b1843 b1750=b1851 := @add_cons V1 _ o1 b1569 (List.nil : V1) b1569 b1844 b1830 b1852 b1851 e1368 e1381 (by rfl)
theorem e1383 : o2.add b1842 b1850=b1579 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1843 b1750 b1851 b1579 e34 e1382 (by rfl)
theorem e1384 : o2.mul b82 b27=b1579 := @mul_cons V1 _ o1 b77 b1636 b27 b1750 b1842 b1850 b1579 e1353 e1367 (by rfl) e1383
theorem e1385 : o1.mul b81 b28=b1877 := by decide
theorem e1386 : o1.mul b81 b29=b1872 := by decide
theorem e1387 : o1.mul b81 b30=b1878 := by decide
theorem e1388 : o1.mul b81 b31=b1879 := by decide
theorem e1389 : o1.mul b81 b32=b1880 := by decide
theorem e1390 : o1.mul b81 b33=b485 := by decide
theorem e1391 : o1.scale b81 b864=b1889 := @scale_cons V1 _ o1 b81 b33 b485 (List.nil : V2) (List.nil : V2) b1889 e1390 e1115 (by rfl)
theorem e1392 : o1.scale b81 b862=b1888 := @scale_cons V1 _ o1 b81 b32 b1880 b864 b1889 b1888 e1389 e1391 (by rfl)
theorem e1393 : o1.scale b81 b860=b1887 := @scale_cons V1 _ o1 b81 b31 b1879 b862 b1888 b1887 e1388 e1392 (by rfl)
theorem e1394 : o1.scale b81 b858=b1886 := @scale_cons V1 _ o1 b81 b30 b1878 b860 b1887 b1886 e1387 e1393 (by rfl)
theorem e1395 : o1.scale b81 b856=b1885 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b858 b1886 b1885 e1108 e1394 (by rfl)
theorem e1396 : o1.scale b81 b854=b1884 := @scale_cons V1 _ o1 b81 b29 b1872 b856 b1885 b1884 e1386 e1395 (by rfl)
theorem e1397 : o1.scale b81 b852=b1883 := @scale_cons V1 _ o1 b81 b28 b1877 b854 b1884 b1883 e1385 e1396 (by rfl)
theorem e1398 : o1.scale b81 b850=b1882 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b852 b1883 b1882 e1108 e1397 (by rfl)
theorem e1399 : o1.scale b81 b34=b1881 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b850 b1882 b1881 e1108 e1398 (by rfl)
theorem e1400 : o2.add b1881 (List.nil : V2)=b1881 := by rfl
theorem e1401 : o2.mul b1657 b34=b1881 := @mul_cons V1 _ o1 b81 (List.nil : V2) b34 (List.nil : V2) b1881 (List.nil : V2) b1881 e281 e1399 (by rfl) e1400
theorem e1402 : o1.mul b80 b28=b1871 := by decide
theorem e1403 : o1.mul b80 b29=b1890 := by decide
theorem e1404 : o1.mul b80 b30=b1873 := by decide
theorem e1405 : o1.mul b80 b31=b1891 := by decide
theorem e1406 : o1.mul b80 b32=b1892 := by decide
theorem e1407 : o1.mul b80 b33=b1893 := by decide
theorem e1408 : o1.scale b80 b864=b1902 := @scale_cons V1 _ o1 b80 b33 b1893 (List.nil : V2) (List.nil : V2) b1902 e1407 e1132 (by rfl)
theorem e1409 : o1.scale b80 b862=b1901 := @scale_cons V1 _ o1 b80 b32 b1892 b864 b1902 b1901 e1406 e1408 (by rfl)
theorem e1410 : o1.scale b80 b860=b1900 := @scale_cons V1 _ o1 b80 b31 b1891 b862 b1901 b1900 e1405 e1409 (by rfl)
theorem e1411 : o1.scale b80 b858=b1899 := @scale_cons V1 _ o1 b80 b30 b1873 b860 b1900 b1899 e1404 e1410 (by rfl)
theorem e1412 : o1.scale b80 b856=b1898 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b858 b1899 b1898 e1125 e1411 (by rfl)
theorem e1413 : o1.scale b80 b854=b1897 := @scale_cons V1 _ o1 b80 b29 b1890 b856 b1898 b1897 e1403 e1412 (by rfl)
theorem e1414 : o1.scale b80 b852=b1896 := @scale_cons V1 _ o1 b80 b28 b1871 b854 b1897 b1896 e1402 e1413 (by rfl)
theorem e1415 : o1.scale b80 b850=b1895 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b852 b1896 b1895 e1125 e1414 (by rfl)
theorem e1416 : o1.scale b80 b34=b1894 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b850 b1895 b1894 e1125 e1415 (by rfl)
theorem e1417 : o1.add b1871 (List.nil : V1)=b1871 := by rfl
theorem e1418 : o1.add b1890 b1877=b1866 := by decide
theorem e1419 : o1.add (List.nil : V1) b1872=b1872 := by rfl
theorem e1420 : o1.add b1873 (List.nil : V1)=b1873 := by rfl
theorem e1421 : o1.add b1891 b1878=b1874 := by decide
theorem e1422 : o1.add b1892 b1879=b1875 := by decide
theorem e1423 : o1.add b1893 b1880=b1589 := by decide
theorem e1424 : o2.add (List.nil : V2) b1889=b1889 := by rfl
theorem e1425 : o2.add b1902 b1888=b1911 := @add_cons V1 _ o1 b1893 b1880 b1589 (List.nil : V2) b1889 b1889 b1911 e1423 e1424 (by rfl)
theorem e1426 : o2.add b1901 b1887=b1910 := @add_cons V1 _ o1 b1892 b1879 b1875 b1902 b1888 b1911 b1910 e1422 e1425 (by rfl)
theorem e1427 : o2.add b1900 b1886=b1909 := @add_cons V1 _ o1 b1891 b1878 b1874 b1901 b1887 b1910 b1909 e1421 e1426 (by rfl)
theorem e1428 : o2.add b1899 b1885=b1908 := @add_cons V1 _ o1 b1873 (List.nil : V1) b1873 b1900 b1886 b1909 b1908 e1420 e1427 (by rfl)
theorem e1429 : o2.add b1898 b1884=b1907 := @add_cons V1 _ o1 (List.nil : V1) b1872 b1872 b1899 b1885 b1908 b1907 e1419 e1428 (by rfl)
theorem e1430 : o2.add b1897 b1883=b1906 := @add_cons V1 _ o1 b1890 b1877 b1866 b1898 b1884 b1907 b1906 e1418 e1429 (by rfl)
theorem e1431 : o2.add b1896 b1882=b1905 := @add_cons V1 _ o1 b1871 (List.nil : V1) b1871 b1897 b1883 b1906 b1905 e1417 e1430 (by rfl)
theorem e1432 : o2.add b1895 b1881=b1904 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1896 b1882 b1905 b1904 e34 e1431 (by rfl)
theorem e1433 : o2.add b1894 b1903=b1876 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1895 b1881 b1904 b1876 e34 e1432 (by rfl)
theorem e1434 : o2.mul b1650 b34=b1876 := @mul_cons V1 _ o1 b80 b1657 b34 b1881 b1894 b1903 b1876 e1401 e1416 (by rfl) e1433
theorem e1435 : o1.mul b79 b28=b1865 := by decide
theorem e1436 : o1.mul b79 b29=b1912 := by decide
theorem e1437 : o1.mul b79 b30=b1913 := by decide
theorem e1438 : o1.mul b79 b31=b1914 := by decide
theorem e1439 : o1.mul b79 b32=b1915 := by decide
theorem e1440 : o1.mul b79 b33=b1916 := by decide
theorem e1441 : o1.scale b79 b864=b1925 := @scale_cons V1 _ o1 b79 b33 b1916 (List.nil : V2) (List.nil : V2) b1925 e1440 e1162 (by rfl)
theorem e1442 : o1.scale b79 b862=b1924 := @scale_cons V1 _ o1 b79 b32 b1915 b864 b1925 b1924 e1439 e1441 (by rfl)
theorem e1443 : o1.scale b79 b860=b1923 := @scale_cons V1 _ o1 b79 b31 b1914 b862 b1924 b1923 e1438 e1442 (by rfl)
theorem e1444 : o1.scale b79 b858=b1922 := @scale_cons V1 _ o1 b79 b30 b1913 b860 b1923 b1922 e1437 e1443 (by rfl)
theorem e1445 : o1.scale b79 b856=b1921 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b858 b1922 b1921 e1155 e1444 (by rfl)
theorem e1446 : o1.scale b79 b854=b1920 := @scale_cons V1 _ o1 b79 b29 b1912 b856 b1921 b1920 e1436 e1445 (by rfl)
theorem e1447 : o1.scale b79 b852=b1919 := @scale_cons V1 _ o1 b79 b28 b1865 b854 b1920 b1919 e1435 e1446 (by rfl)
theorem e1448 : o1.scale b79 b850=b1918 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b852 b1919 b1918 e1155 e1447 (by rfl)
theorem e1449 : o1.scale b79 b34=b1917 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b850 b1918 b1917 e1155 e1448 (by rfl)
theorem e1450 : o1.add b1865 (List.nil : V1)=b1865 := by rfl
theorem e1451 : o1.add b1912 b1871=b1860 := by decide
theorem e1452 : o1.add (List.nil : V1) b1866=b1866 := by rfl
theorem e1453 : o1.add b1913 b1872=b1867 := by decide
theorem e1454 : o1.add b1914 b1873=b1868 := by decide
theorem e1455 : o1.add b1915 b1874=b1869 := by decide
theorem e1456 : o1.add b1916 b1875=b1588 := by decide
theorem e1457 : o2.add (List.nil : V2) b1911=b1911 := by rfl
theorem e1458 : o2.add b1925 b1910=b1934 := @add_cons V1 _ o1 b1916 b1875 b1588 (List.nil : V2) b1911 b1911 b1934 e1456 e1457 (by rfl)
theorem e1459 : o2.add b1924 b1909=b1933 := @add_cons V1 _ o1 b1915 b1874 b1869 b1925 b1910 b1934 b1933 e1455 e1458 (by rfl)
theorem e1460 : o2.add b1923 b1908=b1932 := @add_cons V1 _ o1 b1914 b1873 b1868 b1924 b1909 b1933 b1932 e1454 e1459 (by rfl)
theorem e1461 : o2.add b1922 b1907=b1931 := @add_cons V1 _ o1 b1913 b1872 b1867 b1923 b1908 b1932 b1931 e1453 e1460 (by rfl)
theorem e1462 : o2.add b1921 b1906=b1930 := @add_cons V1 _ o1 (List.nil : V1) b1866 b1866 b1922 b1907 b1931 b1930 e1452 e1461 (by rfl)
theorem e1463 : o2.add b1920 b1905=b1929 := @add_cons V1 _ o1 b1912 b1871 b1860 b1921 b1906 b1930 b1929 e1451 e1462 (by rfl)
theorem e1464 : o2.add b1919 b1904=b1928 := @add_cons V1 _ o1 b1865 (List.nil : V1) b1865 b1920 b1905 b1929 b1928 e1450 e1463 (by rfl)
theorem e1465 : o2.add b1918 b1876=b1927 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1919 b1904 b1928 b1927 e34 e1464 (by rfl)
theorem e1466 : o2.add b1917 b1926=b1870 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1918 b1876 b1927 b1870 e34 e1465 (by rfl)
theorem e1467 : o2.mul b1643 b34=b1870 := @mul_cons V1 _ o1 b79 b1650 b34 b1876 b1917 b1926 b1870 e1434 e1449 (by rfl) e1466
theorem e1468 : o1.mul b78 b28=b1859 := by decide
theorem e1469 : o1.mul b78 b29=b1935 := by decide
theorem e1470 : o1.mul b78 b30=b1936 := by decide
theorem e1471 : o1.mul b78 b31=b1937 := by decide
theorem e1472 : o1.mul b78 b32=b1938 := by decide
theorem e1473 : o1.mul b78 b33=b1939 := by decide
theorem e1474 : o1.scale b78 b864=b1948 := @scale_cons V1 _ o1 b78 b33 b1939 (List.nil : V2) (List.nil : V2) b1948 e1473 e1192 (by rfl)
theorem e1475 : o1.scale b78 b862=b1947 := @scale_cons V1 _ o1 b78 b32 b1938 b864 b1948 b1947 e1472 e1474 (by rfl)
theorem e1476 : o1.scale b78 b860=b1946 := @scale_cons V1 _ o1 b78 b31 b1937 b862 b1947 b1946 e1471 e1475 (by rfl)
theorem e1477 : o1.scale b78 b858=b1945 := @scale_cons V1 _ o1 b78 b30 b1936 b860 b1946 b1945 e1470 e1476 (by rfl)
theorem e1478 : o1.scale b78 b856=b1944 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b858 b1945 b1944 e1185 e1477 (by rfl)
theorem e1479 : o1.scale b78 b854=b1943 := @scale_cons V1 _ o1 b78 b29 b1935 b856 b1944 b1943 e1469 e1478 (by rfl)
theorem e1480 : o1.scale b78 b852=b1942 := @scale_cons V1 _ o1 b78 b28 b1859 b854 b1943 b1942 e1468 e1479 (by rfl)
theorem e1481 : o1.scale b78 b850=b1941 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b852 b1942 b1941 e1185 e1480 (by rfl)
theorem e1482 : o1.scale b78 b34=b1940 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b850 b1941 b1940 e1185 e1481 (by rfl)
theorem e1483 : o1.add b1859 (List.nil : V1)=b1859 := by rfl
theorem e1484 : o1.add b1935 b1865=b1582 := by decide
theorem e1485 : o1.add (List.nil : V1) b1860=b1860 := by rfl
theorem e1486 : o1.add b1936 b1866=b1861 := by decide
theorem e1487 : o1.add b1937 b1867=b1862 := by decide
theorem e1488 : o1.add b1938 b1868=b1863 := by decide
theorem e1489 : o1.add b1939 b1869=b1587 := by decide
theorem e1490 : o2.add (List.nil : V2) b1934=b1934 := by rfl
theorem e1491 : o2.add b1948 b1933=b1957 := @add_cons V1 _ o1 b1939 b1869 b1587 (List.nil : V2) b1934 b1934 b1957 e1489 e1490 (by rfl)
theorem e1492 : o2.add b1947 b1932=b1956 := @add_cons V1 _ o1 b1938 b1868 b1863 b1948 b1933 b1957 b1956 e1488 e1491 (by rfl)
theorem e1493 : o2.add b1946 b1931=b1955 := @add_cons V1 _ o1 b1937 b1867 b1862 b1947 b1932 b1956 b1955 e1487 e1492 (by rfl)
theorem e1494 : o2.add b1945 b1930=b1954 := @add_cons V1 _ o1 b1936 b1866 b1861 b1946 b1931 b1955 b1954 e1486 e1493 (by rfl)
theorem e1495 : o2.add b1944 b1929=b1953 := @add_cons V1 _ o1 (List.nil : V1) b1860 b1860 b1945 b1930 b1954 b1953 e1485 e1494 (by rfl)
theorem e1496 : o2.add b1943 b1928=b1952 := @add_cons V1 _ o1 b1935 b1865 b1582 b1944 b1929 b1953 b1952 e1484 e1495 (by rfl)
theorem e1497 : o2.add b1942 b1927=b1951 := @add_cons V1 _ o1 b1859 (List.nil : V1) b1859 b1943 b1928 b1952 b1951 e1483 e1496 (by rfl)
theorem e1498 : o2.add b1941 b1870=b1950 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1942 b1927 b1951 b1950 e34 e1497 (by rfl)
theorem e1499 : o2.add b1940 b1949=b1864 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1941 b1870 b1950 b1864 e34 e1498 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
