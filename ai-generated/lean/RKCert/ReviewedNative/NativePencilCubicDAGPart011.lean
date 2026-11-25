module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart010

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1500 : o2.mul b1636 b34=b1864 := @mul_cons V1 _ o1 b78 b1643 b34 b1870 b1940 b1949 b1864 e1467 e1482 (by rfl) e1499
theorem e1501 : o1.mul b77 b28=b1580 := by decide
theorem e1502 : o1.mul b77 b29=b1958 := by decide
theorem e1503 : o1.mul b77 b30=b1959 := by decide
theorem e1504 : o1.mul b77 b31=b1960 := by decide
theorem e1505 : o1.mul b77 b32=b1961 := by decide
theorem e1506 : o1.mul b77 b33=b1962 := by decide
theorem e1507 : o1.scale b77 b864=b1971 := @scale_cons V1 _ o1 b77 b33 b1962 (List.nil : V2) (List.nil : V2) b1971 e1506 e1222 (by rfl)
theorem e1508 : o1.scale b77 b862=b1970 := @scale_cons V1 _ o1 b77 b32 b1961 b864 b1971 b1970 e1505 e1507 (by rfl)
theorem e1509 : o1.scale b77 b860=b1969 := @scale_cons V1 _ o1 b77 b31 b1960 b862 b1970 b1969 e1504 e1508 (by rfl)
theorem e1510 : o1.scale b77 b858=b1968 := @scale_cons V1 _ o1 b77 b30 b1959 b860 b1969 b1968 e1503 e1509 (by rfl)
theorem e1511 : o1.scale b77 b856=b1967 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b858 b1968 b1967 e1215 e1510 (by rfl)
theorem e1512 : o1.scale b77 b854=b1966 := @scale_cons V1 _ o1 b77 b29 b1958 b856 b1967 b1966 e1502 e1511 (by rfl)
theorem e1513 : o1.scale b77 b852=b1965 := @scale_cons V1 _ o1 b77 b28 b1580 b854 b1966 b1965 e1501 e1512 (by rfl)
theorem e1514 : o1.scale b77 b850=b1964 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b852 b1965 b1964 e1215 e1513 (by rfl)
theorem e1515 : o1.scale b77 b34=b1963 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b850 b1964 b1963 e1215 e1514 (by rfl)
theorem e1516 : o1.add b1580 (List.nil : V1)=b1580 := by rfl
theorem e1517 : o1.add b1958 b1859=b1581 := by decide
theorem e1518 : o1.add (List.nil : V1) b1582=b1582 := by rfl
theorem e1519 : o1.add b1959 b1860=b1583 := by decide
theorem e1520 : o1.add b1960 b1861=b1584 := by decide
theorem e1521 : o1.add b1961 b1862=b1585 := by decide
theorem e1522 : o1.add b1962 b1863=b1586 := by decide
theorem e1523 : o2.add (List.nil : V2) b1957=b1957 := by rfl
theorem e1524 : o2.add b1971 b1956=b1980 := @add_cons V1 _ o1 b1962 b1863 b1586 (List.nil : V2) b1957 b1957 b1980 e1522 e1523 (by rfl)
theorem e1525 : o2.add b1970 b1955=b1979 := @add_cons V1 _ o1 b1961 b1862 b1585 b1971 b1956 b1980 b1979 e1521 e1524 (by rfl)
theorem e1526 : o2.add b1969 b1954=b1978 := @add_cons V1 _ o1 b1960 b1861 b1584 b1970 b1955 b1979 b1978 e1520 e1525 (by rfl)
theorem e1527 : o2.add b1968 b1953=b1977 := @add_cons V1 _ o1 b1959 b1860 b1583 b1969 b1954 b1978 b1977 e1519 e1526 (by rfl)
theorem e1528 : o2.add b1967 b1952=b1976 := @add_cons V1 _ o1 (List.nil : V1) b1582 b1582 b1968 b1953 b1977 b1976 e1518 e1527 (by rfl)
theorem e1529 : o2.add b1966 b1951=b1975 := @add_cons V1 _ o1 b1958 b1859 b1581 b1967 b1952 b1976 b1975 e1517 e1528 (by rfl)
theorem e1530 : o2.add b1965 b1950=b1974 := @add_cons V1 _ o1 b1580 (List.nil : V1) b1580 b1966 b1951 b1975 b1974 e1516 e1529 (by rfl)
theorem e1531 : o2.add b1964 b1864=b1973 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1965 b1950 b1974 b1973 e34 e1530 (by rfl)
theorem e1532 : o2.add b1963 b1972=b1590 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1964 b1864 b1973 b1590 e34 e1531 (by rfl)
theorem e1533 : o2.mul b82 b34=b1590 := @mul_cons V1 _ o1 b77 b1636 b34 b1864 b1963 b1972 b1590 e1500 e1515 (by rfl) e1532
theorem e1534 : o1.mul b81 b35=b2000 := by decide
theorem e1535 : o1.mul b81 b36=b2001 := by decide
theorem e1536 : o1.mul b81 b37=b1996 := by decide
theorem e1537 : o1.mul b81 b38=b2002 := by decide
theorem e1538 : o1.mul b81 b39=b2003 := by decide
theorem e1539 : o1.mul b81 b40=b496 := by decide
theorem e1540 : o1.scale b81 b998=b2013 := @scale_cons V1 _ o1 b81 b40 b496 (List.nil : V2) (List.nil : V2) b2013 e1539 e1115 (by rfl)
theorem e1541 : o1.scale b81 b996=b2012 := @scale_cons V1 _ o1 b81 b39 b2003 b998 b2013 b2012 e1538 e1540 (by rfl)
theorem e1542 : o1.scale b81 b994=b2011 := @scale_cons V1 _ o1 b81 b38 b2002 b996 b2012 b2011 e1537 e1541 (by rfl)
theorem e1543 : o1.scale b81 b992=b2010 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b994 b2011 b2010 e1108 e1542 (by rfl)
theorem e1544 : o1.scale b81 b990=b2009 := @scale_cons V1 _ o1 b81 b37 b1996 b992 b2010 b2009 e1536 e1543 (by rfl)
theorem e1545 : o1.scale b81 b988=b2008 := @scale_cons V1 _ o1 b81 b36 b2001 b990 b2009 b2008 e1535 e1544 (by rfl)
theorem e1546 : o1.scale b81 b986=b2007 := @scale_cons V1 _ o1 b81 b35 b2000 b988 b2008 b2007 e1534 e1545 (by rfl)
theorem e1547 : o1.scale b81 b984=b2006 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b986 b2007 b2006 e1108 e1546 (by rfl)
theorem e1548 : o1.scale b81 b982=b2005 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b984 b2006 b2005 e1108 e1547 (by rfl)
theorem e1549 : o1.scale b81 b41=b2004 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b982 b2005 b2004 e1108 e1548 (by rfl)
theorem e1550 : o2.add b2004 (List.nil : V2)=b2004 := by rfl
theorem e1551 : o2.mul b1657 b41=b2004 := @mul_cons V1 _ o1 b81 (List.nil : V2) b41 (List.nil : V2) b2004 (List.nil : V2) b2004 e431 e1549 (by rfl) e1550
theorem e1552 : o1.mul b80 b35=b1994 := by decide
theorem e1553 : o1.mul b80 b36=b2014 := by decide
theorem e1554 : o1.mul b80 b37=b2015 := by decide
theorem e1555 : o1.mul b80 b38=b1997 := by decide
theorem e1556 : o1.mul b80 b39=b2016 := by decide
theorem e1557 : o1.mul b80 b40=b2017 := by decide
theorem e1558 : o1.scale b80 b998=b2027 := @scale_cons V1 _ o1 b80 b40 b2017 (List.nil : V2) (List.nil : V2) b2027 e1557 e1132 (by rfl)
theorem e1559 : o1.scale b80 b996=b2026 := @scale_cons V1 _ o1 b80 b39 b2016 b998 b2027 b2026 e1556 e1558 (by rfl)
theorem e1560 : o1.scale b80 b994=b2025 := @scale_cons V1 _ o1 b80 b38 b1997 b996 b2026 b2025 e1555 e1559 (by rfl)
theorem e1561 : o1.scale b80 b992=b2024 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b994 b2025 b2024 e1125 e1560 (by rfl)
theorem e1562 : o1.scale b80 b990=b2023 := @scale_cons V1 _ o1 b80 b37 b2015 b992 b2024 b2023 e1554 e1561 (by rfl)
theorem e1563 : o1.scale b80 b988=b2022 := @scale_cons V1 _ o1 b80 b36 b2014 b990 b2023 b2022 e1553 e1562 (by rfl)
theorem e1564 : o1.scale b80 b986=b2021 := @scale_cons V1 _ o1 b80 b35 b1994 b988 b2022 b2021 e1552 e1563 (by rfl)
theorem e1565 : o1.scale b80 b984=b2020 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b986 b2021 b2020 e1125 e1564 (by rfl)
theorem e1566 : o1.scale b80 b982=b2019 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b984 b2020 b2019 e1125 e1565 (by rfl)
theorem e1567 : o1.scale b80 b41=b2018 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b982 b2019 b2018 e1125 e1566 (by rfl)
theorem e1568 : o1.add b1994 (List.nil : V1)=b1994 := by rfl
theorem e1569 : o1.add b2014 b2000=b1995 := by decide
theorem e1570 : o1.add b2015 b2001=b1990 := by decide
theorem e1571 : o1.add (List.nil : V1) b1996=b1996 := by rfl
theorem e1572 : o1.add b1997 (List.nil : V1)=b1997 := by rfl
theorem e1573 : o1.add b2016 b2002=b1998 := by decide
theorem e1574 : o1.add b2017 b2003=b1600 := by decide
theorem e1575 : o2.add (List.nil : V2) b2013=b2013 := by rfl
theorem e1576 : o2.add b2027 b2012=b2037 := @add_cons V1 _ o1 b2017 b2003 b1600 (List.nil : V2) b2013 b2013 b2037 e1574 e1575 (by rfl)
theorem e1577 : o2.add b2026 b2011=b2036 := @add_cons V1 _ o1 b2016 b2002 b1998 b2027 b2012 b2037 b2036 e1573 e1576 (by rfl)
theorem e1578 : o2.add b2025 b2010=b2035 := @add_cons V1 _ o1 b1997 (List.nil : V1) b1997 b2026 b2011 b2036 b2035 e1572 e1577 (by rfl)
theorem e1579 : o2.add b2024 b2009=b2034 := @add_cons V1 _ o1 (List.nil : V1) b1996 b1996 b2025 b2010 b2035 b2034 e1571 e1578 (by rfl)
theorem e1580 : o2.add b2023 b2008=b2033 := @add_cons V1 _ o1 b2015 b2001 b1990 b2024 b2009 b2034 b2033 e1570 e1579 (by rfl)
theorem e1581 : o2.add b2022 b2007=b2032 := @add_cons V1 _ o1 b2014 b2000 b1995 b2023 b2008 b2033 b2032 e1569 e1580 (by rfl)
theorem e1582 : o2.add b2021 b2006=b2031 := @add_cons V1 _ o1 b1994 (List.nil : V1) b1994 b2022 b2007 b2032 b2031 e1568 e1581 (by rfl)
theorem e1583 : o2.add b2020 b2005=b2030 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2021 b2006 b2031 b2030 e34 e1582 (by rfl)
theorem e1584 : o2.add b2019 b2004=b2029 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2020 b2005 b2030 b2029 e34 e1583 (by rfl)
theorem e1585 : o2.add b2018 b2028=b1999 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2019 b2004 b2029 b1999 e34 e1584 (by rfl)
theorem e1586 : o2.mul b1650 b41=b1999 := @mul_cons V1 _ o1 b80 b1657 b41 b2004 b2018 b2028 b1999 e1551 e1567 (by rfl) e1585
theorem e1587 : o1.mul b79 b35=b1988 := by decide
theorem e1588 : o1.mul b79 b36=b2038 := by decide
theorem e1589 : o1.mul b79 b37=b2039 := by decide
theorem e1590 : o1.mul b79 b38=b2040 := by decide
theorem e1591 : o1.mul b79 b39=b2041 := by decide
theorem e1592 : o1.mul b79 b40=b2042 := by decide
theorem e1593 : o1.scale b79 b998=b2052 := @scale_cons V1 _ o1 b79 b40 b2042 (List.nil : V2) (List.nil : V2) b2052 e1592 e1162 (by rfl)
theorem e1594 : o1.scale b79 b996=b2051 := @scale_cons V1 _ o1 b79 b39 b2041 b998 b2052 b2051 e1591 e1593 (by rfl)
theorem e1595 : o1.scale b79 b994=b2050 := @scale_cons V1 _ o1 b79 b38 b2040 b996 b2051 b2050 e1590 e1594 (by rfl)
theorem e1596 : o1.scale b79 b992=b2049 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b994 b2050 b2049 e1155 e1595 (by rfl)
theorem e1597 : o1.scale b79 b990=b2048 := @scale_cons V1 _ o1 b79 b37 b2039 b992 b2049 b2048 e1589 e1596 (by rfl)
theorem e1598 : o1.scale b79 b988=b2047 := @scale_cons V1 _ o1 b79 b36 b2038 b990 b2048 b2047 e1588 e1597 (by rfl)
theorem e1599 : o1.scale b79 b986=b2046 := @scale_cons V1 _ o1 b79 b35 b1988 b988 b2047 b2046 e1587 e1598 (by rfl)
theorem e1600 : o1.scale b79 b984=b2045 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b986 b2046 b2045 e1155 e1599 (by rfl)
theorem e1601 : o1.scale b79 b982=b2044 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b984 b2045 b2044 e1155 e1600 (by rfl)
theorem e1602 : o1.scale b79 b41=b2043 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b982 b2044 b2043 e1155 e1601 (by rfl)
theorem e1603 : o1.add b1988 (List.nil : V1)=b1988 := by rfl
theorem e1604 : o1.add b2038 b1994=b1989 := by decide
theorem e1605 : o1.add b2039 b1995=b1984 := by decide
theorem e1606 : o1.add (List.nil : V1) b1990=b1990 := by rfl
theorem e1607 : o1.add b2040 b1996=b1991 := by decide
theorem e1608 : o1.add b2041 b1997=b1992 := by decide
theorem e1609 : o1.add b2042 b1998=b1599 := by decide
theorem e1610 : o2.add (List.nil : V2) b2037=b2037 := by rfl
theorem e1611 : o2.add b2052 b2036=b2062 := @add_cons V1 _ o1 b2042 b1998 b1599 (List.nil : V2) b2037 b2037 b2062 e1609 e1610 (by rfl)
theorem e1612 : o2.add b2051 b2035=b2061 := @add_cons V1 _ o1 b2041 b1997 b1992 b2052 b2036 b2062 b2061 e1608 e1611 (by rfl)
theorem e1613 : o2.add b2050 b2034=b2060 := @add_cons V1 _ o1 b2040 b1996 b1991 b2051 b2035 b2061 b2060 e1607 e1612 (by rfl)
theorem e1614 : o2.add b2049 b2033=b2059 := @add_cons V1 _ o1 (List.nil : V1) b1990 b1990 b2050 b2034 b2060 b2059 e1606 e1613 (by rfl)
theorem e1615 : o2.add b2048 b2032=b2058 := @add_cons V1 _ o1 b2039 b1995 b1984 b2049 b2033 b2059 b2058 e1605 e1614 (by rfl)
theorem e1616 : o2.add b2047 b2031=b2057 := @add_cons V1 _ o1 b2038 b1994 b1989 b2048 b2032 b2058 b2057 e1604 e1615 (by rfl)
theorem e1617 : o2.add b2046 b2030=b2056 := @add_cons V1 _ o1 b1988 (List.nil : V1) b1988 b2047 b2031 b2057 b2056 e1603 e1616 (by rfl)
theorem e1618 : o2.add b2045 b2029=b2055 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2046 b2030 b2056 b2055 e34 e1617 (by rfl)
theorem e1619 : o2.add b2044 b1999=b2054 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2045 b2029 b2055 b2054 e34 e1618 (by rfl)
theorem e1620 : o2.add b2043 b2053=b1993 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2044 b1999 b2054 b1993 e34 e1619 (by rfl)
theorem e1621 : o2.mul b1643 b41=b1993 := @mul_cons V1 _ o1 b79 b1650 b41 b1999 b2043 b2053 b1993 e1586 e1602 (by rfl) e1620
theorem e1622 : o1.mul b78 b35=b1982 := by decide
theorem e1623 : o1.mul b78 b36=b2063 := by decide
theorem e1624 : o1.mul b78 b37=b2064 := by decide
theorem e1625 : o1.mul b78 b38=b2065 := by decide
theorem e1626 : o1.mul b78 b39=b2066 := by decide
theorem e1627 : o1.mul b78 b40=b2067 := by decide
theorem e1628 : o1.scale b78 b998=b2077 := @scale_cons V1 _ o1 b78 b40 b2067 (List.nil : V2) (List.nil : V2) b2077 e1627 e1192 (by rfl)
theorem e1629 : o1.scale b78 b996=b2076 := @scale_cons V1 _ o1 b78 b39 b2066 b998 b2077 b2076 e1626 e1628 (by rfl)
theorem e1630 : o1.scale b78 b994=b2075 := @scale_cons V1 _ o1 b78 b38 b2065 b996 b2076 b2075 e1625 e1629 (by rfl)
theorem e1631 : o1.scale b78 b992=b2074 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b994 b2075 b2074 e1185 e1630 (by rfl)
theorem e1632 : o1.scale b78 b990=b2073 := @scale_cons V1 _ o1 b78 b37 b2064 b992 b2074 b2073 e1624 e1631 (by rfl)
theorem e1633 : o1.scale b78 b988=b2072 := @scale_cons V1 _ o1 b78 b36 b2063 b990 b2073 b2072 e1623 e1632 (by rfl)
theorem e1634 : o1.scale b78 b986=b2071 := @scale_cons V1 _ o1 b78 b35 b1982 b988 b2072 b2071 e1622 e1633 (by rfl)
theorem e1635 : o1.scale b78 b984=b2070 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b986 b2071 b2070 e1185 e1634 (by rfl)
theorem e1636 : o1.scale b78 b982=b2069 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b984 b2070 b2069 e1185 e1635 (by rfl)
theorem e1637 : o1.scale b78 b41=b2068 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b982 b2069 b2068 e1185 e1636 (by rfl)
theorem e1638 : o1.add b1982 (List.nil : V1)=b1982 := by rfl
theorem e1639 : o1.add b2063 b1988=b1983 := by decide
theorem e1640 : o1.add b2064 b1989=b1594 := by decide
theorem e1641 : o1.add (List.nil : V1) b1984=b1984 := by rfl
theorem e1642 : o1.add b2065 b1990=b1985 := by decide
theorem e1643 : o1.add b2066 b1991=b1986 := by decide
theorem e1644 : o1.add b2067 b1992=b1598 := by decide
theorem e1645 : o2.add (List.nil : V2) b2062=b2062 := by rfl
theorem e1646 : o2.add b2077 b2061=b2087 := @add_cons V1 _ o1 b2067 b1992 b1598 (List.nil : V2) b2062 b2062 b2087 e1644 e1645 (by rfl)
theorem e1647 : o2.add b2076 b2060=b2086 := @add_cons V1 _ o1 b2066 b1991 b1986 b2077 b2061 b2087 b2086 e1643 e1646 (by rfl)
theorem e1648 : o2.add b2075 b2059=b2085 := @add_cons V1 _ o1 b2065 b1990 b1985 b2076 b2060 b2086 b2085 e1642 e1647 (by rfl)
theorem e1649 : o2.add b2074 b2058=b2084 := @add_cons V1 _ o1 (List.nil : V1) b1984 b1984 b2075 b2059 b2085 b2084 e1641 e1648 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
