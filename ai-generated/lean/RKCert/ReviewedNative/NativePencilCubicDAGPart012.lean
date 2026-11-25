module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart011

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1650 : o2.add b2073 b2057=b2083 := @add_cons V1 _ o1 b2064 b1989 b1594 b2074 b2058 b2084 b2083 e1640 e1649 (by rfl)
theorem e1651 : o2.add b2072 b2056=b2082 := @add_cons V1 _ o1 b2063 b1988 b1983 b2073 b2057 b2083 b2082 e1639 e1650 (by rfl)
theorem e1652 : o2.add b2071 b2055=b2081 := @add_cons V1 _ o1 b1982 (List.nil : V1) b1982 b2072 b2056 b2082 b2081 e1638 e1651 (by rfl)
theorem e1653 : o2.add b2070 b2054=b2080 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2071 b2055 b2081 b2080 e34 e1652 (by rfl)
theorem e1654 : o2.add b2069 b1993=b2079 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2070 b2054 b2080 b2079 e34 e1653 (by rfl)
theorem e1655 : o2.add b2068 b2078=b1987 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2069 b1993 b2079 b1987 e34 e1654 (by rfl)
theorem e1656 : o2.mul b1636 b41=b1987 := @mul_cons V1 _ o1 b78 b1643 b41 b1993 b2068 b2078 b1987 e1621 e1637 (by rfl) e1655
theorem e1657 : o1.mul b77 b35=b1591 := by decide
theorem e1658 : o1.mul b77 b36=b2088 := by decide
theorem e1659 : o1.mul b77 b37=b2089 := by decide
theorem e1660 : o1.mul b77 b38=b2090 := by decide
theorem e1661 : o1.mul b77 b39=b2091 := by decide
theorem e1662 : o1.mul b77 b40=b2092 := by decide
theorem e1663 : o1.scale b77 b998=b2102 := @scale_cons V1 _ o1 b77 b40 b2092 (List.nil : V2) (List.nil : V2) b2102 e1662 e1222 (by rfl)
theorem e1664 : o1.scale b77 b996=b2101 := @scale_cons V1 _ o1 b77 b39 b2091 b998 b2102 b2101 e1661 e1663 (by rfl)
theorem e1665 : o1.scale b77 b994=b2100 := @scale_cons V1 _ o1 b77 b38 b2090 b996 b2101 b2100 e1660 e1664 (by rfl)
theorem e1666 : o1.scale b77 b992=b2099 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b994 b2100 b2099 e1215 e1665 (by rfl)
theorem e1667 : o1.scale b77 b990=b2098 := @scale_cons V1 _ o1 b77 b37 b2089 b992 b2099 b2098 e1659 e1666 (by rfl)
theorem e1668 : o1.scale b77 b988=b2097 := @scale_cons V1 _ o1 b77 b36 b2088 b990 b2098 b2097 e1658 e1667 (by rfl)
theorem e1669 : o1.scale b77 b986=b2096 := @scale_cons V1 _ o1 b77 b35 b1591 b988 b2097 b2096 e1657 e1668 (by rfl)
theorem e1670 : o1.scale b77 b984=b2095 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b986 b2096 b2095 e1215 e1669 (by rfl)
theorem e1671 : o1.scale b77 b982=b2094 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b984 b2095 b2094 e1215 e1670 (by rfl)
theorem e1672 : o1.scale b77 b41=b2093 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b982 b2094 b2093 e1215 e1671 (by rfl)
theorem e1673 : o1.add b1591 (List.nil : V1)=b1591 := by rfl
theorem e1674 : o1.add b2088 b1982=b1592 := by decide
theorem e1675 : o1.add b2089 b1983=b1593 := by decide
theorem e1676 : o1.add (List.nil : V1) b1594=b1594 := by rfl
theorem e1677 : o1.add b2090 b1984=b1595 := by decide
theorem e1678 : o1.add b2091 b1985=b1596 := by decide
theorem e1679 : o1.add b2092 b1986=b1597 := by decide
theorem e1680 : o2.add (List.nil : V2) b2087=b2087 := by rfl
theorem e1681 : o2.add b2102 b2086=b2112 := @add_cons V1 _ o1 b2092 b1986 b1597 (List.nil : V2) b2087 b2087 b2112 e1679 e1680 (by rfl)
theorem e1682 : o2.add b2101 b2085=b2111 := @add_cons V1 _ o1 b2091 b1985 b1596 b2102 b2086 b2112 b2111 e1678 e1681 (by rfl)
theorem e1683 : o2.add b2100 b2084=b2110 := @add_cons V1 _ o1 b2090 b1984 b1595 b2101 b2085 b2111 b2110 e1677 e1682 (by rfl)
theorem e1684 : o2.add b2099 b2083=b2109 := @add_cons V1 _ o1 (List.nil : V1) b1594 b1594 b2100 b2084 b2110 b2109 e1676 e1683 (by rfl)
theorem e1685 : o2.add b2098 b2082=b2108 := @add_cons V1 _ o1 b2089 b1983 b1593 b2099 b2083 b2109 b2108 e1675 e1684 (by rfl)
theorem e1686 : o2.add b2097 b2081=b2107 := @add_cons V1 _ o1 b2088 b1982 b1592 b2098 b2082 b2108 b2107 e1674 e1685 (by rfl)
theorem e1687 : o2.add b2096 b2080=b2106 := @add_cons V1 _ o1 b1591 (List.nil : V1) b1591 b2097 b2081 b2107 b2106 e1673 e1686 (by rfl)
theorem e1688 : o2.add b2095 b2079=b2105 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2096 b2080 b2106 b2105 e34 e1687 (by rfl)
theorem e1689 : o2.add b2094 b1987=b2104 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2095 b2079 b2105 b2104 e34 e1688 (by rfl)
theorem e1690 : o2.add b2093 b2103=b1601 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2094 b1987 b2104 b1601 e34 e1689 (by rfl)
theorem e1691 : o2.mul b82 b41=b1601 := @mul_cons V1 _ o1 b77 b1636 b41 b1987 b2093 b2103 b1601 e1656 e1672 (by rfl) e1690
theorem e1692 : o1.mul b81 b42=b2129 := by decide
theorem e1693 : o1.mul b81 b43=b2130 := by decide
theorem e1694 : o1.mul b81 b44=b2126 := by decide
theorem e1695 : o1.mul b81 b45=b2131 := by decide
theorem e1696 : o1.mul b81 b46=b507 := by decide
theorem e1697 : o1.scale b81 b1138=b2142 := @scale_cons V1 _ o1 b81 b46 b507 (List.nil : V2) (List.nil : V2) b2142 e1696 e1115 (by rfl)
theorem e1698 : o1.scale b81 b1136=b2141 := @scale_cons V1 _ o1 b81 b45 b2131 b1138 b2142 b2141 e1695 e1697 (by rfl)
theorem e1699 : o1.scale b81 b1134=b2140 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1136 b2141 b2140 e1108 e1698 (by rfl)
theorem e1700 : o1.scale b81 b1132=b2139 := @scale_cons V1 _ o1 b81 b44 b2126 b1134 b2140 b2139 e1694 e1699 (by rfl)
theorem e1701 : o1.scale b81 b1130=b2138 := @scale_cons V1 _ o1 b81 b43 b2130 b1132 b2139 b2138 e1693 e1700 (by rfl)
theorem e1702 : o1.scale b81 b1128=b2137 := @scale_cons V1 _ o1 b81 b42 b2129 b1130 b2138 b2137 e1692 e1701 (by rfl)
theorem e1703 : o1.scale b81 b1126=b2136 := @scale_cons V1 _ o1 b81 b18 b1662 b1128 b2137 b2136 e1113 e1702 (by rfl)
theorem e1704 : o1.scale b81 b1124=b2135 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1126 b2136 b2135 e1108 e1703 (by rfl)
theorem e1705 : o1.scale b81 b1122=b2134 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1124 b2135 b2134 e1108 e1704 (by rfl)
theorem e1706 : o1.scale b81 b1120=b2133 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1122 b2134 b2133 e1108 e1705 (by rfl)
theorem e1707 : o1.scale b81 b47=b2132 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1120 b2133 b2132 e1108 e1706 (by rfl)
theorem e1708 : o2.add b2132 (List.nil : V2)=b2132 := by rfl
theorem e1709 : o2.mul b1657 b47=b2132 := @mul_cons V1 _ o1 b81 (List.nil : V2) b47 (List.nil : V2) b2132 (List.nil : V2) b2132 e590 e1707 (by rfl) e1708
theorem e1710 : o1.mul b80 b42=b2143 := by decide
theorem e1711 : o1.mul b80 b43=b2144 := by decide
theorem e1712 : o1.mul b80 b44=b2145 := by decide
theorem e1713 : o1.mul b80 b45=b2127 := by decide
theorem e1714 : o1.mul b80 b46=b2146 := by decide
theorem e1715 : o1.scale b80 b1138=b2157 := @scale_cons V1 _ o1 b80 b46 b2146 (List.nil : V2) (List.nil : V2) b2157 e1714 e1132 (by rfl)
theorem e1716 : o1.scale b80 b1136=b2156 := @scale_cons V1 _ o1 b80 b45 b2127 b1138 b2157 b2156 e1713 e1715 (by rfl)
theorem e1717 : o1.scale b80 b1134=b2155 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1136 b2156 b2155 e1125 e1716 (by rfl)
theorem e1718 : o1.scale b80 b1132=b2154 := @scale_cons V1 _ o1 b80 b44 b2145 b1134 b2155 b2154 e1712 e1717 (by rfl)
theorem e1719 : o1.scale b80 b1130=b2153 := @scale_cons V1 _ o1 b80 b43 b2144 b1132 b2154 b2153 e1711 e1718 (by rfl)
theorem e1720 : o1.scale b80 b1128=b2152 := @scale_cons V1 _ o1 b80 b42 b2143 b1130 b2153 b2152 e1710 e1719 (by rfl)
theorem e1721 : o1.scale b80 b1126=b2151 := @scale_cons V1 _ o1 b80 b18 b1673 b1128 b2152 b2151 e1130 e1720 (by rfl)
theorem e1722 : o1.scale b80 b1124=b2150 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1126 b2151 b2150 e1125 e1721 (by rfl)
theorem e1723 : o1.scale b80 b1122=b2149 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1124 b2150 b2149 e1125 e1722 (by rfl)
theorem e1724 : o1.scale b80 b1120=b2148 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1122 b2149 b2148 e1125 e1723 (by rfl)
theorem e1725 : o1.scale b80 b47=b2147 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1120 b2148 b2147 e1125 e1724 (by rfl)
theorem e1726 : o1.add b1673 (List.nil : V1)=b1673 := by rfl
theorem e1727 : o1.add b2143 b1662=b2124 := by decide
theorem e1728 : o1.add b2144 b2129=b2125 := by decide
theorem e1729 : o1.add b2145 b2130=b2121 := by decide
theorem e1730 : o1.add (List.nil : V1) b2126=b2126 := by rfl
theorem e1731 : o1.add b2127 (List.nil : V1)=b2127 := by rfl
theorem e1732 : o1.add b2146 b2131=b1611 := by decide
theorem e1733 : o2.add (List.nil : V2) b2142=b2142 := by rfl
theorem e1734 : o2.add b2157 b2141=b2168 := @add_cons V1 _ o1 b2146 b2131 b1611 (List.nil : V2) b2142 b2142 b2168 e1732 e1733 (by rfl)
theorem e1735 : o2.add b2156 b2140=b2167 := @add_cons V1 _ o1 b2127 (List.nil : V1) b2127 b2157 b2141 b2168 b2167 e1731 e1734 (by rfl)
theorem e1736 : o2.add b2155 b2139=b2166 := @add_cons V1 _ o1 (List.nil : V1) b2126 b2126 b2156 b2140 b2167 b2166 e1730 e1735 (by rfl)
theorem e1737 : o2.add b2154 b2138=b2165 := @add_cons V1 _ o1 b2145 b2130 b2121 b2155 b2139 b2166 b2165 e1729 e1736 (by rfl)
theorem e1738 : o2.add b2153 b2137=b2164 := @add_cons V1 _ o1 b2144 b2129 b2125 b2154 b2138 b2165 b2164 e1728 e1737 (by rfl)
theorem e1739 : o2.add b2152 b2136=b2163 := @add_cons V1 _ o1 b2143 b1662 b2124 b2153 b2137 b2164 b2163 e1727 e1738 (by rfl)
theorem e1740 : o2.add b2151 b2135=b2162 := @add_cons V1 _ o1 b1673 (List.nil : V1) b1673 b2152 b2136 b2163 b2162 e1726 e1739 (by rfl)
theorem e1741 : o2.add b2150 b2134=b2161 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2151 b2135 b2162 b2161 e34 e1740 (by rfl)
theorem e1742 : o2.add b2149 b2133=b2160 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2150 b2134 b2161 b2160 e34 e1741 (by rfl)
theorem e1743 : o2.add b2148 b2132=b2159 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2149 b2133 b2160 b2159 e34 e1742 (by rfl)
theorem e1744 : o2.add b2147 b2158=b2128 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2148 b2132 b2159 b2128 e34 e1743 (by rfl)
theorem e1745 : o2.mul b1650 b47=b2128 := @mul_cons V1 _ o1 b80 b1657 b47 b2132 b2147 b2158 b2128 e1709 e1725 (by rfl) e1744
theorem e1746 : o1.mul b79 b42=b2169 := by decide
theorem e1747 : o1.mul b79 b43=b2170 := by decide
theorem e1748 : o1.mul b79 b44=b2171 := by decide
theorem e1749 : o1.mul b79 b45=b2172 := by decide
theorem e1750 : o1.mul b79 b46=b2173 := by decide
theorem e1751 : o1.scale b79 b1138=b2184 := @scale_cons V1 _ o1 b79 b46 b2173 (List.nil : V2) (List.nil : V2) b2184 e1750 e1162 (by rfl)
theorem e1752 : o1.scale b79 b1136=b2183 := @scale_cons V1 _ o1 b79 b45 b2172 b1138 b2184 b2183 e1749 e1751 (by rfl)
theorem e1753 : o1.scale b79 b1134=b2182 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1136 b2183 b2182 e1155 e1752 (by rfl)
theorem e1754 : o1.scale b79 b1132=b2181 := @scale_cons V1 _ o1 b79 b44 b2171 b1134 b2182 b2181 e1748 e1753 (by rfl)
theorem e1755 : o1.scale b79 b1130=b2180 := @scale_cons V1 _ o1 b79 b43 b2170 b1132 b2181 b2180 e1747 e1754 (by rfl)
theorem e1756 : o1.scale b79 b1128=b2179 := @scale_cons V1 _ o1 b79 b42 b2169 b1130 b2180 b2179 e1746 e1755 (by rfl)
theorem e1757 : o1.scale b79 b1126=b2178 := @scale_cons V1 _ o1 b79 b18 b1692 b1128 b2179 b2178 e1160 e1756 (by rfl)
theorem e1758 : o1.scale b79 b1124=b2177 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1126 b2178 b2177 e1155 e1757 (by rfl)
theorem e1759 : o1.scale b79 b1122=b2176 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1124 b2177 b2176 e1155 e1758 (by rfl)
theorem e1760 : o1.scale b79 b1120=b2175 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1122 b2176 b2175 e1155 e1759 (by rfl)
theorem e1761 : o1.scale b79 b47=b2174 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1120 b2175 b2174 e1155 e1760 (by rfl)
theorem e1762 : o1.add b1692 (List.nil : V1)=b1692 := by rfl
theorem e1763 : o1.add b2169 b1673=b2119 := by decide
theorem e1764 : o1.add b2170 b2124=b2120 := by decide
theorem e1765 : o1.add b2171 b2125=b2116 := by decide
theorem e1766 : o1.add (List.nil : V1) b2121=b2121 := by rfl
theorem e1767 : o1.add b2172 b2126=b2122 := by decide
theorem e1768 : o1.add b2173 b2127=b1610 := by decide
theorem e1769 : o2.add (List.nil : V2) b2168=b2168 := by rfl
theorem e1770 : o2.add b2184 b2167=b2195 := @add_cons V1 _ o1 b2173 b2127 b1610 (List.nil : V2) b2168 b2168 b2195 e1768 e1769 (by rfl)
theorem e1771 : o2.add b2183 b2166=b2194 := @add_cons V1 _ o1 b2172 b2126 b2122 b2184 b2167 b2195 b2194 e1767 e1770 (by rfl)
theorem e1772 : o2.add b2182 b2165=b2193 := @add_cons V1 _ o1 (List.nil : V1) b2121 b2121 b2183 b2166 b2194 b2193 e1766 e1771 (by rfl)
theorem e1773 : o2.add b2181 b2164=b2192 := @add_cons V1 _ o1 b2171 b2125 b2116 b2182 b2165 b2193 b2192 e1765 e1772 (by rfl)
theorem e1774 : o2.add b2180 b2163=b2191 := @add_cons V1 _ o1 b2170 b2124 b2120 b2181 b2164 b2192 b2191 e1764 e1773 (by rfl)
theorem e1775 : o2.add b2179 b2162=b2190 := @add_cons V1 _ o1 b2169 b1673 b2119 b2180 b2163 b2191 b2190 e1763 e1774 (by rfl)
theorem e1776 : o2.add b2178 b2161=b2189 := @add_cons V1 _ o1 b1692 (List.nil : V1) b1692 b2179 b2162 b2190 b2189 e1762 e1775 (by rfl)
theorem e1777 : o2.add b2177 b2160=b2188 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2178 b2161 b2189 b2188 e34 e1776 (by rfl)
theorem e1778 : o2.add b2176 b2159=b2187 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2177 b2160 b2188 b2187 e34 e1777 (by rfl)
theorem e1779 : o2.add b2175 b2128=b2186 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2176 b2159 b2187 b2186 e34 e1778 (by rfl)
theorem e1780 : o2.add b2174 b2185=b2123 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2175 b2128 b2186 b2123 e34 e1779 (by rfl)
theorem e1781 : o2.mul b1643 b47=b2123 := @mul_cons V1 _ o1 b79 b1650 b47 b2128 b2174 b2185 b2123 e1745 e1761 (by rfl) e1780
theorem e1782 : o1.mul b78 b42=b2196 := by decide
theorem e1783 : o1.mul b78 b43=b2197 := by decide
theorem e1784 : o1.mul b78 b44=b2198 := by decide
theorem e1785 : o1.mul b78 b45=b2199 := by decide
theorem e1786 : o1.mul b78 b46=b2200 := by decide
theorem e1787 : o1.scale b78 b1138=b2211 := @scale_cons V1 _ o1 b78 b46 b2200 (List.nil : V2) (List.nil : V2) b2211 e1786 e1192 (by rfl)
theorem e1788 : o1.scale b78 b1136=b2210 := @scale_cons V1 _ o1 b78 b45 b2199 b1138 b2211 b2210 e1785 e1787 (by rfl)
theorem e1789 : o1.scale b78 b1134=b2209 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1136 b2210 b2209 e1185 e1788 (by rfl)
theorem e1790 : o1.scale b78 b1132=b2208 := @scale_cons V1 _ o1 b78 b44 b2198 b1134 b2209 b2208 e1784 e1789 (by rfl)
theorem e1791 : o1.scale b78 b1130=b2207 := @scale_cons V1 _ o1 b78 b43 b2197 b1132 b2208 b2207 e1783 e1790 (by rfl)
theorem e1792 : o1.scale b78 b1128=b2206 := @scale_cons V1 _ o1 b78 b42 b2196 b1130 b2207 b2206 e1782 e1791 (by rfl)
theorem e1793 : o1.scale b78 b1126=b2205 := @scale_cons V1 _ o1 b78 b18 b1711 b1128 b2206 b2205 e1190 e1792 (by rfl)
theorem e1794 : o1.scale b78 b1124=b2204 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1126 b2205 b2204 e1185 e1793 (by rfl)
theorem e1795 : o1.scale b78 b1122=b2203 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1124 b2204 b2203 e1185 e1794 (by rfl)
theorem e1796 : o1.scale b78 b1120=b2202 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1122 b2203 b2202 e1185 e1795 (by rfl)
theorem e1797 : o1.scale b78 b47=b2201 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1120 b2202 b2201 e1185 e1796 (by rfl)
theorem e1798 : o1.add b1711 (List.nil : V1)=b1711 := by rfl
theorem e1799 : o1.add b2196 b1692=b2114 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
