module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart012

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1800 : o1.add b2197 b2119=b2115 := by decide
theorem e1801 : o1.add b2198 b2120=b1606 := by decide
theorem e1802 : o1.add (List.nil : V1) b2116=b2116 := by rfl
theorem e1803 : o1.add b2199 b2121=b2117 := by decide
theorem e1804 : o1.add b2200 b2122=b1609 := by decide
theorem e1805 : o2.add (List.nil : V2) b2195=b2195 := by rfl
theorem e1806 : o2.add b2211 b2194=b2222 := @add_cons V1 _ o1 b2200 b2122 b1609 (List.nil : V2) b2195 b2195 b2222 e1804 e1805 (by rfl)
theorem e1807 : o2.add b2210 b2193=b2221 := @add_cons V1 _ o1 b2199 b2121 b2117 b2211 b2194 b2222 b2221 e1803 e1806 (by rfl)
theorem e1808 : o2.add b2209 b2192=b2220 := @add_cons V1 _ o1 (List.nil : V1) b2116 b2116 b2210 b2193 b2221 b2220 e1802 e1807 (by rfl)
theorem e1809 : o2.add b2208 b2191=b2219 := @add_cons V1 _ o1 b2198 b2120 b1606 b2209 b2192 b2220 b2219 e1801 e1808 (by rfl)
theorem e1810 : o2.add b2207 b2190=b2218 := @add_cons V1 _ o1 b2197 b2119 b2115 b2208 b2191 b2219 b2218 e1800 e1809 (by rfl)
theorem e1811 : o2.add b2206 b2189=b2217 := @add_cons V1 _ o1 b2196 b1692 b2114 b2207 b2190 b2218 b2217 e1799 e1810 (by rfl)
theorem e1812 : o2.add b2205 b2188=b2216 := @add_cons V1 _ o1 b1711 (List.nil : V1) b1711 b2206 b2189 b2217 b2216 e1798 e1811 (by rfl)
theorem e1813 : o2.add b2204 b2187=b2215 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2205 b2188 b2216 b2215 e34 e1812 (by rfl)
theorem e1814 : o2.add b2203 b2186=b2214 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2204 b2187 b2215 b2214 e34 e1813 (by rfl)
theorem e1815 : o2.add b2202 b2123=b2213 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2203 b2186 b2214 b2213 e34 e1814 (by rfl)
theorem e1816 : o2.add b2201 b2212=b2118 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2202 b2123 b2213 b2118 e34 e1815 (by rfl)
theorem e1817 : o2.mul b1636 b47=b2118 := @mul_cons V1 _ o1 b78 b1643 b47 b2123 b2201 b2212 b2118 e1781 e1797 (by rfl) e1816
theorem e1818 : o1.mul b77 b42=b2223 := by decide
theorem e1819 : o1.mul b77 b43=b2224 := by decide
theorem e1820 : o1.mul b77 b44=b2225 := by decide
theorem e1821 : o1.mul b77 b45=b2226 := by decide
theorem e1822 : o1.mul b77 b46=b2227 := by decide
theorem e1823 : o1.scale b77 b1138=b2238 := @scale_cons V1 _ o1 b77 b46 b2227 (List.nil : V2) (List.nil : V2) b2238 e1822 e1222 (by rfl)
theorem e1824 : o1.scale b77 b1136=b2237 := @scale_cons V1 _ o1 b77 b45 b2226 b1138 b2238 b2237 e1821 e1823 (by rfl)
theorem e1825 : o1.scale b77 b1134=b2236 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1136 b2237 b2236 e1215 e1824 (by rfl)
theorem e1826 : o1.scale b77 b1132=b2235 := @scale_cons V1 _ o1 b77 b44 b2225 b1134 b2236 b2235 e1820 e1825 (by rfl)
theorem e1827 : o1.scale b77 b1130=b2234 := @scale_cons V1 _ o1 b77 b43 b2224 b1132 b2235 b2234 e1819 e1826 (by rfl)
theorem e1828 : o1.scale b77 b1128=b2233 := @scale_cons V1 _ o1 b77 b42 b2223 b1130 b2234 b2233 e1818 e1827 (by rfl)
theorem e1829 : o1.scale b77 b1126=b2232 := @scale_cons V1 _ o1 b77 b18 b1602 b1128 b2233 b2232 e1220 e1828 (by rfl)
theorem e1830 : o1.scale b77 b1124=b2231 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1126 b2232 b2231 e1215 e1829 (by rfl)
theorem e1831 : o1.scale b77 b1122=b2230 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1124 b2231 b2230 e1215 e1830 (by rfl)
theorem e1832 : o1.scale b77 b1120=b2229 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1122 b2230 b2229 e1215 e1831 (by rfl)
theorem e1833 : o1.scale b77 b47=b2228 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1120 b2229 b2228 e1215 e1832 (by rfl)
theorem e1834 : o1.add b1602 (List.nil : V1)=b1602 := by rfl
theorem e1835 : o1.add b2223 b1711=b1603 := by decide
theorem e1836 : o1.add b2224 b2114=b1604 := by decide
theorem e1837 : o1.add b2225 b2115=b1605 := by decide
theorem e1838 : o1.add (List.nil : V1) b1606=b1606 := by rfl
theorem e1839 : o1.add b2226 b2116=b1607 := by decide
theorem e1840 : o1.add b2227 b2117=b1608 := by decide
theorem e1841 : o2.add (List.nil : V2) b2222=b2222 := by rfl
theorem e1842 : o2.add b2238 b2221=b2249 := @add_cons V1 _ o1 b2227 b2117 b1608 (List.nil : V2) b2222 b2222 b2249 e1840 e1841 (by rfl)
theorem e1843 : o2.add b2237 b2220=b2248 := @add_cons V1 _ o1 b2226 b2116 b1607 b2238 b2221 b2249 b2248 e1839 e1842 (by rfl)
theorem e1844 : o2.add b2236 b2219=b2247 := @add_cons V1 _ o1 (List.nil : V1) b1606 b1606 b2237 b2220 b2248 b2247 e1838 e1843 (by rfl)
theorem e1845 : o2.add b2235 b2218=b2246 := @add_cons V1 _ o1 b2225 b2115 b1605 b2236 b2219 b2247 b2246 e1837 e1844 (by rfl)
theorem e1846 : o2.add b2234 b2217=b2245 := @add_cons V1 _ o1 b2224 b2114 b1604 b2235 b2218 b2246 b2245 e1836 e1845 (by rfl)
theorem e1847 : o2.add b2233 b2216=b2244 := @add_cons V1 _ o1 b2223 b1711 b1603 b2234 b2217 b2245 b2244 e1835 e1846 (by rfl)
theorem e1848 : o2.add b2232 b2215=b2243 := @add_cons V1 _ o1 b1602 (List.nil : V1) b1602 b2233 b2216 b2244 b2243 e1834 e1847 (by rfl)
theorem e1849 : o2.add b2231 b2214=b2242 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2232 b2215 b2243 b2242 e34 e1848 (by rfl)
theorem e1850 : o2.add b2230 b2213=b2241 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2231 b2214 b2242 b2241 e34 e1849 (by rfl)
theorem e1851 : o2.add b2229 b2118=b2240 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2230 b2213 b2241 b2240 e34 e1850 (by rfl)
theorem e1852 : o2.add b2228 b2239=b1612 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2229 b2118 b2240 b1612 e34 e1851 (by rfl)
theorem e1853 : o2.mul b82 b47=b1612 := @mul_cons V1 _ o1 b77 b1636 b47 b2118 b2228 b2239 b1612 e1817 e1833 (by rfl) e1852
theorem e1854 : o1.mul b81 b48=b2266 := by decide
theorem e1855 : o1.mul b81 b49=b2267 := by decide
theorem e1856 : o1.mul b81 b50=b2268 := by decide
theorem e1857 : o1.mul b81 b51=b2264 := by decide
theorem e1858 : o1.mul b81 b52=b518 := by decide
theorem e1859 : o1.scale b81 b1288=b2280 := @scale_cons V1 _ o1 b81 b52 b518 (List.nil : V2) (List.nil : V2) b2280 e1858 e1115 (by rfl)
theorem e1860 : o1.scale b81 b1286=b2279 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1288 b2280 b2279 e1108 e1859 (by rfl)
theorem e1861 : o1.scale b81 b1284=b2278 := @scale_cons V1 _ o1 b81 b51 b2264 b1286 b2279 b2278 e1857 e1860 (by rfl)
theorem e1862 : o1.scale b81 b1282=b2277 := @scale_cons V1 _ o1 b81 b50 b2268 b1284 b2278 b2277 e1856 e1861 (by rfl)
theorem e1863 : o1.scale b81 b1280=b2276 := @scale_cons V1 _ o1 b81 b49 b2267 b1282 b2277 b2276 e1855 e1862 (by rfl)
theorem e1864 : o1.scale b81 b1278=b2275 := @scale_cons V1 _ o1 b81 b48 b2266 b1280 b2276 b2275 e1854 e1863 (by rfl)
theorem e1865 : o1.scale b81 b1276=b2274 := @scale_cons V1 _ o1 b81 b17 b1661 b1278 b2275 b2274 e1112 e1864 (by rfl)
theorem e1866 : o1.scale b81 b1274=b2273 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1276 b2274 b2273 e1108 e1865 (by rfl)
theorem e1867 : o1.scale b81 b1272=b2272 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1274 b2273 b2272 e1108 e1866 (by rfl)
theorem e1868 : o1.scale b81 b1270=b2271 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1272 b2272 b2271 e1108 e1867 (by rfl)
theorem e1869 : o1.scale b81 b1268=b2270 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1270 b2271 b2270 e1108 e1868 (by rfl)
theorem e1870 : o1.scale b81 b53=b2269 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1268 b2270 b2269 e1108 e1869 (by rfl)
theorem e1871 : o2.add b2269 (List.nil : V2)=b2269 := by rfl
theorem e1872 : o2.mul b1657 b53=b2269 := @mul_cons V1 _ o1 b81 (List.nil : V2) b53 (List.nil : V2) b2269 (List.nil : V2) b2269 e753 e1870 (by rfl) e1871
theorem e1873 : o1.mul b80 b48=b2281 := by decide
theorem e1874 : o1.mul b80 b49=b2282 := by decide
theorem e1875 : o1.mul b80 b50=b2283 := by decide
theorem e1876 : o1.mul b80 b51=b2284 := by decide
theorem e1877 : o1.mul b80 b52=b1622 := by decide
theorem e1878 : o1.scale b80 b1288=b2296 := @scale_cons V1 _ o1 b80 b52 b1622 (List.nil : V2) (List.nil : V2) b2296 e1877 e1132 (by rfl)
theorem e1879 : o1.scale b80 b1286=b2295 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1288 b2296 b2295 e1125 e1878 (by rfl)
theorem e1880 : o1.scale b80 b1284=b2294 := @scale_cons V1 _ o1 b80 b51 b2284 b1286 b2295 b2294 e1876 e1879 (by rfl)
theorem e1881 : o1.scale b80 b1282=b2293 := @scale_cons V1 _ o1 b80 b50 b2283 b1284 b2294 b2293 e1875 e1880 (by rfl)
theorem e1882 : o1.scale b80 b1280=b2292 := @scale_cons V1 _ o1 b80 b49 b2282 b1282 b2293 b2292 e1874 e1881 (by rfl)
theorem e1883 : o1.scale b80 b1278=b2291 := @scale_cons V1 _ o1 b80 b48 b2281 b1280 b2292 b2291 e1873 e1882 (by rfl)
theorem e1884 : o1.scale b80 b1276=b2290 := @scale_cons V1 _ o1 b80 b17 b1672 b1278 b2291 b2290 e1129 e1883 (by rfl)
theorem e1885 : o1.scale b80 b1274=b2289 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1276 b2290 b2289 e1125 e1884 (by rfl)
theorem e1886 : o1.scale b80 b1272=b2288 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1274 b2289 b2288 e1125 e1885 (by rfl)
theorem e1887 : o1.scale b80 b1270=b2287 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1272 b2288 b2287 e1125 e1886 (by rfl)
theorem e1888 : o1.scale b80 b1268=b2286 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1270 b2287 b2286 e1125 e1887 (by rfl)
theorem e1889 : o1.scale b80 b53=b2285 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1268 b2286 b2285 e1125 e1888 (by rfl)
theorem e1890 : o1.add b1672 (List.nil : V1)=b1672 := by rfl
theorem e1891 : o1.add b2281 b1661=b2261 := by decide
theorem e1892 : o1.add b2282 b2266=b2262 := by decide
theorem e1893 : o1.add b2283 b2267=b2263 := by decide
theorem e1894 : o1.add b2284 b2268=b2259 := by decide
theorem e1895 : o1.add (List.nil : V1) b2264=b2264 := by rfl
theorem e1896 : o1.add b1622 (List.nil : V1)=b1622 := by rfl
theorem e1897 : o2.add (List.nil : V2) b2280=b2280 := by rfl
theorem e1898 : o2.add b2296 b2279=b2308 := @add_cons V1 _ o1 b1622 (List.nil : V1) b1622 (List.nil : V2) b2280 b2280 b2308 e1896 e1897 (by rfl)
theorem e1899 : o2.add b2295 b2278=b2307 := @add_cons V1 _ o1 (List.nil : V1) b2264 b2264 b2296 b2279 b2308 b2307 e1895 e1898 (by rfl)
theorem e1900 : o2.add b2294 b2277=b2306 := @add_cons V1 _ o1 b2284 b2268 b2259 b2295 b2278 b2307 b2306 e1894 e1899 (by rfl)
theorem e1901 : o2.add b2293 b2276=b2305 := @add_cons V1 _ o1 b2283 b2267 b2263 b2294 b2277 b2306 b2305 e1893 e1900 (by rfl)
theorem e1902 : o2.add b2292 b2275=b2304 := @add_cons V1 _ o1 b2282 b2266 b2262 b2293 b2276 b2305 b2304 e1892 e1901 (by rfl)
theorem e1903 : o2.add b2291 b2274=b2303 := @add_cons V1 _ o1 b2281 b1661 b2261 b2292 b2275 b2304 b2303 e1891 e1902 (by rfl)
theorem e1904 : o2.add b2290 b2273=b2302 := @add_cons V1 _ o1 b1672 (List.nil : V1) b1672 b2291 b2274 b2303 b2302 e1890 e1903 (by rfl)
theorem e1905 : o2.add b2289 b2272=b2301 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2290 b2273 b2302 b2301 e34 e1904 (by rfl)
theorem e1906 : o2.add b2288 b2271=b2300 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2289 b2272 b2301 b2300 e34 e1905 (by rfl)
theorem e1907 : o2.add b2287 b2270=b2299 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2288 b2271 b2300 b2299 e34 e1906 (by rfl)
theorem e1908 : o2.add b2286 b2269=b2298 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2287 b2270 b2299 b2298 e34 e1907 (by rfl)
theorem e1909 : o2.add b2285 b2297=b2265 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2286 b2269 b2298 b2265 e34 e1908 (by rfl)
theorem e1910 : o2.mul b1650 b53=b2265 := @mul_cons V1 _ o1 b80 b1657 b53 b2269 b2285 b2297 b2265 e1872 e1889 (by rfl) e1909
theorem e1911 : o1.mul b79 b48=b2309 := by decide
theorem e1912 : o1.mul b79 b49=b2310 := by decide
theorem e1913 : o1.mul b79 b50=b2311 := by decide
theorem e1914 : o1.mul b79 b51=b2312 := by decide
theorem e1915 : o1.mul b79 b52=b2313 := by decide
theorem e1916 : o1.scale b79 b1288=b2325 := @scale_cons V1 _ o1 b79 b52 b2313 (List.nil : V2) (List.nil : V2) b2325 e1915 e1162 (by rfl)
theorem e1917 : o1.scale b79 b1286=b2324 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1288 b2325 b2324 e1155 e1916 (by rfl)
theorem e1918 : o1.scale b79 b1284=b2323 := @scale_cons V1 _ o1 b79 b51 b2312 b1286 b2324 b2323 e1914 e1917 (by rfl)
theorem e1919 : o1.scale b79 b1282=b2322 := @scale_cons V1 _ o1 b79 b50 b2311 b1284 b2323 b2322 e1913 e1918 (by rfl)
theorem e1920 : o1.scale b79 b1280=b2321 := @scale_cons V1 _ o1 b79 b49 b2310 b1282 b2322 b2321 e1912 e1919 (by rfl)
theorem e1921 : o1.scale b79 b1278=b2320 := @scale_cons V1 _ o1 b79 b48 b2309 b1280 b2321 b2320 e1911 e1920 (by rfl)
theorem e1922 : o1.scale b79 b1276=b2319 := @scale_cons V1 _ o1 b79 b17 b1691 b1278 b2320 b2319 e1159 e1921 (by rfl)
theorem e1923 : o1.scale b79 b1274=b2318 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1276 b2319 b2318 e1155 e1922 (by rfl)
theorem e1924 : o1.scale b79 b1272=b2317 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1274 b2318 b2317 e1155 e1923 (by rfl)
theorem e1925 : o1.scale b79 b1270=b2316 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1272 b2317 b2316 e1155 e1924 (by rfl)
theorem e1926 : o1.scale b79 b1268=b2315 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1270 b2316 b2315 e1155 e1925 (by rfl)
theorem e1927 : o1.scale b79 b53=b2314 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1268 b2315 b2314 e1155 e1926 (by rfl)
theorem e1928 : o1.add b1691 (List.nil : V1)=b1691 := by rfl
theorem e1929 : o1.add b2309 b1672=b2256 := by decide
theorem e1930 : o1.add b2310 b2261=b2257 := by decide
theorem e1931 : o1.add b2311 b2262=b2258 := by decide
theorem e1932 : o1.add b2312 b2263=b2254 := by decide
theorem e1933 : o1.add (List.nil : V1) b2259=b2259 := by rfl
theorem e1934 : o1.add b2313 b2264=b1621 := by decide
theorem e1935 : o2.add (List.nil : V2) b2308=b2308 := by rfl
theorem e1936 : o2.add b2325 b2307=b2337 := @add_cons V1 _ o1 b2313 b2264 b1621 (List.nil : V2) b2308 b2308 b2337 e1934 e1935 (by rfl)
theorem e1937 : o2.add b2324 b2306=b2336 := @add_cons V1 _ o1 (List.nil : V1) b2259 b2259 b2325 b2307 b2337 b2336 e1933 e1936 (by rfl)
theorem e1938 : o2.add b2323 b2305=b2335 := @add_cons V1 _ o1 b2312 b2263 b2254 b2324 b2306 b2336 b2335 e1932 e1937 (by rfl)
theorem e1939 : o2.add b2322 b2304=b2334 := @add_cons V1 _ o1 b2311 b2262 b2258 b2323 b2305 b2335 b2334 e1931 e1938 (by rfl)
theorem e1940 : o2.add b2321 b2303=b2333 := @add_cons V1 _ o1 b2310 b2261 b2257 b2322 b2304 b2334 b2333 e1930 e1939 (by rfl)
theorem e1941 : o2.add b2320 b2302=b2332 := @add_cons V1 _ o1 b2309 b1672 b2256 b2321 b2303 b2333 b2332 e1929 e1940 (by rfl)
theorem e1942 : o2.add b2319 b2301=b2331 := @add_cons V1 _ o1 b1691 (List.nil : V1) b1691 b2320 b2302 b2332 b2331 e1928 e1941 (by rfl)
theorem e1943 : o2.add b2318 b2300=b2330 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2319 b2301 b2331 b2330 e34 e1942 (by rfl)
theorem e1944 : o2.add b2317 b2299=b2329 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2318 b2300 b2330 b2329 e34 e1943 (by rfl)
theorem e1945 : o2.add b2316 b2298=b2328 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2317 b2299 b2329 b2328 e34 e1944 (by rfl)
theorem e1946 : o2.add b2315 b2265=b2327 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2316 b2298 b2328 b2327 e34 e1945 (by rfl)
theorem e1947 : o2.add b2314 b2326=b2260 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2315 b2265 b2327 b2260 e34 e1946 (by rfl)
theorem e1948 : o2.mul b1643 b53=b2260 := @mul_cons V1 _ o1 b79 b1650 b53 b2265 b2314 b2326 b2260 e1910 e1927 (by rfl) e1947
theorem e1949 : o1.mul b78 b48=b2338 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
