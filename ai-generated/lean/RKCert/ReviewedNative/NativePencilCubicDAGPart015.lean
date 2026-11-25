module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart014

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e2100 : o1.scale b79 b60=b2466 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1431 b2467 b2466 e1155 e2099 (by rfl)
theorem e2101 : o1.add b2403 (List.nil : V1)=b2403 := by rfl
theorem e2102 : o1.add b2461 b2409=b2404 := by decide
theorem e2103 : o1.add b2462 b2410=b2405 := by decide
theorem e2104 : o1.add b2463 b2411=b2406 := by decide
theorem e2105 : o1.add b2464 b2412=b2407 := by decide
theorem e2106 : o1.add b2465 b2413=b1631 := by decide
theorem e2107 : o2.add (List.nil : V2) b2460=b2460 := by rfl
theorem e2108 : o2.add b2477 b2459=b2489 := @add_cons V1 _ o1 b2465 b2413 b1631 (List.nil : V2) b2460 b2460 b2489 e2106 e2107 (by rfl)
theorem e2109 : o2.add b2476 b2458=b2488 := @add_cons V1 _ o1 b2464 b2412 b2407 b2477 b2459 b2489 b2488 e2105 e2108 (by rfl)
theorem e2110 : o2.add b2475 b2457=b2487 := @add_cons V1 _ o1 b2463 b2411 b2406 b2476 b2458 b2488 b2487 e2104 e2109 (by rfl)
theorem e2111 : o2.add b2474 b2456=b2486 := @add_cons V1 _ o1 b2462 b2410 b2405 b2475 b2457 b2487 b2486 e2103 e2110 (by rfl)
theorem e2112 : o2.add b2473 b2455=b2485 := @add_cons V1 _ o1 b2461 b2409 b2404 b2474 b2456 b2486 b2485 e2102 e2111 (by rfl)
theorem e2113 : o2.add b2472 b2454=b2484 := @add_cons V1 _ o1 b2403 (List.nil : V1) b2403 b2473 b2455 b2485 b2484 e2101 e2112 (by rfl)
theorem e2114 : o2.add b2471 b2453=b2483 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2472 b2454 b2484 b2483 e34 e2113 (by rfl)
theorem e2115 : o2.add b2470 b2452=b2482 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2471 b2453 b2483 b2482 e34 e2114 (by rfl)
theorem e2116 : o2.add b2469 b2451=b2481 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2470 b2452 b2482 b2481 e34 e2115 (by rfl)
theorem e2117 : o2.add b2468 b2450=b2480 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2469 b2451 b2481 b2480 e34 e2116 (by rfl)
theorem e2118 : o2.add b2467 b2414=b2479 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2468 b2450 b2480 b2479 e34 e2117 (by rfl)
theorem e2119 : o2.add b2466 b2478=b2408 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2467 b2414 b2479 b2408 e34 e2118 (by rfl)
theorem e2120 : o2.mul b1643 b60=b2408 := @mul_cons V1 _ o1 b79 b1650 b60 b2414 b2466 b2478 b2408 e2082 e2100 (by rfl) e2119
theorem e2121 : o1.mul b78 b54=b2397 := by decide
theorem e2122 : o1.mul b78 b55=b2490 := by decide
theorem e2123 : o1.mul b78 b56=b2491 := by decide
theorem e2124 : o1.mul b78 b57=b2492 := by decide
theorem e2125 : o1.mul b78 b58=b2493 := by decide
theorem e2126 : o1.mul b78 b59=b2494 := by decide
theorem e2127 : o1.scale b78 b1451=b2506 := @scale_cons V1 _ o1 b78 b59 b2494 (List.nil : V2) (List.nil : V2) b2506 e2126 e1192 (by rfl)
theorem e2128 : o1.scale b78 b1449=b2505 := @scale_cons V1 _ o1 b78 b58 b2493 b1451 b2506 b2505 e2125 e2127 (by rfl)
theorem e2129 : o1.scale b78 b1447=b2504 := @scale_cons V1 _ o1 b78 b57 b2492 b1449 b2505 b2504 e2124 e2128 (by rfl)
theorem e2130 : o1.scale b78 b1445=b2503 := @scale_cons V1 _ o1 b78 b56 b2491 b1447 b2504 b2503 e2123 e2129 (by rfl)
theorem e2131 : o1.scale b78 b1443=b2502 := @scale_cons V1 _ o1 b78 b55 b2490 b1445 b2503 b2502 e2122 e2130 (by rfl)
theorem e2132 : o1.scale b78 b1441=b2501 := @scale_cons V1 _ o1 b78 b54 b2397 b1443 b2502 b2501 e2121 e2131 (by rfl)
theorem e2133 : o1.scale b78 b1439=b2500 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1441 b2501 b2500 e1185 e2132 (by rfl)
theorem e2134 : o1.scale b78 b1437=b2499 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1439 b2500 b2499 e1185 e2133 (by rfl)
theorem e2135 : o1.scale b78 b1435=b2498 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1437 b2499 b2498 e1185 e2134 (by rfl)
theorem e2136 : o1.scale b78 b1433=b2497 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1435 b2498 b2497 e1185 e2135 (by rfl)
theorem e2137 : o1.scale b78 b1431=b2496 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1433 b2497 b2496 e1185 e2136 (by rfl)
theorem e2138 : o1.scale b78 b60=b2495 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1431 b2496 b2495 e1185 e2137 (by rfl)
theorem e2139 : o1.add b2397 (List.nil : V1)=b2397 := by rfl
theorem e2140 : o1.add b2490 b2403=b2398 := by decide
theorem e2141 : o1.add b2491 b2404=b2399 := by decide
theorem e2142 : o1.add b2492 b2405=b2400 := by decide
theorem e2143 : o1.add b2493 b2406=b2401 := by decide
theorem e2144 : o1.add b2494 b2407=b1630 := by decide
theorem e2145 : o2.add (List.nil : V2) b2489=b2489 := by rfl
theorem e2146 : o2.add b2506 b2488=b2518 := @add_cons V1 _ o1 b2494 b2407 b1630 (List.nil : V2) b2489 b2489 b2518 e2144 e2145 (by rfl)
theorem e2147 : o2.add b2505 b2487=b2517 := @add_cons V1 _ o1 b2493 b2406 b2401 b2506 b2488 b2518 b2517 e2143 e2146 (by rfl)
theorem e2148 : o2.add b2504 b2486=b2516 := @add_cons V1 _ o1 b2492 b2405 b2400 b2505 b2487 b2517 b2516 e2142 e2147 (by rfl)
theorem e2149 : o2.add b2503 b2485=b2515 := @add_cons V1 _ o1 b2491 b2404 b2399 b2504 b2486 b2516 b2515 e2141 e2148 (by rfl)
theorem e2150 : o2.add b2502 b2484=b2514 := @add_cons V1 _ o1 b2490 b2403 b2398 b2503 b2485 b2515 b2514 e2140 e2149 (by rfl)
theorem e2151 : o2.add b2501 b2483=b2513 := @add_cons V1 _ o1 b2397 (List.nil : V1) b2397 b2502 b2484 b2514 b2513 e2139 e2150 (by rfl)
theorem e2152 : o2.add b2500 b2482=b2512 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2501 b2483 b2513 b2512 e34 e2151 (by rfl)
theorem e2153 : o2.add b2499 b2481=b2511 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2500 b2482 b2512 b2511 e34 e2152 (by rfl)
theorem e2154 : o2.add b2498 b2480=b2510 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2499 b2481 b2511 b2510 e34 e2153 (by rfl)
theorem e2155 : o2.add b2497 b2479=b2509 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2498 b2480 b2510 b2509 e34 e2154 (by rfl)
theorem e2156 : o2.add b2496 b2408=b2508 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2497 b2479 b2509 b2508 e34 e2155 (by rfl)
theorem e2157 : o2.add b2495 b2507=b2402 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2496 b2408 b2508 b2402 e34 e2156 (by rfl)
theorem e2158 : o2.mul b1636 b60=b2402 := @mul_cons V1 _ o1 b78 b1643 b60 b2408 b2495 b2507 b2402 e2120 e2138 (by rfl) e2157
theorem e2159 : o1.mul b77 b54=b1624 := by decide
theorem e2160 : o1.mul b77 b55=b2519 := by decide
theorem e2161 : o1.mul b77 b56=b2520 := by decide
theorem e2162 : o1.mul b77 b57=b2521 := by decide
theorem e2163 : o1.mul b77 b58=b2522 := by decide
theorem e2164 : o1.mul b77 b59=b2523 := by decide
theorem e2165 : o1.scale b77 b1451=b2535 := @scale_cons V1 _ o1 b77 b59 b2523 (List.nil : V2) (List.nil : V2) b2535 e2164 e1222 (by rfl)
theorem e2166 : o1.scale b77 b1449=b2534 := @scale_cons V1 _ o1 b77 b58 b2522 b1451 b2535 b2534 e2163 e2165 (by rfl)
theorem e2167 : o1.scale b77 b1447=b2533 := @scale_cons V1 _ o1 b77 b57 b2521 b1449 b2534 b2533 e2162 e2166 (by rfl)
theorem e2168 : o1.scale b77 b1445=b2532 := @scale_cons V1 _ o1 b77 b56 b2520 b1447 b2533 b2532 e2161 e2167 (by rfl)
theorem e2169 : o1.scale b77 b1443=b2531 := @scale_cons V1 _ o1 b77 b55 b2519 b1445 b2532 b2531 e2160 e2168 (by rfl)
theorem e2170 : o1.scale b77 b1441=b2530 := @scale_cons V1 _ o1 b77 b54 b1624 b1443 b2531 b2530 e2159 e2169 (by rfl)
theorem e2171 : o1.scale b77 b1439=b2529 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1441 b2530 b2529 e1215 e2170 (by rfl)
theorem e2172 : o1.scale b77 b1437=b2528 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1439 b2529 b2528 e1215 e2171 (by rfl)
theorem e2173 : o1.scale b77 b1435=b2527 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1437 b2528 b2527 e1215 e2172 (by rfl)
theorem e2174 : o1.scale b77 b1433=b2526 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1435 b2527 b2526 e1215 e2173 (by rfl)
theorem e2175 : o1.scale b77 b1431=b2525 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1433 b2526 b2525 e1215 e2174 (by rfl)
theorem e2176 : o1.scale b77 b60=b2524 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1431 b2525 b2524 e1215 e2175 (by rfl)
theorem e2177 : o1.add b1624 (List.nil : V1)=b1624 := by rfl
theorem e2178 : o1.add b2519 b2397=b1625 := by decide
theorem e2179 : o1.add b2520 b2398=b1626 := by decide
theorem e2180 : o1.add b2521 b2399=b1627 := by decide
theorem e2181 : o1.add b2522 b2400=b1628 := by decide
theorem e2182 : o1.add b2523 b2401=b1629 := by decide
theorem e2183 : o2.add (List.nil : V2) b2518=b2518 := by rfl
theorem e2184 : o2.add b2535 b2517=b2547 := @add_cons V1 _ o1 b2523 b2401 b1629 (List.nil : V2) b2518 b2518 b2547 e2182 e2183 (by rfl)
theorem e2185 : o2.add b2534 b2516=b2546 := @add_cons V1 _ o1 b2522 b2400 b1628 b2535 b2517 b2547 b2546 e2181 e2184 (by rfl)
theorem e2186 : o2.add b2533 b2515=b2545 := @add_cons V1 _ o1 b2521 b2399 b1627 b2534 b2516 b2546 b2545 e2180 e2185 (by rfl)
theorem e2187 : o2.add b2532 b2514=b2544 := @add_cons V1 _ o1 b2520 b2398 b1626 b2533 b2515 b2545 b2544 e2179 e2186 (by rfl)
theorem e2188 : o2.add b2531 b2513=b2543 := @add_cons V1 _ o1 b2519 b2397 b1625 b2532 b2514 b2544 b2543 e2178 e2187 (by rfl)
theorem e2189 : o2.add b2530 b2512=b2542 := @add_cons V1 _ o1 b1624 (List.nil : V1) b1624 b2531 b2513 b2543 b2542 e2177 e2188 (by rfl)
theorem e2190 : o2.add b2529 b2511=b2541 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2530 b2512 b2542 b2541 e34 e2189 (by rfl)
theorem e2191 : o2.add b2528 b2510=b2540 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2529 b2511 b2541 b2540 e34 e2190 (by rfl)
theorem e2192 : o2.add b2527 b2509=b2539 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2528 b2510 b2540 b2539 e34 e2191 (by rfl)
theorem e2193 : o2.add b2526 b2508=b2538 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2527 b2509 b2539 b2538 e34 e2192 (by rfl)
theorem e2194 : o2.add b2525 b2402=b2537 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2526 b2508 b2538 b2537 e34 e2193 (by rfl)
theorem e2195 : o2.add b2524 b2536=b1634 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2525 b2402 b2537 b1634 e34 e2194 (by rfl)
theorem e2196 : o2.mul b82 b60=b1634 := @mul_cons V1 _ o1 b77 b1636 b60 b2402 b2524 b2536 b1634 e2158 e2176 (by rfl) e2195
theorem e2197 : o2.scale b82 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e2198 : o2.scale b82 b1405=b2396 := @scale_cons V2 _ o2 b82 b60 b1634 (List.nil : V3) (List.nil : V3) b2396 e2196 e2197 (by rfl)
theorem e2199 : o2.scale b82 b1247=b2250 := @scale_cons V2 _ o2 b82 b53 b1623 b1405 b2396 b2250 e2024 e2198 (by rfl)
theorem e2200 : o2.scale b82 b1099=b2113 := @scale_cons V2 _ o2 b82 b47 b1612 b1247 b2250 b2113 e1853 e2199 (by rfl)
theorem e2201 : o2.scale b82 b957=b1981 := @scale_cons V2 _ o2 b82 b41 b1601 b1099 b2113 b1981 e1691 e2200 (by rfl)
theorem e2202 : o2.scale b82 b825=b1858 := @scale_cons V2 _ o2 b82 b34 b1590 b957 b1981 b1858 e1533 e2201 (by rfl)
theorem e2203 : o2.scale b82 b703=b1744 := @scale_cons V2 _ o2 b82 b27 b1579 b825 b1858 b1744 e1384 e2202 (by rfl)
theorem e2204 : o2.scale b82 b61=b1635 := @scale_cons V2 _ o2 b82 b20 b464 b703 b1744 b1635 e1244 e2203 (by rfl)
theorem e2205 : o2.add b464 (List.nil : V2)=b464 := by rfl
theorem e2206 : o1.add b1569 b522=b361 := by decide
theorem e2207 : o1.add b1570 b523=b465 := by decide
theorem e2208 : o1.add b1571 b524=b466 := by decide
theorem e2209 : o1.add b1572 b525=b467 := by decide
theorem e2210 : o1.add b1573 b526=b468 := by decide
theorem e2211 : o1.add b1574 b527=b469 := by decide
theorem e2212 : o1.add b1575 b528=b470 := by decide
theorem e2213 : o1.add b1576 b529=b471 := by decide
theorem e2214 : o1.add b1577 b530=b472 := by decide
theorem e2215 : o1.add b1578 b531=b473 := by decide
theorem e2216 : o2.add b1774 (List.nil : V2)=b1774 := by rfl
theorem e2217 : o2.add b1794 b628=b2559 := @add_cons V1 _ o1 b1578 b531 b473 b1774 (List.nil : V2) b1774 b2559 e2215 e2216 (by rfl)
theorem e2218 : o2.add b1815 b647=b2558 := @add_cons V1 _ o1 b1577 b530 b472 b1794 b628 b2559 b2558 e2214 e2217 (by rfl)
theorem e2219 : o2.add b1836 b666=b2557 := @add_cons V1 _ o1 b1576 b529 b471 b1815 b647 b2558 b2557 e2213 e2218 (by rfl)
theorem e2220 : o2.add b1857 b685=b2556 := @add_cons V1 _ o1 b1575 b528 b470 b1836 b666 b2557 b2556 e2212 e2219 (by rfl)
theorem e2221 : o2.add b1856 b702=b2555 := @add_cons V1 _ o1 b1574 b527 b469 b1857 b685 b2556 b2555 e2211 e2220 (by rfl)
theorem e2222 : o2.add b1855 b701=b2554 := @add_cons V1 _ o1 b1573 b526 b468 b1856 b702 b2555 b2554 e2210 e2221 (by rfl)
theorem e2223 : o2.add b1854 b700=b2553 := @add_cons V1 _ o1 b1572 b525 b467 b1855 b701 b2554 b2553 e2209 e2222 (by rfl)
theorem e2224 : o2.add b1853 b699=b2552 := @add_cons V1 _ o1 b1571 b524 b466 b1854 b700 b2553 b2552 e2208 e2223 (by rfl)
theorem e2225 : o2.add b1852 b698=b2551 := @add_cons V1 _ o1 b1570 b523 b465 b1853 b699 b2552 b2551 e2207 e2224 (by rfl)
theorem e2226 : o2.add b1851 b697=b2550 := @add_cons V1 _ o1 b1569 b522 b361 b1852 b698 b2551 b2550 e2206 e2225 (by rfl)
theorem e2227 : o2.add b1579 b532=b475 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b1851 b697 b2550 b475 e34 e2226 (by rfl)
theorem e2228 : o1.add (List.nil : V1) b374=b374 := by rfl
theorem e2229 : o1.add b1580 b533=b375 := by decide
theorem e2230 : o1.add b1581 b534=b476 := by decide
theorem e2231 : o1.add b1582 b535=b477 := by decide
theorem e2232 : o1.add b1583 b536=b478 := by decide
theorem e2233 : o1.add b1584 b537=b479 := by decide
theorem e2234 : o1.add b1585 b538=b480 := by decide
theorem e2235 : o1.add b1586 b539=b481 := by decide
theorem e2236 : o1.add b1587 b540=b482 := by decide
theorem e2237 : o1.add b1588 b541=b483 := by decide
theorem e2238 : o1.add b1589 b542=b484 := by decide
theorem e2239 : o2.add b1889 (List.nil : V2)=b1889 := by rfl
theorem e2240 : o2.add b1911 b741=b2571 := @add_cons V1 _ o1 b1589 b542 b484 b1889 (List.nil : V2) b1889 b2571 e2238 e2239 (by rfl)
theorem e2241 : o2.add b1934 b761=b2570 := @add_cons V1 _ o1 b1588 b541 b483 b1911 b741 b2571 b2570 e2237 e2240 (by rfl)
theorem e2242 : o2.add b1957 b782=b2569 := @add_cons V1 _ o1 b1587 b540 b482 b1934 b761 b2570 b2569 e2236 e2241 (by rfl)
theorem e2243 : o2.add b1980 b803=b2568 := @add_cons V1 _ o1 b1586 b539 b481 b1957 b782 b2569 b2568 e2235 e2242 (by rfl)
theorem e2244 : o2.add b1979 b824=b2567 := @add_cons V1 _ o1 b1585 b538 b480 b1980 b803 b2568 b2567 e2234 e2243 (by rfl)
theorem e2245 : o2.add b1978 b823=b2566 := @add_cons V1 _ o1 b1584 b537 b479 b1979 b824 b2567 b2566 e2233 e2244 (by rfl)
theorem e2246 : o2.add b1977 b822=b2565 := @add_cons V1 _ o1 b1583 b536 b478 b1978 b823 b2566 b2565 e2232 e2245 (by rfl)
theorem e2247 : o2.add b1976 b821=b2564 := @add_cons V1 _ o1 b1582 b535 b477 b1977 b822 b2565 b2564 e2231 e2246 (by rfl)
theorem e2248 : o2.add b1975 b820=b2563 := @add_cons V1 _ o1 b1581 b534 b476 b1976 b821 b2564 b2563 e2230 e2247 (by rfl)
theorem e2249 : o2.add b1974 b819=b2562 := @add_cons V1 _ o1 b1580 b533 b375 b1975 b820 b2563 b2562 e2229 e2248 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
