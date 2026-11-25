module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart013

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e1950 : o1.mul b78 b49=b2339 := by decide
theorem e1951 : o1.mul b78 b50=b2340 := by decide
theorem e1952 : o1.mul b78 b51=b2341 := by decide
theorem e1953 : o1.mul b78 b52=b2342 := by decide
theorem e1954 : o1.scale b78 b1288=b2354 := @scale_cons V1 _ o1 b78 b52 b2342 (List.nil : V2) (List.nil : V2) b2354 e1953 e1192 (by rfl)
theorem e1955 : o1.scale b78 b1286=b2353 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1288 b2354 b2353 e1185 e1954 (by rfl)
theorem e1956 : o1.scale b78 b1284=b2352 := @scale_cons V1 _ o1 b78 b51 b2341 b1286 b2353 b2352 e1952 e1955 (by rfl)
theorem e1957 : o1.scale b78 b1282=b2351 := @scale_cons V1 _ o1 b78 b50 b2340 b1284 b2352 b2351 e1951 e1956 (by rfl)
theorem e1958 : o1.scale b78 b1280=b2350 := @scale_cons V1 _ o1 b78 b49 b2339 b1282 b2351 b2350 e1950 e1957 (by rfl)
theorem e1959 : o1.scale b78 b1278=b2349 := @scale_cons V1 _ o1 b78 b48 b2338 b1280 b2350 b2349 e1949 e1958 (by rfl)
theorem e1960 : o1.scale b78 b1276=b2348 := @scale_cons V1 _ o1 b78 b17 b1710 b1278 b2349 b2348 e1189 e1959 (by rfl)
theorem e1961 : o1.scale b78 b1274=b2347 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1276 b2348 b2347 e1185 e1960 (by rfl)
theorem e1962 : o1.scale b78 b1272=b2346 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1274 b2347 b2346 e1185 e1961 (by rfl)
theorem e1963 : o1.scale b78 b1270=b2345 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1272 b2346 b2345 e1185 e1962 (by rfl)
theorem e1964 : o1.scale b78 b1268=b2344 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1270 b2345 b2344 e1185 e1963 (by rfl)
theorem e1965 : o1.scale b78 b53=b2343 := @scale_cons V1 _ o1 b78 (List.nil : V1) (List.nil : V1) b1268 b2344 b2343 e1185 e1964 (by rfl)
theorem e1966 : o1.add b1710 (List.nil : V1)=b1710 := by rfl
theorem e1967 : o1.add b2338 b1691=b2251 := by decide
theorem e1968 : o1.add b2339 b2256=b2252 := by decide
theorem e1969 : o1.add b2340 b2257=b2253 := by decide
theorem e1970 : o1.add b2341 b2258=b1618 := by decide
theorem e1971 : o1.add (List.nil : V1) b2254=b2254 := by rfl
theorem e1972 : o1.add b2342 b2259=b1620 := by decide
theorem e1973 : o2.add (List.nil : V2) b2337=b2337 := by rfl
theorem e1974 : o2.add b2354 b2336=b2366 := @add_cons V1 _ o1 b2342 b2259 b1620 (List.nil : V2) b2337 b2337 b2366 e1972 e1973 (by rfl)
theorem e1975 : o2.add b2353 b2335=b2365 := @add_cons V1 _ o1 (List.nil : V1) b2254 b2254 b2354 b2336 b2366 b2365 e1971 e1974 (by rfl)
theorem e1976 : o2.add b2352 b2334=b2364 := @add_cons V1 _ o1 b2341 b2258 b1618 b2353 b2335 b2365 b2364 e1970 e1975 (by rfl)
theorem e1977 : o2.add b2351 b2333=b2363 := @add_cons V1 _ o1 b2340 b2257 b2253 b2352 b2334 b2364 b2363 e1969 e1976 (by rfl)
theorem e1978 : o2.add b2350 b2332=b2362 := @add_cons V1 _ o1 b2339 b2256 b2252 b2351 b2333 b2363 b2362 e1968 e1977 (by rfl)
theorem e1979 : o2.add b2349 b2331=b2361 := @add_cons V1 _ o1 b2338 b1691 b2251 b2350 b2332 b2362 b2361 e1967 e1978 (by rfl)
theorem e1980 : o2.add b2348 b2330=b2360 := @add_cons V1 _ o1 b1710 (List.nil : V1) b1710 b2349 b2331 b2361 b2360 e1966 e1979 (by rfl)
theorem e1981 : o2.add b2347 b2329=b2359 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2348 b2330 b2360 b2359 e34 e1980 (by rfl)
theorem e1982 : o2.add b2346 b2328=b2358 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2347 b2329 b2359 b2358 e34 e1981 (by rfl)
theorem e1983 : o2.add b2345 b2327=b2357 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2346 b2328 b2358 b2357 e34 e1982 (by rfl)
theorem e1984 : o2.add b2344 b2260=b2356 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2345 b2327 b2357 b2356 e34 e1983 (by rfl)
theorem e1985 : o2.add b2343 b2355=b2255 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2344 b2260 b2356 b2255 e34 e1984 (by rfl)
theorem e1986 : o2.mul b1636 b53=b2255 := @mul_cons V1 _ o1 b78 b1643 b53 b2260 b2343 b2355 b2255 e1948 e1965 (by rfl) e1985
theorem e1987 : o1.mul b77 b48=b2367 := by decide
theorem e1988 : o1.mul b77 b49=b2368 := by decide
theorem e1989 : o1.mul b77 b50=b2369 := by decide
theorem e1990 : o1.mul b77 b51=b2370 := by decide
theorem e1991 : o1.mul b77 b52=b2371 := by decide
theorem e1992 : o1.scale b77 b1288=b2383 := @scale_cons V1 _ o1 b77 b52 b2371 (List.nil : V2) (List.nil : V2) b2383 e1991 e1222 (by rfl)
theorem e1993 : o1.scale b77 b1286=b2382 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1288 b2383 b2382 e1215 e1992 (by rfl)
theorem e1994 : o1.scale b77 b1284=b2381 := @scale_cons V1 _ o1 b77 b51 b2370 b1286 b2382 b2381 e1990 e1993 (by rfl)
theorem e1995 : o1.scale b77 b1282=b2380 := @scale_cons V1 _ o1 b77 b50 b2369 b1284 b2381 b2380 e1989 e1994 (by rfl)
theorem e1996 : o1.scale b77 b1280=b2379 := @scale_cons V1 _ o1 b77 b49 b2368 b1282 b2380 b2379 e1988 e1995 (by rfl)
theorem e1997 : o1.scale b77 b1278=b2378 := @scale_cons V1 _ o1 b77 b48 b2367 b1280 b2379 b2378 e1987 e1996 (by rfl)
theorem e1998 : o1.scale b77 b1276=b2377 := @scale_cons V1 _ o1 b77 b17 b1613 b1278 b2378 b2377 e1219 e1997 (by rfl)
theorem e1999 : o1.scale b77 b1274=b2376 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1276 b2377 b2376 e1215 e1998 (by rfl)
theorem e2000 : o1.scale b77 b1272=b2375 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1274 b2376 b2375 e1215 e1999 (by rfl)
theorem e2001 : o1.scale b77 b1270=b2374 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1272 b2375 b2374 e1215 e2000 (by rfl)
theorem e2002 : o1.scale b77 b1268=b2373 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1270 b2374 b2373 e1215 e2001 (by rfl)
theorem e2003 : o1.scale b77 b53=b2372 := @scale_cons V1 _ o1 b77 (List.nil : V1) (List.nil : V1) b1268 b2373 b2372 e1215 e2002 (by rfl)
theorem e2004 : o1.add b1613 (List.nil : V1)=b1613 := by rfl
theorem e2005 : o1.add b2367 b1710=b1614 := by decide
theorem e2006 : o1.add b2368 b2251=b1615 := by decide
theorem e2007 : o1.add b2369 b2252=b1616 := by decide
theorem e2008 : o1.add b2370 b2253=b1617 := by decide
theorem e2009 : o1.add (List.nil : V1) b1618=b1618 := by rfl
theorem e2010 : o1.add b2371 b2254=b1619 := by decide
theorem e2011 : o2.add (List.nil : V2) b2366=b2366 := by rfl
theorem e2012 : o2.add b2383 b2365=b2395 := @add_cons V1 _ o1 b2371 b2254 b1619 (List.nil : V2) b2366 b2366 b2395 e2010 e2011 (by rfl)
theorem e2013 : o2.add b2382 b2364=b2394 := @add_cons V1 _ o1 (List.nil : V1) b1618 b1618 b2383 b2365 b2395 b2394 e2009 e2012 (by rfl)
theorem e2014 : o2.add b2381 b2363=b2393 := @add_cons V1 _ o1 b2370 b2253 b1617 b2382 b2364 b2394 b2393 e2008 e2013 (by rfl)
theorem e2015 : o2.add b2380 b2362=b2392 := @add_cons V1 _ o1 b2369 b2252 b1616 b2381 b2363 b2393 b2392 e2007 e2014 (by rfl)
theorem e2016 : o2.add b2379 b2361=b2391 := @add_cons V1 _ o1 b2368 b2251 b1615 b2380 b2362 b2392 b2391 e2006 e2015 (by rfl)
theorem e2017 : o2.add b2378 b2360=b2390 := @add_cons V1 _ o1 b2367 b1710 b1614 b2379 b2361 b2391 b2390 e2005 e2016 (by rfl)
theorem e2018 : o2.add b2377 b2359=b2389 := @add_cons V1 _ o1 b1613 (List.nil : V1) b1613 b2378 b2360 b2390 b2389 e2004 e2017 (by rfl)
theorem e2019 : o2.add b2376 b2358=b2388 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2377 b2359 b2389 b2388 e34 e2018 (by rfl)
theorem e2020 : o2.add b2375 b2357=b2387 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2376 b2358 b2388 b2387 e34 e2019 (by rfl)
theorem e2021 : o2.add b2374 b2356=b2386 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2375 b2357 b2387 b2386 e34 e2020 (by rfl)
theorem e2022 : o2.add b2373 b2255=b2385 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2374 b2356 b2386 b2385 e34 e2021 (by rfl)
theorem e2023 : o2.add b2372 b2384=b1623 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2373 b2255 b2385 b1623 e34 e2022 (by rfl)
theorem e2024 : o2.mul b82 b53=b1623 := @mul_cons V1 _ o1 b77 b1636 b53 b2255 b2372 b2384 b1623 e1986 e2003 (by rfl) e2023
theorem e2025 : o1.mul b81 b54=b2415 := by decide
theorem e2026 : o1.mul b81 b55=b2416 := by decide
theorem e2027 : o1.mul b81 b56=b2417 := by decide
theorem e2028 : o1.mul b81 b57=b2418 := by decide
theorem e2029 : o1.mul b81 b58=b2419 := by decide
theorem e2030 : o1.mul b81 b59=b1633 := by decide
theorem e2031 : o1.scale b81 b1451=b2431 := @scale_cons V1 _ o1 b81 b59 b1633 (List.nil : V2) (List.nil : V2) b2431 e2030 e1115 (by rfl)
theorem e2032 : o1.scale b81 b1449=b2430 := @scale_cons V1 _ o1 b81 b58 b2419 b1451 b2431 b2430 e2029 e2031 (by rfl)
theorem e2033 : o1.scale b81 b1447=b2429 := @scale_cons V1 _ o1 b81 b57 b2418 b1449 b2430 b2429 e2028 e2032 (by rfl)
theorem e2034 : o1.scale b81 b1445=b2428 := @scale_cons V1 _ o1 b81 b56 b2417 b1447 b2429 b2428 e2027 e2033 (by rfl)
theorem e2035 : o1.scale b81 b1443=b2427 := @scale_cons V1 _ o1 b81 b55 b2416 b1445 b2428 b2427 e2026 e2034 (by rfl)
theorem e2036 : o1.scale b81 b1441=b2426 := @scale_cons V1 _ o1 b81 b54 b2415 b1443 b2427 b2426 e2025 e2035 (by rfl)
theorem e2037 : o1.scale b81 b1439=b2425 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1441 b2426 b2425 e1108 e2036 (by rfl)
theorem e2038 : o1.scale b81 b1437=b2424 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1439 b2425 b2424 e1108 e2037 (by rfl)
theorem e2039 : o1.scale b81 b1435=b2423 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1437 b2424 b2423 e1108 e2038 (by rfl)
theorem e2040 : o1.scale b81 b1433=b2422 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1435 b2423 b2422 e1108 e2039 (by rfl)
theorem e2041 : o1.scale b81 b1431=b2421 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1433 b2422 b2421 e1108 e2040 (by rfl)
theorem e2042 : o1.scale b81 b60=b2420 := @scale_cons V1 _ o1 b81 (List.nil : V1) (List.nil : V1) b1431 b2421 b2420 e1108 e2041 (by rfl)
theorem e2043 : o2.add b2420 (List.nil : V2)=b2420 := by rfl
theorem e2044 : o2.mul b1657 b60=b2420 := @mul_cons V1 _ o1 b81 (List.nil : V2) b60 (List.nil : V2) b2420 (List.nil : V2) b2420 e925 e2042 (by rfl) e2043
theorem e2045 : o1.mul b80 b54=b2409 := by decide
theorem e2046 : o1.mul b80 b55=b2432 := by decide
theorem e2047 : o1.mul b80 b56=b2433 := by decide
theorem e2048 : o1.mul b80 b57=b2434 := by decide
theorem e2049 : o1.mul b80 b58=b2435 := by decide
theorem e2050 : o1.mul b80 b59=b2436 := by decide
theorem e2051 : o1.scale b80 b1451=b2448 := @scale_cons V1 _ o1 b80 b59 b2436 (List.nil : V2) (List.nil : V2) b2448 e2050 e1132 (by rfl)
theorem e2052 : o1.scale b80 b1449=b2447 := @scale_cons V1 _ o1 b80 b58 b2435 b1451 b2448 b2447 e2049 e2051 (by rfl)
theorem e2053 : o1.scale b80 b1447=b2446 := @scale_cons V1 _ o1 b80 b57 b2434 b1449 b2447 b2446 e2048 e2052 (by rfl)
theorem e2054 : o1.scale b80 b1445=b2445 := @scale_cons V1 _ o1 b80 b56 b2433 b1447 b2446 b2445 e2047 e2053 (by rfl)
theorem e2055 : o1.scale b80 b1443=b2444 := @scale_cons V1 _ o1 b80 b55 b2432 b1445 b2445 b2444 e2046 e2054 (by rfl)
theorem e2056 : o1.scale b80 b1441=b2443 := @scale_cons V1 _ o1 b80 b54 b2409 b1443 b2444 b2443 e2045 e2055 (by rfl)
theorem e2057 : o1.scale b80 b1439=b2442 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1441 b2443 b2442 e1125 e2056 (by rfl)
theorem e2058 : o1.scale b80 b1437=b2441 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1439 b2442 b2441 e1125 e2057 (by rfl)
theorem e2059 : o1.scale b80 b1435=b2440 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1437 b2441 b2440 e1125 e2058 (by rfl)
theorem e2060 : o1.scale b80 b1433=b2439 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1435 b2440 b2439 e1125 e2059 (by rfl)
theorem e2061 : o1.scale b80 b1431=b2438 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1433 b2439 b2438 e1125 e2060 (by rfl)
theorem e2062 : o1.scale b80 b60=b2437 := @scale_cons V1 _ o1 b80 (List.nil : V1) (List.nil : V1) b1431 b2438 b2437 e1125 e2061 (by rfl)
theorem e2063 : o1.add b2409 (List.nil : V1)=b2409 := by rfl
theorem e2064 : o1.add b2432 b2415=b2410 := by decide
theorem e2065 : o1.add b2433 b2416=b2411 := by decide
theorem e2066 : o1.add b2434 b2417=b2412 := by decide
theorem e2067 : o1.add b2435 b2418=b2413 := by decide
theorem e2068 : o1.add b2436 b2419=b1632 := by decide
theorem e2069 : o2.add (List.nil : V2) b2431=b2431 := by rfl
theorem e2070 : o2.add b2448 b2430=b2460 := @add_cons V1 _ o1 b2436 b2419 b1632 (List.nil : V2) b2431 b2431 b2460 e2068 e2069 (by rfl)
theorem e2071 : o2.add b2447 b2429=b2459 := @add_cons V1 _ o1 b2435 b2418 b2413 b2448 b2430 b2460 b2459 e2067 e2070 (by rfl)
theorem e2072 : o2.add b2446 b2428=b2458 := @add_cons V1 _ o1 b2434 b2417 b2412 b2447 b2429 b2459 b2458 e2066 e2071 (by rfl)
theorem e2073 : o2.add b2445 b2427=b2457 := @add_cons V1 _ o1 b2433 b2416 b2411 b2446 b2428 b2458 b2457 e2065 e2072 (by rfl)
theorem e2074 : o2.add b2444 b2426=b2456 := @add_cons V1 _ o1 b2432 b2415 b2410 b2445 b2427 b2457 b2456 e2064 e2073 (by rfl)
theorem e2075 : o2.add b2443 b2425=b2455 := @add_cons V1 _ o1 b2409 (List.nil : V1) b2409 b2444 b2426 b2456 b2455 e2063 e2074 (by rfl)
theorem e2076 : o2.add b2442 b2424=b2454 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2443 b2425 b2455 b2454 e34 e2075 (by rfl)
theorem e2077 : o2.add b2441 b2423=b2453 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2442 b2424 b2454 b2453 e34 e2076 (by rfl)
theorem e2078 : o2.add b2440 b2422=b2452 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2441 b2423 b2453 b2452 e34 e2077 (by rfl)
theorem e2079 : o2.add b2439 b2421=b2451 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2440 b2422 b2452 b2451 e34 e2078 (by rfl)
theorem e2080 : o2.add b2438 b2420=b2450 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2439 b2421 b2451 b2450 e34 e2079 (by rfl)
theorem e2081 : o2.add b2437 b2449=b2414 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2438 b2420 b2450 b2414 e34 e2080 (by rfl)
theorem e2082 : o2.mul b1650 b60=b2414 := @mul_cons V1 _ o1 b80 b1657 b60 b2420 b2437 b2449 b2414 e2044 e2062 (by rfl) e2081
theorem e2083 : o1.mul b79 b54=b2403 := by decide
theorem e2084 : o1.mul b79 b55=b2461 := by decide
theorem e2085 : o1.mul b79 b56=b2462 := by decide
theorem e2086 : o1.mul b79 b57=b2463 := by decide
theorem e2087 : o1.mul b79 b58=b2464 := by decide
theorem e2088 : o1.mul b79 b59=b2465 := by decide
theorem e2089 : o1.scale b79 b1451=b2477 := @scale_cons V1 _ o1 b79 b59 b2465 (List.nil : V2) (List.nil : V2) b2477 e2088 e1162 (by rfl)
theorem e2090 : o1.scale b79 b1449=b2476 := @scale_cons V1 _ o1 b79 b58 b2464 b1451 b2477 b2476 e2087 e2089 (by rfl)
theorem e2091 : o1.scale b79 b1447=b2475 := @scale_cons V1 _ o1 b79 b57 b2463 b1449 b2476 b2475 e2086 e2090 (by rfl)
theorem e2092 : o1.scale b79 b1445=b2474 := @scale_cons V1 _ o1 b79 b56 b2462 b1447 b2475 b2474 e2085 e2091 (by rfl)
theorem e2093 : o1.scale b79 b1443=b2473 := @scale_cons V1 _ o1 b79 b55 b2461 b1445 b2474 b2473 e2084 e2092 (by rfl)
theorem e2094 : o1.scale b79 b1441=b2472 := @scale_cons V1 _ o1 b79 b54 b2403 b1443 b2473 b2472 e2083 e2093 (by rfl)
theorem e2095 : o1.scale b79 b1439=b2471 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1441 b2472 b2471 e1155 e2094 (by rfl)
theorem e2096 : o1.scale b79 b1437=b2470 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1439 b2471 b2470 e1155 e2095 (by rfl)
theorem e2097 : o1.scale b79 b1435=b2469 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1437 b2470 b2469 e1155 e2096 (by rfl)
theorem e2098 : o1.scale b79 b1433=b2468 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1435 b2469 b2468 e1155 e2097 (by rfl)
theorem e2099 : o1.scale b79 b1431=b2467 := @scale_cons V1 _ o1 b79 (List.nil : V1) (List.nil : V1) b1433 b2468 b2467 e1155 e2098 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
