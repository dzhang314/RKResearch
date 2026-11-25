module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart016

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e2400 : o1.add b2731 b2719=b2713 := by decide
theorem e2401 : o1.add b2732 b2720=b2714 := by decide
theorem e2402 : o1.add b2733 b2721=b2715 := by decide
theorem e2403 : o1.add b2734 b2722=b2716 := by decide
theorem e2404 : o1.add b2735 b2723=b346 := by decide
theorem e2405 : o2.add (List.nil : V2) b2730=b2730 := by rfl
theorem e2406 : o2.add b2742 b2729=b2749 := @add_cons V1 _ o1 b2735 b2723 b346 (List.nil : V2) b2730 b2730 b2749 e2404 e2405 (by rfl)
theorem e2407 : o2.add b2741 b2728=b2748 := @add_cons V1 _ o1 b2734 b2722 b2716 b2742 b2729 b2749 b2748 e2403 e2406 (by rfl)
theorem e2408 : o2.add b2740 b2727=b2747 := @add_cons V1 _ o1 b2733 b2721 b2715 b2741 b2728 b2748 b2747 e2402 e2407 (by rfl)
theorem e2409 : o2.add b2739 b2726=b2746 := @add_cons V1 _ o1 b2732 b2720 b2714 b2740 b2727 b2747 b2746 e2401 e2408 (by rfl)
theorem e2410 : o2.add b2738 b2725=b2745 := @add_cons V1 _ o1 b2731 b2719 b2713 b2739 b2726 b2746 b2745 e2400 e2409 (by rfl)
theorem e2411 : o2.add b2737 b2724=b2744 := @add_cons V1 _ o1 b2712 (List.nil : V1) b2712 b2738 b2725 b2745 b2744 e2399 e2410 (by rfl)
theorem e2412 : o2.add b2736 b2743=b2717 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2737 b2724 b2744 b2717 e34 e2411 (by rfl)
theorem e2413 : o2.mul b2711 b20=b2717 := @mul_cons V1 _ o1 b74 b2718 b20 b2724 b2736 b2743 b2717 e2383 e2398 (by rfl) e2412
theorem e2414 : o1.mul b73 (List.nil : V1)=(List.nil : V1) := by decide
theorem e2415 : o1.mul b73 b14=b2705 := by decide
theorem e2416 : o1.mul b73 b15=b2750 := by decide
theorem e2417 : o1.mul b73 b16=b2751 := by decide
theorem e2418 : o1.mul b73 b17=b2752 := by decide
theorem e2419 : o1.mul b73 b18=b2753 := by decide
theorem e2420 : o1.mul b73 b19=b2754 := by decide
theorem e2421 : o1.scale b73 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e2422 : o1.scale b73 b627=b2761 := @scale_cons V1 _ o1 b73 b19 b2754 (List.nil : V2) (List.nil : V2) b2761 e2420 e2421 (by rfl)
theorem e2423 : o1.scale b73 b625=b2760 := @scale_cons V1 _ o1 b73 b18 b2753 b627 b2761 b2760 e2419 e2422 (by rfl)
theorem e2424 : o1.scale b73 b623=b2759 := @scale_cons V1 _ o1 b73 b17 b2752 b625 b2760 b2759 e2418 e2423 (by rfl)
theorem e2425 : o1.scale b73 b621=b2758 := @scale_cons V1 _ o1 b73 b16 b2751 b623 b2759 b2758 e2417 e2424 (by rfl)
theorem e2426 : o1.scale b73 b619=b2757 := @scale_cons V1 _ o1 b73 b15 b2750 b621 b2758 b2757 e2416 e2425 (by rfl)
theorem e2427 : o1.scale b73 b617=b2756 := @scale_cons V1 _ o1 b73 b14 b2705 b619 b2757 b2756 e2415 e2426 (by rfl)
theorem e2428 : o1.scale b73 b20=b2755 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b617 b2756 b2755 e2414 e2427 (by rfl)
theorem e2429 : o1.add b2705 (List.nil : V1)=b2705 := by rfl
theorem e2430 : o1.add b2750 b2712=b2706 := by decide
theorem e2431 : o1.add b2751 b2713=b2707 := by decide
theorem e2432 : o1.add b2752 b2714=b2708 := by decide
theorem e2433 : o1.add b2753 b2715=b2709 := by decide
theorem e2434 : o1.add b2754 b2716=b345 := by decide
theorem e2435 : o2.add (List.nil : V2) b2749=b2749 := by rfl
theorem e2436 : o2.add b2761 b2748=b2768 := @add_cons V1 _ o1 b2754 b2716 b345 (List.nil : V2) b2749 b2749 b2768 e2434 e2435 (by rfl)
theorem e2437 : o2.add b2760 b2747=b2767 := @add_cons V1 _ o1 b2753 b2715 b2709 b2761 b2748 b2768 b2767 e2433 e2436 (by rfl)
theorem e2438 : o2.add b2759 b2746=b2766 := @add_cons V1 _ o1 b2752 b2714 b2708 b2760 b2747 b2767 b2766 e2432 e2437 (by rfl)
theorem e2439 : o2.add b2758 b2745=b2765 := @add_cons V1 _ o1 b2751 b2713 b2707 b2759 b2746 b2766 b2765 e2431 e2438 (by rfl)
theorem e2440 : o2.add b2757 b2744=b2764 := @add_cons V1 _ o1 b2750 b2712 b2706 b2758 b2745 b2765 b2764 e2430 e2439 (by rfl)
theorem e2441 : o2.add b2756 b2717=b2763 := @add_cons V1 _ o1 b2705 (List.nil : V1) b2705 b2757 b2744 b2764 b2763 e2429 e2440 (by rfl)
theorem e2442 : o2.add b2755 b2762=b2710 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2756 b2717 b2763 b2710 e34 e2441 (by rfl)
theorem e2443 : o2.mul b2704 b20=b2710 := @mul_cons V1 _ o1 b73 b2711 b20 b2717 b2755 b2762 b2710 e2413 e2428 (by rfl) e2442
theorem e2444 : o1.mul b72 (List.nil : V1)=(List.nil : V1) := by decide
theorem e2445 : o1.mul b72 b14=b2698 := by decide
theorem e2446 : o1.mul b72 b15=b2769 := by decide
theorem e2447 : o1.mul b72 b16=b2770 := by decide
theorem e2448 : o1.mul b72 b17=b2771 := by decide
theorem e2449 : o1.mul b72 b18=b2772 := by decide
theorem e2450 : o1.mul b72 b19=b2773 := by decide
theorem e2451 : o1.scale b72 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e2452 : o1.scale b72 b627=b2780 := @scale_cons V1 _ o1 b72 b19 b2773 (List.nil : V2) (List.nil : V2) b2780 e2450 e2451 (by rfl)
theorem e2453 : o1.scale b72 b625=b2779 := @scale_cons V1 _ o1 b72 b18 b2772 b627 b2780 b2779 e2449 e2452 (by rfl)
theorem e2454 : o1.scale b72 b623=b2778 := @scale_cons V1 _ o1 b72 b17 b2771 b625 b2779 b2778 e2448 e2453 (by rfl)
theorem e2455 : o1.scale b72 b621=b2777 := @scale_cons V1 _ o1 b72 b16 b2770 b623 b2778 b2777 e2447 e2454 (by rfl)
theorem e2456 : o1.scale b72 b619=b2776 := @scale_cons V1 _ o1 b72 b15 b2769 b621 b2777 b2776 e2446 e2455 (by rfl)
theorem e2457 : o1.scale b72 b617=b2775 := @scale_cons V1 _ o1 b72 b14 b2698 b619 b2776 b2775 e2445 e2456 (by rfl)
theorem e2458 : o1.scale b72 b20=b2774 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b617 b2775 b2774 e2444 e2457 (by rfl)
theorem e2459 : o1.add b2698 (List.nil : V1)=b2698 := by rfl
theorem e2460 : o1.add b2769 b2705=b2699 := by decide
theorem e2461 : o1.add b2770 b2706=b2700 := by decide
theorem e2462 : o1.add b2771 b2707=b2701 := by decide
theorem e2463 : o1.add b2772 b2708=b2702 := by decide
theorem e2464 : o1.add b2773 b2709=b344 := by decide
theorem e2465 : o2.add (List.nil : V2) b2768=b2768 := by rfl
theorem e2466 : o2.add b2780 b2767=b2787 := @add_cons V1 _ o1 b2773 b2709 b344 (List.nil : V2) b2768 b2768 b2787 e2464 e2465 (by rfl)
theorem e2467 : o2.add b2779 b2766=b2786 := @add_cons V1 _ o1 b2772 b2708 b2702 b2780 b2767 b2787 b2786 e2463 e2466 (by rfl)
theorem e2468 : o2.add b2778 b2765=b2785 := @add_cons V1 _ o1 b2771 b2707 b2701 b2779 b2766 b2786 b2785 e2462 e2467 (by rfl)
theorem e2469 : o2.add b2777 b2764=b2784 := @add_cons V1 _ o1 b2770 b2706 b2700 b2778 b2765 b2785 b2784 e2461 e2468 (by rfl)
theorem e2470 : o2.add b2776 b2763=b2783 := @add_cons V1 _ o1 b2769 b2705 b2699 b2777 b2764 b2784 b2783 e2460 e2469 (by rfl)
theorem e2471 : o2.add b2775 b2710=b2782 := @add_cons V1 _ o1 b2698 (List.nil : V1) b2698 b2776 b2763 b2783 b2782 e2459 e2470 (by rfl)
theorem e2472 : o2.add b2774 b2781=b2703 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2775 b2710 b2782 b2703 e34 e2471 (by rfl)
theorem e2473 : o2.mul b2697 b20=b2703 := @mul_cons V1 _ o1 b72 b2704 b20 b2710 b2774 b2781 b2703 e2443 e2458 (by rfl) e2472
theorem e2474 : o1.mul b71 (List.nil : V1)=(List.nil : V1) := by decide
theorem e2475 : o1.mul b71 b14=b338 := by decide
theorem e2476 : o1.mul b71 b15=b2788 := by decide
theorem e2477 : o1.mul b71 b16=b2789 := by decide
theorem e2478 : o1.mul b71 b17=b2674 := by decide
theorem e2479 : o1.mul b71 b18=b2663 := by decide
theorem e2480 : o1.mul b71 b19=b2790 := by decide
theorem e2481 : o1.scale b71 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e2482 : o1.scale b71 b627=b2797 := @scale_cons V1 _ o1 b71 b19 b2790 (List.nil : V2) (List.nil : V2) b2797 e2480 e2481 (by rfl)
theorem e2483 : o1.scale b71 b625=b2796 := @scale_cons V1 _ o1 b71 b18 b2663 b627 b2797 b2796 e2479 e2482 (by rfl)
theorem e2484 : o1.scale b71 b623=b2795 := @scale_cons V1 _ o1 b71 b17 b2674 b625 b2796 b2795 e2478 e2483 (by rfl)
theorem e2485 : o1.scale b71 b621=b2794 := @scale_cons V1 _ o1 b71 b16 b2789 b623 b2795 b2794 e2477 e2484 (by rfl)
theorem e2486 : o1.scale b71 b619=b2793 := @scale_cons V1 _ o1 b71 b15 b2788 b621 b2794 b2793 e2476 e2485 (by rfl)
theorem e2487 : o1.scale b71 b617=b2792 := @scale_cons V1 _ o1 b71 b14 b338 b619 b2793 b2792 e2475 e2486 (by rfl)
theorem e2488 : o1.scale b71 b20=b2791 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b617 b2792 b2791 e2474 e2487 (by rfl)
theorem e2489 : o1.add b338 (List.nil : V1)=b338 := by rfl
theorem e2490 : o1.add b2788 b2698=b339 := by decide
theorem e2491 : o1.add b2789 b2699=b340 := by decide
theorem e2492 : o1.add b2674 b2700=b341 := by decide
theorem e2493 : o1.add b2663 b2701=b342 := by decide
theorem e2494 : o1.add b2790 b2702=b343 := by decide
theorem e2495 : o2.add (List.nil : V2) b2787=b2787 := by rfl
theorem e2496 : o2.add b2797 b2786=b2804 := @add_cons V1 _ o1 b2790 b2702 b343 (List.nil : V2) b2787 b2787 b2804 e2494 e2495 (by rfl)
theorem e2497 : o2.add b2796 b2785=b2803 := @add_cons V1 _ o1 b2663 b2701 b342 b2797 b2786 b2804 b2803 e2493 e2496 (by rfl)
theorem e2498 : o2.add b2795 b2784=b2802 := @add_cons V1 _ o1 b2674 b2700 b341 b2796 b2785 b2803 b2802 e2492 e2497 (by rfl)
theorem e2499 : o2.add b2794 b2783=b2801 := @add_cons V1 _ o1 b2789 b2699 b340 b2795 b2784 b2802 b2801 e2491 e2498 (by rfl)
theorem e2500 : o2.add b2793 b2782=b2800 := @add_cons V1 _ o1 b2788 b2698 b339 b2794 b2783 b2801 b2800 e2490 e2499 (by rfl)
theorem e2501 : o2.add b2792 b2703=b2799 := @add_cons V1 _ o1 b338 (List.nil : V1) b338 b2793 b2782 b2800 b2799 e2489 e2500 (by rfl)
theorem e2502 : o2.add b2791 b2798=b348 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2792 b2703 b2799 b348 e34 e2501 (by rfl)
theorem e2503 : o2.mul b76 b20=b348 := @mul_cons V1 _ o1 b71 b2697 b20 b2703 b2791 b2798 b348 e2473 e2488 (by rfl) e2502
theorem e2504 : o1.mul b75 b21=b2818 := by decide
theorem e2505 : o1.mul b75 b22=b2824 := by decide
theorem e2506 : o1.mul b75 b23=b2825 := by decide
theorem e2507 : o1.mul b75 b24=b2826 := by decide
theorem e2508 : o1.mul b75 b25=b2827 := by decide
theorem e2509 : o1.mul b75 b26=b359 := by decide
theorem e2510 : o1.scale b75 b740=b2835 := @scale_cons V1 _ o1 b75 b26 b359 (List.nil : V2) (List.nil : V2) b2835 e2509 e2374 (by rfl)
theorem e2511 : o1.scale b75 b738=b2834 := @scale_cons V1 _ o1 b75 b25 b2827 b740 b2835 b2834 e2508 e2510 (by rfl)
theorem e2512 : o1.scale b75 b736=b2833 := @scale_cons V1 _ o1 b75 b24 b2826 b738 b2834 b2833 e2507 e2511 (by rfl)
theorem e2513 : o1.scale b75 b734=b2832 := @scale_cons V1 _ o1 b75 b23 b2825 b736 b2833 b2832 e2506 e2512 (by rfl)
theorem e2514 : o1.scale b75 b732=b2831 := @scale_cons V1 _ o1 b75 b22 b2824 b734 b2832 b2831 e2505 e2513 (by rfl)
theorem e2515 : o1.scale b75 b730=b2830 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b732 b2831 b2830 e2367 e2514 (by rfl)
theorem e2516 : o1.scale b75 b728=b2829 := @scale_cons V1 _ o1 b75 b21 b2818 b730 b2830 b2829 e2504 e2515 (by rfl)
theorem e2517 : o1.scale b75 b27=b2828 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b728 b2829 b2828 e2367 e2516 (by rfl)
theorem e2518 : o2.add b2828 (List.nil : V2)=b2828 := by rfl
theorem e2519 : o2.mul b2718 b27=b2828 := @mul_cons V1 _ o1 b75 (List.nil : V2) b27 (List.nil : V2) b2828 (List.nil : V2) b2828 e140 e2517 (by rfl) e2518
theorem e2520 : o1.mul b74 b21=b2812 := by decide
theorem e2521 : o1.mul b74 b22=b2819 := by decide
theorem e2522 : o1.mul b74 b23=b2836 := by decide
theorem e2523 : o1.mul b74 b24=b2837 := by decide
theorem e2524 : o1.mul b74 b25=b2838 := by decide
theorem e2525 : o1.mul b74 b26=b2839 := by decide
theorem e2526 : o1.scale b74 b740=b2847 := @scale_cons V1 _ o1 b74 b26 b2839 (List.nil : V2) (List.nil : V2) b2847 e2525 e2391 (by rfl)
theorem e2527 : o1.scale b74 b738=b2846 := @scale_cons V1 _ o1 b74 b25 b2838 b740 b2847 b2846 e2524 e2526 (by rfl)
theorem e2528 : o1.scale b74 b736=b2845 := @scale_cons V1 _ o1 b74 b24 b2837 b738 b2846 b2845 e2523 e2527 (by rfl)
theorem e2529 : o1.scale b74 b734=b2844 := @scale_cons V1 _ o1 b74 b23 b2836 b736 b2845 b2844 e2522 e2528 (by rfl)
theorem e2530 : o1.scale b74 b732=b2843 := @scale_cons V1 _ o1 b74 b22 b2819 b734 b2844 b2843 e2521 e2529 (by rfl)
theorem e2531 : o1.scale b74 b730=b2842 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b732 b2843 b2842 e2384 e2530 (by rfl)
theorem e2532 : o1.scale b74 b728=b2841 := @scale_cons V1 _ o1 b74 b21 b2812 b730 b2842 b2841 e2520 e2531 (by rfl)
theorem e2533 : o1.scale b74 b27=b2840 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b728 b2841 b2840 e2384 e2532 (by rfl)
theorem e2534 : o1.add b2812 (List.nil : V1)=b2812 := by rfl
theorem e2535 : o1.add (List.nil : V1) b2818=b2818 := by rfl
theorem e2536 : o1.add b2819 (List.nil : V1)=b2819 := by rfl
theorem e2537 : o1.add b2836 b2824=b2820 := by decide
theorem e2538 : o1.add b2837 b2825=b2821 := by decide
theorem e2539 : o1.add b2838 b2826=b2822 := by decide
theorem e2540 : o1.add b2839 b2827=b2639 := by decide
theorem e2541 : o2.add (List.nil : V2) b2835=b2835 := by rfl
theorem e2542 : o2.add b2847 b2834=b2855 := @add_cons V1 _ o1 b2839 b2827 b2639 (List.nil : V2) b2835 b2835 b2855 e2540 e2541 (by rfl)
theorem e2543 : o2.add b2846 b2833=b2854 := @add_cons V1 _ o1 b2838 b2826 b2822 b2847 b2834 b2855 b2854 e2539 e2542 (by rfl)
theorem e2544 : o2.add b2845 b2832=b2853 := @add_cons V1 _ o1 b2837 b2825 b2821 b2846 b2833 b2854 b2853 e2538 e2543 (by rfl)
theorem e2545 : o2.add b2844 b2831=b2852 := @add_cons V1 _ o1 b2836 b2824 b2820 b2845 b2832 b2853 b2852 e2537 e2544 (by rfl)
theorem e2546 : o2.add b2843 b2830=b2851 := @add_cons V1 _ o1 b2819 (List.nil : V1) b2819 b2844 b2831 b2852 b2851 e2536 e2545 (by rfl)
theorem e2547 : o2.add b2842 b2829=b2850 := @add_cons V1 _ o1 (List.nil : V1) b2818 b2818 b2843 b2830 b2851 b2850 e2535 e2546 (by rfl)
theorem e2548 : o2.add b2841 b2828=b2849 := @add_cons V1 _ o1 b2812 (List.nil : V1) b2812 b2842 b2829 b2850 b2849 e2534 e2547 (by rfl)
theorem e2549 : o2.add b2840 b2848=b2823 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2841 b2828 b2849 b2823 e34 e2548 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
