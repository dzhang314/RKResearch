module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart018

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e2700 : o1.scale b73 b864=b2986 := @scale_cons V1 _ o1 b73 b33 b2977 (List.nil : V2) (List.nil : V2) b2986 e2699 e2421 (by rfl)
theorem e2701 : o1.scale b73 b862=b2985 := @scale_cons V1 _ o1 b73 b32 b2976 b864 b2986 b2985 e2698 e2700 (by rfl)
theorem e2702 : o1.scale b73 b860=b2984 := @scale_cons V1 _ o1 b73 b31 b2975 b862 b2985 b2984 e2697 e2701 (by rfl)
theorem e2703 : o1.scale b73 b858=b2983 := @scale_cons V1 _ o1 b73 b30 b2974 b860 b2984 b2983 e2696 e2702 (by rfl)
theorem e2704 : o1.scale b73 b856=b2982 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b858 b2983 b2982 e2414 e2703 (by rfl)
theorem e2705 : o1.scale b73 b854=b2981 := @scale_cons V1 _ o1 b73 b29 b2973 b856 b2982 b2981 e2695 e2704 (by rfl)
theorem e2706 : o1.scale b73 b852=b2980 := @scale_cons V1 _ o1 b73 b28 b2926 b854 b2981 b2980 e2694 e2705 (by rfl)
theorem e2707 : o1.scale b73 b850=b2979 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b852 b2980 b2979 e2414 e2706 (by rfl)
theorem e2708 : o1.scale b73 b34=b2978 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b850 b2979 b2978 e2414 e2707 (by rfl)
theorem e2709 : o1.add b2926 (List.nil : V1)=b2926 := by rfl
theorem e2710 : o1.add b2973 b2932=b2921 := by decide
theorem e2711 : o1.add (List.nil : V1) b2927=b2927 := by rfl
theorem e2712 : o1.add b2974 b2933=b2928 := by decide
theorem e2713 : o1.add b2975 b2934=b2929 := by decide
theorem e2714 : o1.add b2976 b2935=b2930 := by decide
theorem e2715 : o1.add b2977 b2936=b2649 := by decide
theorem e2716 : o2.add (List.nil : V2) b2972=b2972 := by rfl
theorem e2717 : o2.add b2986 b2971=b2995 := @add_cons V1 _ o1 b2977 b2936 b2649 (List.nil : V2) b2972 b2972 b2995 e2715 e2716 (by rfl)
theorem e2718 : o2.add b2985 b2970=b2994 := @add_cons V1 _ o1 b2976 b2935 b2930 b2986 b2971 b2995 b2994 e2714 e2717 (by rfl)
theorem e2719 : o2.add b2984 b2969=b2993 := @add_cons V1 _ o1 b2975 b2934 b2929 b2985 b2970 b2994 b2993 e2713 e2718 (by rfl)
theorem e2720 : o2.add b2983 b2968=b2992 := @add_cons V1 _ o1 b2974 b2933 b2928 b2984 b2969 b2993 b2992 e2712 e2719 (by rfl)
theorem e2721 : o2.add b2982 b2967=b2991 := @add_cons V1 _ o1 (List.nil : V1) b2927 b2927 b2983 b2968 b2992 b2991 e2711 e2720 (by rfl)
theorem e2722 : o2.add b2981 b2966=b2990 := @add_cons V1 _ o1 b2973 b2932 b2921 b2982 b2967 b2991 b2990 e2710 e2721 (by rfl)
theorem e2723 : o2.add b2980 b2965=b2989 := @add_cons V1 _ o1 b2926 (List.nil : V1) b2926 b2981 b2966 b2990 b2989 e2709 e2722 (by rfl)
theorem e2724 : o2.add b2979 b2937=b2988 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2980 b2965 b2989 b2988 e34 e2723 (by rfl)
theorem e2725 : o2.add b2978 b2987=b2931 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2979 b2937 b2988 b2931 e34 e2724 (by rfl)
theorem e2726 : o2.mul b2704 b34=b2931 := @mul_cons V1 _ o1 b73 b2711 b34 b2937 b2978 b2987 b2931 e2693 e2708 (by rfl) e2725
theorem e2727 : o1.mul b72 b28=b2920 := by decide
theorem e2728 : o1.mul b72 b29=b2996 := by decide
theorem e2729 : o1.mul b72 b30=b2997 := by decide
theorem e2730 : o1.mul b72 b31=b2998 := by decide
theorem e2731 : o1.mul b72 b32=b2999 := by decide
theorem e2732 : o1.mul b72 b33=b3000 := by decide
theorem e2733 : o1.scale b72 b864=b3009 := @scale_cons V1 _ o1 b72 b33 b3000 (List.nil : V2) (List.nil : V2) b3009 e2732 e2451 (by rfl)
theorem e2734 : o1.scale b72 b862=b3008 := @scale_cons V1 _ o1 b72 b32 b2999 b864 b3009 b3008 e2731 e2733 (by rfl)
theorem e2735 : o1.scale b72 b860=b3007 := @scale_cons V1 _ o1 b72 b31 b2998 b862 b3008 b3007 e2730 e2734 (by rfl)
theorem e2736 : o1.scale b72 b858=b3006 := @scale_cons V1 _ o1 b72 b30 b2997 b860 b3007 b3006 e2729 e2735 (by rfl)
theorem e2737 : o1.scale b72 b856=b3005 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b858 b3006 b3005 e2444 e2736 (by rfl)
theorem e2738 : o1.scale b72 b854=b3004 := @scale_cons V1 _ o1 b72 b29 b2996 b856 b3005 b3004 e2728 e2737 (by rfl)
theorem e2739 : o1.scale b72 b852=b3003 := @scale_cons V1 _ o1 b72 b28 b2920 b854 b3004 b3003 e2727 e2738 (by rfl)
theorem e2740 : o1.scale b72 b850=b3002 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b852 b3003 b3002 e2444 e2739 (by rfl)
theorem e2741 : o1.scale b72 b34=b3001 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b850 b3002 b3001 e2444 e2740 (by rfl)
theorem e2742 : o1.add b2920 (List.nil : V1)=b2920 := by rfl
theorem e2743 : o1.add b2996 b2926=b2643 := by decide
theorem e2744 : o1.add (List.nil : V1) b2921=b2921 := by rfl
theorem e2745 : o1.add b2997 b2927=b2922 := by decide
theorem e2746 : o1.add b2998 b2928=b2923 := by decide
theorem e2747 : o1.add b2999 b2929=b2924 := by decide
theorem e2748 : o1.add b3000 b2930=b2648 := by decide
theorem e2749 : o2.add (List.nil : V2) b2995=b2995 := by rfl
theorem e2750 : o2.add b3009 b2994=b3018 := @add_cons V1 _ o1 b3000 b2930 b2648 (List.nil : V2) b2995 b2995 b3018 e2748 e2749 (by rfl)
theorem e2751 : o2.add b3008 b2993=b3017 := @add_cons V1 _ o1 b2999 b2929 b2924 b3009 b2994 b3018 b3017 e2747 e2750 (by rfl)
theorem e2752 : o2.add b3007 b2992=b3016 := @add_cons V1 _ o1 b2998 b2928 b2923 b3008 b2993 b3017 b3016 e2746 e2751 (by rfl)
theorem e2753 : o2.add b3006 b2991=b3015 := @add_cons V1 _ o1 b2997 b2927 b2922 b3007 b2992 b3016 b3015 e2745 e2752 (by rfl)
theorem e2754 : o2.add b3005 b2990=b3014 := @add_cons V1 _ o1 (List.nil : V1) b2921 b2921 b3006 b2991 b3015 b3014 e2744 e2753 (by rfl)
theorem e2755 : o2.add b3004 b2989=b3013 := @add_cons V1 _ o1 b2996 b2926 b2643 b3005 b2990 b3014 b3013 e2743 e2754 (by rfl)
theorem e2756 : o2.add b3003 b2988=b3012 := @add_cons V1 _ o1 b2920 (List.nil : V1) b2920 b3004 b2989 b3013 b3012 e2742 e2755 (by rfl)
theorem e2757 : o2.add b3002 b2931=b3011 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3003 b2988 b3012 b3011 e34 e2756 (by rfl)
theorem e2758 : o2.add b3001 b3010=b2925 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3002 b2931 b3011 b2925 e34 e2757 (by rfl)
theorem e2759 : o2.mul b2697 b34=b2925 := @mul_cons V1 _ o1 b72 b2704 b34 b2931 b3001 b3010 b2925 e2726 e2741 (by rfl) e2758
theorem e2760 : o1.mul b71 b28=b2641 := by decide
theorem e2761 : o1.mul b71 b29=b3019 := by decide
theorem e2762 : o1.mul b71 b30=b3020 := by decide
theorem e2763 : o1.mul b71 b31=b3021 := by decide
theorem e2764 : o1.mul b71 b32=b3022 := by decide
theorem e2765 : o1.mul b71 b33=b3023 := by decide
theorem e2766 : o1.scale b71 b864=b3032 := @scale_cons V1 _ o1 b71 b33 b3023 (List.nil : V2) (List.nil : V2) b3032 e2765 e2481 (by rfl)
theorem e2767 : o1.scale b71 b862=b3031 := @scale_cons V1 _ o1 b71 b32 b3022 b864 b3032 b3031 e2764 e2766 (by rfl)
theorem e2768 : o1.scale b71 b860=b3030 := @scale_cons V1 _ o1 b71 b31 b3021 b862 b3031 b3030 e2763 e2767 (by rfl)
theorem e2769 : o1.scale b71 b858=b3029 := @scale_cons V1 _ o1 b71 b30 b3020 b860 b3030 b3029 e2762 e2768 (by rfl)
theorem e2770 : o1.scale b71 b856=b3028 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b858 b3029 b3028 e2474 e2769 (by rfl)
theorem e2771 : o1.scale b71 b854=b3027 := @scale_cons V1 _ o1 b71 b29 b3019 b856 b3028 b3027 e2761 e2770 (by rfl)
theorem e2772 : o1.scale b71 b852=b3026 := @scale_cons V1 _ o1 b71 b28 b2641 b854 b3027 b3026 e2760 e2771 (by rfl)
theorem e2773 : o1.scale b71 b850=b3025 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b852 b3026 b3025 e2474 e2772 (by rfl)
theorem e2774 : o1.scale b71 b34=b3024 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b850 b3025 b3024 e2474 e2773 (by rfl)
theorem e2775 : o1.add b2641 (List.nil : V1)=b2641 := by rfl
theorem e2776 : o1.add b3019 b2920=b2642 := by decide
theorem e2777 : o1.add (List.nil : V1) b2643=b2643 := by rfl
theorem e2778 : o1.add b3020 b2921=b2644 := by decide
theorem e2779 : o1.add b3021 b2922=b2645 := by decide
theorem e2780 : o1.add b3022 b2923=b2646 := by decide
theorem e2781 : o1.add b3023 b2924=b2647 := by decide
theorem e2782 : o2.add (List.nil : V2) b3018=b3018 := by rfl
theorem e2783 : o2.add b3032 b3017=b3041 := @add_cons V1 _ o1 b3023 b2924 b2647 (List.nil : V2) b3018 b3018 b3041 e2781 e2782 (by rfl)
theorem e2784 : o2.add b3031 b3016=b3040 := @add_cons V1 _ o1 b3022 b2923 b2646 b3032 b3017 b3041 b3040 e2780 e2783 (by rfl)
theorem e2785 : o2.add b3030 b3015=b3039 := @add_cons V1 _ o1 b3021 b2922 b2645 b3031 b3016 b3040 b3039 e2779 e2784 (by rfl)
theorem e2786 : o2.add b3029 b3014=b3038 := @add_cons V1 _ o1 b3020 b2921 b2644 b3030 b3015 b3039 b3038 e2778 e2785 (by rfl)
theorem e2787 : o2.add b3028 b3013=b3037 := @add_cons V1 _ o1 (List.nil : V1) b2643 b2643 b3029 b3014 b3038 b3037 e2777 e2786 (by rfl)
theorem e2788 : o2.add b3027 b3012=b3036 := @add_cons V1 _ o1 b3019 b2920 b2642 b3028 b3013 b3037 b3036 e2776 e2787 (by rfl)
theorem e2789 : o2.add b3026 b3011=b3035 := @add_cons V1 _ o1 b2641 (List.nil : V1) b2641 b3027 b3012 b3036 b3035 e2775 e2788 (by rfl)
theorem e2790 : o2.add b3025 b2925=b3034 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3026 b3011 b3035 b3034 e34 e2789 (by rfl)
theorem e2791 : o2.add b3024 b3033=b2651 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3025 b2925 b3034 b2651 e34 e2790 (by rfl)
theorem e2792 : o2.mul b76 b34=b2651 := @mul_cons V1 _ o1 b71 b2697 b34 b2925 b3024 b3033 b2651 e2759 e2774 (by rfl) e2791
theorem e2793 : o1.mul b75 b35=b3061 := by decide
theorem e2794 : o1.mul b75 b36=b3062 := by decide
theorem e2795 : o1.mul b75 b37=b3057 := by decide
theorem e2796 : o1.mul b75 b38=b3063 := by decide
theorem e2797 : o1.mul b75 b39=b3064 := by decide
theorem e2798 : o1.mul b75 b40=b386 := by decide
theorem e2799 : o1.scale b75 b998=b3074 := @scale_cons V1 _ o1 b75 b40 b386 (List.nil : V2) (List.nil : V2) b3074 e2798 e2374 (by rfl)
theorem e2800 : o1.scale b75 b996=b3073 := @scale_cons V1 _ o1 b75 b39 b3064 b998 b3074 b3073 e2797 e2799 (by rfl)
theorem e2801 : o1.scale b75 b994=b3072 := @scale_cons V1 _ o1 b75 b38 b3063 b996 b3073 b3072 e2796 e2800 (by rfl)
theorem e2802 : o1.scale b75 b992=b3071 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b994 b3072 b3071 e2367 e2801 (by rfl)
theorem e2803 : o1.scale b75 b990=b3070 := @scale_cons V1 _ o1 b75 b37 b3057 b992 b3071 b3070 e2795 e2802 (by rfl)
theorem e2804 : o1.scale b75 b988=b3069 := @scale_cons V1 _ o1 b75 b36 b3062 b990 b3070 b3069 e2794 e2803 (by rfl)
theorem e2805 : o1.scale b75 b986=b3068 := @scale_cons V1 _ o1 b75 b35 b3061 b988 b3069 b3068 e2793 e2804 (by rfl)
theorem e2806 : o1.scale b75 b984=b3067 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b986 b3068 b3067 e2367 e2805 (by rfl)
theorem e2807 : o1.scale b75 b982=b3066 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b984 b3067 b3066 e2367 e2806 (by rfl)
theorem e2808 : o1.scale b75 b41=b3065 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b982 b3066 b3065 e2367 e2807 (by rfl)
theorem e2809 : o2.add b3065 (List.nil : V2)=b3065 := by rfl
theorem e2810 : o2.mul b2718 b41=b3065 := @mul_cons V1 _ o1 b75 (List.nil : V2) b41 (List.nil : V2) b3065 (List.nil : V2) b3065 e431 e2808 (by rfl) e2809
theorem e2811 : o1.mul b74 b35=b3055 := by decide
theorem e2812 : o1.mul b74 b36=b3075 := by decide
theorem e2813 : o1.mul b74 b37=b3076 := by decide
theorem e2814 : o1.mul b74 b38=b3058 := by decide
theorem e2815 : o1.mul b74 b39=b3077 := by decide
theorem e2816 : o1.mul b74 b40=b3078 := by decide
theorem e2817 : o1.scale b74 b998=b3088 := @scale_cons V1 _ o1 b74 b40 b3078 (List.nil : V2) (List.nil : V2) b3088 e2816 e2391 (by rfl)
theorem e2818 : o1.scale b74 b996=b3087 := @scale_cons V1 _ o1 b74 b39 b3077 b998 b3088 b3087 e2815 e2817 (by rfl)
theorem e2819 : o1.scale b74 b994=b3086 := @scale_cons V1 _ o1 b74 b38 b3058 b996 b3087 b3086 e2814 e2818 (by rfl)
theorem e2820 : o1.scale b74 b992=b3085 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b994 b3086 b3085 e2384 e2819 (by rfl)
theorem e2821 : o1.scale b74 b990=b3084 := @scale_cons V1 _ o1 b74 b37 b3076 b992 b3085 b3084 e2813 e2820 (by rfl)
theorem e2822 : o1.scale b74 b988=b3083 := @scale_cons V1 _ o1 b74 b36 b3075 b990 b3084 b3083 e2812 e2821 (by rfl)
theorem e2823 : o1.scale b74 b986=b3082 := @scale_cons V1 _ o1 b74 b35 b3055 b988 b3083 b3082 e2811 e2822 (by rfl)
theorem e2824 : o1.scale b74 b984=b3081 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b986 b3082 b3081 e2384 e2823 (by rfl)
theorem e2825 : o1.scale b74 b982=b3080 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b984 b3081 b3080 e2384 e2824 (by rfl)
theorem e2826 : o1.scale b74 b41=b3079 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b982 b3080 b3079 e2384 e2825 (by rfl)
theorem e2827 : o1.add b3055 (List.nil : V1)=b3055 := by rfl
theorem e2828 : o1.add b3075 b3061=b3056 := by decide
theorem e2829 : o1.add b3076 b3062=b3051 := by decide
theorem e2830 : o1.add (List.nil : V1) b3057=b3057 := by rfl
theorem e2831 : o1.add b3058 (List.nil : V1)=b3058 := by rfl
theorem e2832 : o1.add b3077 b3063=b3059 := by decide
theorem e2833 : o1.add b3078 b3064=b2661 := by decide
theorem e2834 : o2.add (List.nil : V2) b3074=b3074 := by rfl
theorem e2835 : o2.add b3088 b3073=b3098 := @add_cons V1 _ o1 b3078 b3064 b2661 (List.nil : V2) b3074 b3074 b3098 e2833 e2834 (by rfl)
theorem e2836 : o2.add b3087 b3072=b3097 := @add_cons V1 _ o1 b3077 b3063 b3059 b3088 b3073 b3098 b3097 e2832 e2835 (by rfl)
theorem e2837 : o2.add b3086 b3071=b3096 := @add_cons V1 _ o1 b3058 (List.nil : V1) b3058 b3087 b3072 b3097 b3096 e2831 e2836 (by rfl)
theorem e2838 : o2.add b3085 b3070=b3095 := @add_cons V1 _ o1 (List.nil : V1) b3057 b3057 b3086 b3071 b3096 b3095 e2830 e2837 (by rfl)
theorem e2839 : o2.add b3084 b3069=b3094 := @add_cons V1 _ o1 b3076 b3062 b3051 b3085 b3070 b3095 b3094 e2829 e2838 (by rfl)
theorem e2840 : o2.add b3083 b3068=b3093 := @add_cons V1 _ o1 b3075 b3061 b3056 b3084 b3069 b3094 b3093 e2828 e2839 (by rfl)
theorem e2841 : o2.add b3082 b3067=b3092 := @add_cons V1 _ o1 b3055 (List.nil : V1) b3055 b3083 b3068 b3093 b3092 e2827 e2840 (by rfl)
theorem e2842 : o2.add b3081 b3066=b3091 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3082 b3067 b3092 b3091 e34 e2841 (by rfl)
theorem e2843 : o2.add b3080 b3065=b3090 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3081 b3066 b3091 b3090 e34 e2842 (by rfl)
theorem e2844 : o2.add b3079 b3089=b3060 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3080 b3065 b3090 b3060 e34 e2843 (by rfl)
theorem e2845 : o2.mul b2711 b41=b3060 := @mul_cons V1 _ o1 b74 b2718 b41 b3065 b3079 b3089 b3060 e2810 e2826 (by rfl) e2844
theorem e2846 : o1.mul b73 b35=b3049 := by decide
theorem e2847 : o1.mul b73 b36=b3099 := by decide
theorem e2848 : o1.mul b73 b37=b3100 := by decide
theorem e2849 : o1.mul b73 b38=b3101 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
