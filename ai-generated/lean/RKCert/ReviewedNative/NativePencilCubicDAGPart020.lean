module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart019

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e2850 : o1.mul b73 b39=b3102 := by decide
theorem e2851 : o1.mul b73 b40=b3103 := by decide
theorem e2852 : o1.scale b73 b998=b3113 := @scale_cons V1 _ o1 b73 b40 b3103 (List.nil : V2) (List.nil : V2) b3113 e2851 e2421 (by rfl)
theorem e2853 : o1.scale b73 b996=b3112 := @scale_cons V1 _ o1 b73 b39 b3102 b998 b3113 b3112 e2850 e2852 (by rfl)
theorem e2854 : o1.scale b73 b994=b3111 := @scale_cons V1 _ o1 b73 b38 b3101 b996 b3112 b3111 e2849 e2853 (by rfl)
theorem e2855 : o1.scale b73 b992=b3110 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b994 b3111 b3110 e2414 e2854 (by rfl)
theorem e2856 : o1.scale b73 b990=b3109 := @scale_cons V1 _ o1 b73 b37 b3100 b992 b3110 b3109 e2848 e2855 (by rfl)
theorem e2857 : o1.scale b73 b988=b3108 := @scale_cons V1 _ o1 b73 b36 b3099 b990 b3109 b3108 e2847 e2856 (by rfl)
theorem e2858 : o1.scale b73 b986=b3107 := @scale_cons V1 _ o1 b73 b35 b3049 b988 b3108 b3107 e2846 e2857 (by rfl)
theorem e2859 : o1.scale b73 b984=b3106 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b986 b3107 b3106 e2414 e2858 (by rfl)
theorem e2860 : o1.scale b73 b982=b3105 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b984 b3106 b3105 e2414 e2859 (by rfl)
theorem e2861 : o1.scale b73 b41=b3104 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b982 b3105 b3104 e2414 e2860 (by rfl)
theorem e2862 : o1.add b3049 (List.nil : V1)=b3049 := by rfl
theorem e2863 : o1.add b3099 b3055=b3050 := by decide
theorem e2864 : o1.add b3100 b3056=b3045 := by decide
theorem e2865 : o1.add (List.nil : V1) b3051=b3051 := by rfl
theorem e2866 : o1.add b3101 b3057=b3052 := by decide
theorem e2867 : o1.add b3102 b3058=b3053 := by decide
theorem e2868 : o1.add b3103 b3059=b2660 := by decide
theorem e2869 : o2.add (List.nil : V2) b3098=b3098 := by rfl
theorem e2870 : o2.add b3113 b3097=b3123 := @add_cons V1 _ o1 b3103 b3059 b2660 (List.nil : V2) b3098 b3098 b3123 e2868 e2869 (by rfl)
theorem e2871 : o2.add b3112 b3096=b3122 := @add_cons V1 _ o1 b3102 b3058 b3053 b3113 b3097 b3123 b3122 e2867 e2870 (by rfl)
theorem e2872 : o2.add b3111 b3095=b3121 := @add_cons V1 _ o1 b3101 b3057 b3052 b3112 b3096 b3122 b3121 e2866 e2871 (by rfl)
theorem e2873 : o2.add b3110 b3094=b3120 := @add_cons V1 _ o1 (List.nil : V1) b3051 b3051 b3111 b3095 b3121 b3120 e2865 e2872 (by rfl)
theorem e2874 : o2.add b3109 b3093=b3119 := @add_cons V1 _ o1 b3100 b3056 b3045 b3110 b3094 b3120 b3119 e2864 e2873 (by rfl)
theorem e2875 : o2.add b3108 b3092=b3118 := @add_cons V1 _ o1 b3099 b3055 b3050 b3109 b3093 b3119 b3118 e2863 e2874 (by rfl)
theorem e2876 : o2.add b3107 b3091=b3117 := @add_cons V1 _ o1 b3049 (List.nil : V1) b3049 b3108 b3092 b3118 b3117 e2862 e2875 (by rfl)
theorem e2877 : o2.add b3106 b3090=b3116 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3107 b3091 b3117 b3116 e34 e2876 (by rfl)
theorem e2878 : o2.add b3105 b3060=b3115 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3106 b3090 b3116 b3115 e34 e2877 (by rfl)
theorem e2879 : o2.add b3104 b3114=b3054 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3105 b3060 b3115 b3054 e34 e2878 (by rfl)
theorem e2880 : o2.mul b2704 b41=b3054 := @mul_cons V1 _ o1 b73 b2711 b41 b3060 b3104 b3114 b3054 e2845 e2861 (by rfl) e2879
theorem e2881 : o1.mul b72 b35=b3043 := by decide
theorem e2882 : o1.mul b72 b36=b3124 := by decide
theorem e2883 : o1.mul b72 b37=b3125 := by decide
theorem e2884 : o1.mul b72 b38=b3126 := by decide
theorem e2885 : o1.mul b72 b39=b3127 := by decide
theorem e2886 : o1.mul b72 b40=b3128 := by decide
theorem e2887 : o1.scale b72 b998=b3138 := @scale_cons V1 _ o1 b72 b40 b3128 (List.nil : V2) (List.nil : V2) b3138 e2886 e2451 (by rfl)
theorem e2888 : o1.scale b72 b996=b3137 := @scale_cons V1 _ o1 b72 b39 b3127 b998 b3138 b3137 e2885 e2887 (by rfl)
theorem e2889 : o1.scale b72 b994=b3136 := @scale_cons V1 _ o1 b72 b38 b3126 b996 b3137 b3136 e2884 e2888 (by rfl)
theorem e2890 : o1.scale b72 b992=b3135 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b994 b3136 b3135 e2444 e2889 (by rfl)
theorem e2891 : o1.scale b72 b990=b3134 := @scale_cons V1 _ o1 b72 b37 b3125 b992 b3135 b3134 e2883 e2890 (by rfl)
theorem e2892 : o1.scale b72 b988=b3133 := @scale_cons V1 _ o1 b72 b36 b3124 b990 b3134 b3133 e2882 e2891 (by rfl)
theorem e2893 : o1.scale b72 b986=b3132 := @scale_cons V1 _ o1 b72 b35 b3043 b988 b3133 b3132 e2881 e2892 (by rfl)
theorem e2894 : o1.scale b72 b984=b3131 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b986 b3132 b3131 e2444 e2893 (by rfl)
theorem e2895 : o1.scale b72 b982=b3130 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b984 b3131 b3130 e2444 e2894 (by rfl)
theorem e2896 : o1.scale b72 b41=b3129 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b982 b3130 b3129 e2444 e2895 (by rfl)
theorem e2897 : o1.add b3043 (List.nil : V1)=b3043 := by rfl
theorem e2898 : o1.add b3124 b3049=b3044 := by decide
theorem e2899 : o1.add b3125 b3050=b2655 := by decide
theorem e2900 : o1.add (List.nil : V1) b3045=b3045 := by rfl
theorem e2901 : o1.add b3126 b3051=b3046 := by decide
theorem e2902 : o1.add b3127 b3052=b3047 := by decide
theorem e2903 : o1.add b3128 b3053=b2659 := by decide
theorem e2904 : o2.add (List.nil : V2) b3123=b3123 := by rfl
theorem e2905 : o2.add b3138 b3122=b3148 := @add_cons V1 _ o1 b3128 b3053 b2659 (List.nil : V2) b3123 b3123 b3148 e2903 e2904 (by rfl)
theorem e2906 : o2.add b3137 b3121=b3147 := @add_cons V1 _ o1 b3127 b3052 b3047 b3138 b3122 b3148 b3147 e2902 e2905 (by rfl)
theorem e2907 : o2.add b3136 b3120=b3146 := @add_cons V1 _ o1 b3126 b3051 b3046 b3137 b3121 b3147 b3146 e2901 e2906 (by rfl)
theorem e2908 : o2.add b3135 b3119=b3145 := @add_cons V1 _ o1 (List.nil : V1) b3045 b3045 b3136 b3120 b3146 b3145 e2900 e2907 (by rfl)
theorem e2909 : o2.add b3134 b3118=b3144 := @add_cons V1 _ o1 b3125 b3050 b2655 b3135 b3119 b3145 b3144 e2899 e2908 (by rfl)
theorem e2910 : o2.add b3133 b3117=b3143 := @add_cons V1 _ o1 b3124 b3049 b3044 b3134 b3118 b3144 b3143 e2898 e2909 (by rfl)
theorem e2911 : o2.add b3132 b3116=b3142 := @add_cons V1 _ o1 b3043 (List.nil : V1) b3043 b3133 b3117 b3143 b3142 e2897 e2910 (by rfl)
theorem e2912 : o2.add b3131 b3115=b3141 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3132 b3116 b3142 b3141 e34 e2911 (by rfl)
theorem e2913 : o2.add b3130 b3054=b3140 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3131 b3115 b3141 b3140 e34 e2912 (by rfl)
theorem e2914 : o2.add b3129 b3139=b3048 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3130 b3054 b3140 b3048 e34 e2913 (by rfl)
theorem e2915 : o2.mul b2697 b41=b3048 := @mul_cons V1 _ o1 b72 b2704 b41 b3054 b3129 b3139 b3048 e2880 e2896 (by rfl) e2914
theorem e2916 : o1.mul b71 b35=b2652 := by decide
theorem e2917 : o1.mul b71 b36=b3149 := by decide
theorem e2918 : o1.mul b71 b37=b3150 := by decide
theorem e2919 : o1.mul b71 b38=b3151 := by decide
theorem e2920 : o1.mul b71 b39=b3152 := by decide
theorem e2921 : o1.mul b71 b40=b3153 := by decide
theorem e2922 : o1.scale b71 b998=b3163 := @scale_cons V1 _ o1 b71 b40 b3153 (List.nil : V2) (List.nil : V2) b3163 e2921 e2481 (by rfl)
theorem e2923 : o1.scale b71 b996=b3162 := @scale_cons V1 _ o1 b71 b39 b3152 b998 b3163 b3162 e2920 e2922 (by rfl)
theorem e2924 : o1.scale b71 b994=b3161 := @scale_cons V1 _ o1 b71 b38 b3151 b996 b3162 b3161 e2919 e2923 (by rfl)
theorem e2925 : o1.scale b71 b992=b3160 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b994 b3161 b3160 e2474 e2924 (by rfl)
theorem e2926 : o1.scale b71 b990=b3159 := @scale_cons V1 _ o1 b71 b37 b3150 b992 b3160 b3159 e2918 e2925 (by rfl)
theorem e2927 : o1.scale b71 b988=b3158 := @scale_cons V1 _ o1 b71 b36 b3149 b990 b3159 b3158 e2917 e2926 (by rfl)
theorem e2928 : o1.scale b71 b986=b3157 := @scale_cons V1 _ o1 b71 b35 b2652 b988 b3158 b3157 e2916 e2927 (by rfl)
theorem e2929 : o1.scale b71 b984=b3156 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b986 b3157 b3156 e2474 e2928 (by rfl)
theorem e2930 : o1.scale b71 b982=b3155 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b984 b3156 b3155 e2474 e2929 (by rfl)
theorem e2931 : o1.scale b71 b41=b3154 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b982 b3155 b3154 e2474 e2930 (by rfl)
theorem e2932 : o1.add b2652 (List.nil : V1)=b2652 := by rfl
theorem e2933 : o1.add b3149 b3043=b2653 := by decide
theorem e2934 : o1.add b3150 b3044=b2654 := by decide
theorem e2935 : o1.add (List.nil : V1) b2655=b2655 := by rfl
theorem e2936 : o1.add b3151 b3045=b2656 := by decide
theorem e2937 : o1.add b3152 b3046=b2657 := by decide
theorem e2938 : o1.add b3153 b3047=b2658 := by decide
theorem e2939 : o2.add (List.nil : V2) b3148=b3148 := by rfl
theorem e2940 : o2.add b3163 b3147=b3173 := @add_cons V1 _ o1 b3153 b3047 b2658 (List.nil : V2) b3148 b3148 b3173 e2938 e2939 (by rfl)
theorem e2941 : o2.add b3162 b3146=b3172 := @add_cons V1 _ o1 b3152 b3046 b2657 b3163 b3147 b3173 b3172 e2937 e2940 (by rfl)
theorem e2942 : o2.add b3161 b3145=b3171 := @add_cons V1 _ o1 b3151 b3045 b2656 b3162 b3146 b3172 b3171 e2936 e2941 (by rfl)
theorem e2943 : o2.add b3160 b3144=b3170 := @add_cons V1 _ o1 (List.nil : V1) b2655 b2655 b3161 b3145 b3171 b3170 e2935 e2942 (by rfl)
theorem e2944 : o2.add b3159 b3143=b3169 := @add_cons V1 _ o1 b3150 b3044 b2654 b3160 b3144 b3170 b3169 e2934 e2943 (by rfl)
theorem e2945 : o2.add b3158 b3142=b3168 := @add_cons V1 _ o1 b3149 b3043 b2653 b3159 b3143 b3169 b3168 e2933 e2944 (by rfl)
theorem e2946 : o2.add b3157 b3141=b3167 := @add_cons V1 _ o1 b2652 (List.nil : V1) b2652 b3158 b3142 b3168 b3167 e2932 e2945 (by rfl)
theorem e2947 : o2.add b3156 b3140=b3166 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3157 b3141 b3167 b3166 e34 e2946 (by rfl)
theorem e2948 : o2.add b3155 b3048=b3165 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3156 b3140 b3166 b3165 e34 e2947 (by rfl)
theorem e2949 : o2.add b3154 b3164=b2662 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3155 b3048 b3165 b2662 e34 e2948 (by rfl)
theorem e2950 : o2.mul b76 b41=b2662 := @mul_cons V1 _ o1 b71 b2697 b41 b3048 b3154 b3164 b2662 e2915 e2931 (by rfl) e2949
theorem e2951 : o1.mul b75 b42=b3190 := by decide
theorem e2952 : o1.mul b75 b43=b3191 := by decide
theorem e2953 : o1.mul b75 b44=b3187 := by decide
theorem e2954 : o1.mul b75 b45=b3192 := by decide
theorem e2955 : o1.mul b75 b46=b400 := by decide
theorem e2956 : o1.scale b75 b1138=b3203 := @scale_cons V1 _ o1 b75 b46 b400 (List.nil : V2) (List.nil : V2) b3203 e2955 e2374 (by rfl)
theorem e2957 : o1.scale b75 b1136=b3202 := @scale_cons V1 _ o1 b75 b45 b3192 b1138 b3203 b3202 e2954 e2956 (by rfl)
theorem e2958 : o1.scale b75 b1134=b3201 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1136 b3202 b3201 e2367 e2957 (by rfl)
theorem e2959 : o1.scale b75 b1132=b3200 := @scale_cons V1 _ o1 b75 b44 b3187 b1134 b3201 b3200 e2953 e2958 (by rfl)
theorem e2960 : o1.scale b75 b1130=b3199 := @scale_cons V1 _ o1 b75 b43 b3191 b1132 b3200 b3199 e2952 e2959 (by rfl)
theorem e2961 : o1.scale b75 b1128=b3198 := @scale_cons V1 _ o1 b75 b42 b3190 b1130 b3199 b3198 e2951 e2960 (by rfl)
theorem e2962 : o1.scale b75 b1126=b3197 := @scale_cons V1 _ o1 b75 b18 b2723 b1128 b3198 b3197 e2372 e2961 (by rfl)
theorem e2963 : o1.scale b75 b1124=b3196 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1126 b3197 b3196 e2367 e2962 (by rfl)
theorem e2964 : o1.scale b75 b1122=b3195 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1124 b3196 b3195 e2367 e2963 (by rfl)
theorem e2965 : o1.scale b75 b1120=b3194 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1122 b3195 b3194 e2367 e2964 (by rfl)
theorem e2966 : o1.scale b75 b47=b3193 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1120 b3194 b3193 e2367 e2965 (by rfl)
theorem e2967 : o2.add b3193 (List.nil : V2)=b3193 := by rfl
theorem e2968 : o2.mul b2718 b47=b3193 := @mul_cons V1 _ o1 b75 (List.nil : V2) b47 (List.nil : V2) b3193 (List.nil : V2) b3193 e590 e2966 (by rfl) e2967
theorem e2969 : o1.mul b74 b42=b3204 := by decide
theorem e2970 : o1.mul b74 b43=b3205 := by decide
theorem e2971 : o1.mul b74 b44=b3206 := by decide
theorem e2972 : o1.mul b74 b45=b3188 := by decide
theorem e2973 : o1.mul b74 b46=b3207 := by decide
theorem e2974 : o1.scale b74 b1138=b3218 := @scale_cons V1 _ o1 b74 b46 b3207 (List.nil : V2) (List.nil : V2) b3218 e2973 e2391 (by rfl)
theorem e2975 : o1.scale b74 b1136=b3217 := @scale_cons V1 _ o1 b74 b45 b3188 b1138 b3218 b3217 e2972 e2974 (by rfl)
theorem e2976 : o1.scale b74 b1134=b3216 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1136 b3217 b3216 e2384 e2975 (by rfl)
theorem e2977 : o1.scale b74 b1132=b3215 := @scale_cons V1 _ o1 b74 b44 b3206 b1134 b3216 b3215 e2971 e2976 (by rfl)
theorem e2978 : o1.scale b74 b1130=b3214 := @scale_cons V1 _ o1 b74 b43 b3205 b1132 b3215 b3214 e2970 e2977 (by rfl)
theorem e2979 : o1.scale b74 b1128=b3213 := @scale_cons V1 _ o1 b74 b42 b3204 b1130 b3214 b3213 e2969 e2978 (by rfl)
theorem e2980 : o1.scale b74 b1126=b3212 := @scale_cons V1 _ o1 b74 b18 b2734 b1128 b3213 b3212 e2389 e2979 (by rfl)
theorem e2981 : o1.scale b74 b1124=b3211 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1126 b3212 b3211 e2384 e2980 (by rfl)
theorem e2982 : o1.scale b74 b1122=b3210 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1124 b3211 b3210 e2384 e2981 (by rfl)
theorem e2983 : o1.scale b74 b1120=b3209 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1122 b3210 b3209 e2384 e2982 (by rfl)
theorem e2984 : o1.scale b74 b47=b3208 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1120 b3209 b3208 e2384 e2983 (by rfl)
theorem e2985 : o1.add b2734 (List.nil : V1)=b2734 := by rfl
theorem e2986 : o1.add b3204 b2723=b3185 := by decide
theorem e2987 : o1.add b3205 b3190=b3186 := by decide
theorem e2988 : o1.add b3206 b3191=b3182 := by decide
theorem e2989 : o1.add (List.nil : V1) b3187=b3187 := by rfl
theorem e2990 : o1.add b3188 (List.nil : V1)=b3188 := by rfl
theorem e2991 : o1.add b3207 b3192=b2672 := by decide
theorem e2992 : o2.add (List.nil : V2) b3203=b3203 := by rfl
theorem e2993 : o2.add b3218 b3202=b3229 := @add_cons V1 _ o1 b3207 b3192 b2672 (List.nil : V2) b3203 b3203 b3229 e2991 e2992 (by rfl)
theorem e2994 : o2.add b3217 b3201=b3228 := @add_cons V1 _ o1 b3188 (List.nil : V1) b3188 b3218 b3202 b3229 b3228 e2990 e2993 (by rfl)
theorem e2995 : o2.add b3216 b3200=b3227 := @add_cons V1 _ o1 (List.nil : V1) b3187 b3187 b3217 b3201 b3228 b3227 e2989 e2994 (by rfl)
theorem e2996 : o2.add b3215 b3199=b3226 := @add_cons V1 _ o1 b3206 b3191 b3182 b3216 b3200 b3227 b3226 e2988 e2995 (by rfl)
theorem e2997 : o2.add b3214 b3198=b3225 := @add_cons V1 _ o1 b3205 b3190 b3186 b3215 b3199 b3226 b3225 e2987 e2996 (by rfl)
theorem e2998 : o2.add b3213 b3197=b3224 := @add_cons V1 _ o1 b3204 b2723 b3185 b3214 b3198 b3225 b3224 e2986 e2997 (by rfl)
theorem e2999 : o2.add b3212 b3196=b3223 := @add_cons V1 _ o1 b2734 (List.nil : V1) b2734 b3213 b3197 b3224 b3223 e2985 e2998 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
