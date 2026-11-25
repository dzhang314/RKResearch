module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart020

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3000 : o2.add b3211 b3195=b3222 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3212 b3196 b3223 b3222 e34 e2999 (by rfl)
theorem e3001 : o2.add b3210 b3194=b3221 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3211 b3195 b3222 b3221 e34 e3000 (by rfl)
theorem e3002 : o2.add b3209 b3193=b3220 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3210 b3194 b3221 b3220 e34 e3001 (by rfl)
theorem e3003 : o2.add b3208 b3219=b3189 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3209 b3193 b3220 b3189 e34 e3002 (by rfl)
theorem e3004 : o2.mul b2711 b47=b3189 := @mul_cons V1 _ o1 b74 b2718 b47 b3193 b3208 b3219 b3189 e2968 e2984 (by rfl) e3003
theorem e3005 : o1.mul b73 b42=b3230 := by decide
theorem e3006 : o1.mul b73 b43=b3231 := by decide
theorem e3007 : o1.mul b73 b44=b3232 := by decide
theorem e3008 : o1.mul b73 b45=b3233 := by decide
theorem e3009 : o1.mul b73 b46=b3234 := by decide
theorem e3010 : o1.scale b73 b1138=b3245 := @scale_cons V1 _ o1 b73 b46 b3234 (List.nil : V2) (List.nil : V2) b3245 e3009 e2421 (by rfl)
theorem e3011 : o1.scale b73 b1136=b3244 := @scale_cons V1 _ o1 b73 b45 b3233 b1138 b3245 b3244 e3008 e3010 (by rfl)
theorem e3012 : o1.scale b73 b1134=b3243 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1136 b3244 b3243 e2414 e3011 (by rfl)
theorem e3013 : o1.scale b73 b1132=b3242 := @scale_cons V1 _ o1 b73 b44 b3232 b1134 b3243 b3242 e3007 e3012 (by rfl)
theorem e3014 : o1.scale b73 b1130=b3241 := @scale_cons V1 _ o1 b73 b43 b3231 b1132 b3242 b3241 e3006 e3013 (by rfl)
theorem e3015 : o1.scale b73 b1128=b3240 := @scale_cons V1 _ o1 b73 b42 b3230 b1130 b3241 b3240 e3005 e3014 (by rfl)
theorem e3016 : o1.scale b73 b1126=b3239 := @scale_cons V1 _ o1 b73 b18 b2753 b1128 b3240 b3239 e2419 e3015 (by rfl)
theorem e3017 : o1.scale b73 b1124=b3238 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1126 b3239 b3238 e2414 e3016 (by rfl)
theorem e3018 : o1.scale b73 b1122=b3237 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1124 b3238 b3237 e2414 e3017 (by rfl)
theorem e3019 : o1.scale b73 b1120=b3236 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1122 b3237 b3236 e2414 e3018 (by rfl)
theorem e3020 : o1.scale b73 b47=b3235 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1120 b3236 b3235 e2414 e3019 (by rfl)
theorem e3021 : o1.add b2753 (List.nil : V1)=b2753 := by rfl
theorem e3022 : o1.add b3230 b2734=b3180 := by decide
theorem e3023 : o1.add b3231 b3185=b3181 := by decide
theorem e3024 : o1.add b3232 b3186=b3177 := by decide
theorem e3025 : o1.add (List.nil : V1) b3182=b3182 := by rfl
theorem e3026 : o1.add b3233 b3187=b3183 := by decide
theorem e3027 : o1.add b3234 b3188=b2671 := by decide
theorem e3028 : o2.add (List.nil : V2) b3229=b3229 := by rfl
theorem e3029 : o2.add b3245 b3228=b3256 := @add_cons V1 _ o1 b3234 b3188 b2671 (List.nil : V2) b3229 b3229 b3256 e3027 e3028 (by rfl)
theorem e3030 : o2.add b3244 b3227=b3255 := @add_cons V1 _ o1 b3233 b3187 b3183 b3245 b3228 b3256 b3255 e3026 e3029 (by rfl)
theorem e3031 : o2.add b3243 b3226=b3254 := @add_cons V1 _ o1 (List.nil : V1) b3182 b3182 b3244 b3227 b3255 b3254 e3025 e3030 (by rfl)
theorem e3032 : o2.add b3242 b3225=b3253 := @add_cons V1 _ o1 b3232 b3186 b3177 b3243 b3226 b3254 b3253 e3024 e3031 (by rfl)
theorem e3033 : o2.add b3241 b3224=b3252 := @add_cons V1 _ o1 b3231 b3185 b3181 b3242 b3225 b3253 b3252 e3023 e3032 (by rfl)
theorem e3034 : o2.add b3240 b3223=b3251 := @add_cons V1 _ o1 b3230 b2734 b3180 b3241 b3224 b3252 b3251 e3022 e3033 (by rfl)
theorem e3035 : o2.add b3239 b3222=b3250 := @add_cons V1 _ o1 b2753 (List.nil : V1) b2753 b3240 b3223 b3251 b3250 e3021 e3034 (by rfl)
theorem e3036 : o2.add b3238 b3221=b3249 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3239 b3222 b3250 b3249 e34 e3035 (by rfl)
theorem e3037 : o2.add b3237 b3220=b3248 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3238 b3221 b3249 b3248 e34 e3036 (by rfl)
theorem e3038 : o2.add b3236 b3189=b3247 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3237 b3220 b3248 b3247 e34 e3037 (by rfl)
theorem e3039 : o2.add b3235 b3246=b3184 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3236 b3189 b3247 b3184 e34 e3038 (by rfl)
theorem e3040 : o2.mul b2704 b47=b3184 := @mul_cons V1 _ o1 b73 b2711 b47 b3189 b3235 b3246 b3184 e3004 e3020 (by rfl) e3039
theorem e3041 : o1.mul b72 b42=b3257 := by decide
theorem e3042 : o1.mul b72 b43=b3258 := by decide
theorem e3043 : o1.mul b72 b44=b3259 := by decide
theorem e3044 : o1.mul b72 b45=b3260 := by decide
theorem e3045 : o1.mul b72 b46=b3261 := by decide
theorem e3046 : o1.scale b72 b1138=b3272 := @scale_cons V1 _ o1 b72 b46 b3261 (List.nil : V2) (List.nil : V2) b3272 e3045 e2451 (by rfl)
theorem e3047 : o1.scale b72 b1136=b3271 := @scale_cons V1 _ o1 b72 b45 b3260 b1138 b3272 b3271 e3044 e3046 (by rfl)
theorem e3048 : o1.scale b72 b1134=b3270 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1136 b3271 b3270 e2444 e3047 (by rfl)
theorem e3049 : o1.scale b72 b1132=b3269 := @scale_cons V1 _ o1 b72 b44 b3259 b1134 b3270 b3269 e3043 e3048 (by rfl)
theorem e3050 : o1.scale b72 b1130=b3268 := @scale_cons V1 _ o1 b72 b43 b3258 b1132 b3269 b3268 e3042 e3049 (by rfl)
theorem e3051 : o1.scale b72 b1128=b3267 := @scale_cons V1 _ o1 b72 b42 b3257 b1130 b3268 b3267 e3041 e3050 (by rfl)
theorem e3052 : o1.scale b72 b1126=b3266 := @scale_cons V1 _ o1 b72 b18 b2772 b1128 b3267 b3266 e2449 e3051 (by rfl)
theorem e3053 : o1.scale b72 b1124=b3265 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1126 b3266 b3265 e2444 e3052 (by rfl)
theorem e3054 : o1.scale b72 b1122=b3264 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1124 b3265 b3264 e2444 e3053 (by rfl)
theorem e3055 : o1.scale b72 b1120=b3263 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1122 b3264 b3263 e2444 e3054 (by rfl)
theorem e3056 : o1.scale b72 b47=b3262 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1120 b3263 b3262 e2444 e3055 (by rfl)
theorem e3057 : o1.add b2772 (List.nil : V1)=b2772 := by rfl
theorem e3058 : o1.add b3257 b2753=b3175 := by decide
theorem e3059 : o1.add b3258 b3180=b3176 := by decide
theorem e3060 : o1.add b3259 b3181=b2667 := by decide
theorem e3061 : o1.add (List.nil : V1) b3177=b3177 := by rfl
theorem e3062 : o1.add b3260 b3182=b3178 := by decide
theorem e3063 : o1.add b3261 b3183=b2670 := by decide
theorem e3064 : o2.add (List.nil : V2) b3256=b3256 := by rfl
theorem e3065 : o2.add b3272 b3255=b3283 := @add_cons V1 _ o1 b3261 b3183 b2670 (List.nil : V2) b3256 b3256 b3283 e3063 e3064 (by rfl)
theorem e3066 : o2.add b3271 b3254=b3282 := @add_cons V1 _ o1 b3260 b3182 b3178 b3272 b3255 b3283 b3282 e3062 e3065 (by rfl)
theorem e3067 : o2.add b3270 b3253=b3281 := @add_cons V1 _ o1 (List.nil : V1) b3177 b3177 b3271 b3254 b3282 b3281 e3061 e3066 (by rfl)
theorem e3068 : o2.add b3269 b3252=b3280 := @add_cons V1 _ o1 b3259 b3181 b2667 b3270 b3253 b3281 b3280 e3060 e3067 (by rfl)
theorem e3069 : o2.add b3268 b3251=b3279 := @add_cons V1 _ o1 b3258 b3180 b3176 b3269 b3252 b3280 b3279 e3059 e3068 (by rfl)
theorem e3070 : o2.add b3267 b3250=b3278 := @add_cons V1 _ o1 b3257 b2753 b3175 b3268 b3251 b3279 b3278 e3058 e3069 (by rfl)
theorem e3071 : o2.add b3266 b3249=b3277 := @add_cons V1 _ o1 b2772 (List.nil : V1) b2772 b3267 b3250 b3278 b3277 e3057 e3070 (by rfl)
theorem e3072 : o2.add b3265 b3248=b3276 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3266 b3249 b3277 b3276 e34 e3071 (by rfl)
theorem e3073 : o2.add b3264 b3247=b3275 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3265 b3248 b3276 b3275 e34 e3072 (by rfl)
theorem e3074 : o2.add b3263 b3184=b3274 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3264 b3247 b3275 b3274 e34 e3073 (by rfl)
theorem e3075 : o2.add b3262 b3273=b3179 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3263 b3184 b3274 b3179 e34 e3074 (by rfl)
theorem e3076 : o2.mul b2697 b47=b3179 := @mul_cons V1 _ o1 b72 b2704 b47 b3184 b3262 b3273 b3179 e3040 e3056 (by rfl) e3075
theorem e3077 : o1.mul b71 b42=b3284 := by decide
theorem e3078 : o1.mul b71 b43=b3285 := by decide
theorem e3079 : o1.mul b71 b44=b3286 := by decide
theorem e3080 : o1.mul b71 b45=b3287 := by decide
theorem e3081 : o1.mul b71 b46=b3288 := by decide
theorem e3082 : o1.scale b71 b1138=b3299 := @scale_cons V1 _ o1 b71 b46 b3288 (List.nil : V2) (List.nil : V2) b3299 e3081 e2481 (by rfl)
theorem e3083 : o1.scale b71 b1136=b3298 := @scale_cons V1 _ o1 b71 b45 b3287 b1138 b3299 b3298 e3080 e3082 (by rfl)
theorem e3084 : o1.scale b71 b1134=b3297 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1136 b3298 b3297 e2474 e3083 (by rfl)
theorem e3085 : o1.scale b71 b1132=b3296 := @scale_cons V1 _ o1 b71 b44 b3286 b1134 b3297 b3296 e3079 e3084 (by rfl)
theorem e3086 : o1.scale b71 b1130=b3295 := @scale_cons V1 _ o1 b71 b43 b3285 b1132 b3296 b3295 e3078 e3085 (by rfl)
theorem e3087 : o1.scale b71 b1128=b3294 := @scale_cons V1 _ o1 b71 b42 b3284 b1130 b3295 b3294 e3077 e3086 (by rfl)
theorem e3088 : o1.scale b71 b1126=b3293 := @scale_cons V1 _ o1 b71 b18 b2663 b1128 b3294 b3293 e2479 e3087 (by rfl)
theorem e3089 : o1.scale b71 b1124=b3292 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1126 b3293 b3292 e2474 e3088 (by rfl)
theorem e3090 : o1.scale b71 b1122=b3291 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1124 b3292 b3291 e2474 e3089 (by rfl)
theorem e3091 : o1.scale b71 b1120=b3290 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1122 b3291 b3290 e2474 e3090 (by rfl)
theorem e3092 : o1.scale b71 b47=b3289 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1120 b3290 b3289 e2474 e3091 (by rfl)
theorem e3093 : o1.add b2663 (List.nil : V1)=b2663 := by rfl
theorem e3094 : o1.add b3284 b2772=b2664 := by decide
theorem e3095 : o1.add b3285 b3175=b2665 := by decide
theorem e3096 : o1.add b3286 b3176=b2666 := by decide
theorem e3097 : o1.add (List.nil : V1) b2667=b2667 := by rfl
theorem e3098 : o1.add b3287 b3177=b2668 := by decide
theorem e3099 : o1.add b3288 b3178=b2669 := by decide
theorem e3100 : o2.add (List.nil : V2) b3283=b3283 := by rfl
theorem e3101 : o2.add b3299 b3282=b3310 := @add_cons V1 _ o1 b3288 b3178 b2669 (List.nil : V2) b3283 b3283 b3310 e3099 e3100 (by rfl)
theorem e3102 : o2.add b3298 b3281=b3309 := @add_cons V1 _ o1 b3287 b3177 b2668 b3299 b3282 b3310 b3309 e3098 e3101 (by rfl)
theorem e3103 : o2.add b3297 b3280=b3308 := @add_cons V1 _ o1 (List.nil : V1) b2667 b2667 b3298 b3281 b3309 b3308 e3097 e3102 (by rfl)
theorem e3104 : o2.add b3296 b3279=b3307 := @add_cons V1 _ o1 b3286 b3176 b2666 b3297 b3280 b3308 b3307 e3096 e3103 (by rfl)
theorem e3105 : o2.add b3295 b3278=b3306 := @add_cons V1 _ o1 b3285 b3175 b2665 b3296 b3279 b3307 b3306 e3095 e3104 (by rfl)
theorem e3106 : o2.add b3294 b3277=b3305 := @add_cons V1 _ o1 b3284 b2772 b2664 b3295 b3278 b3306 b3305 e3094 e3105 (by rfl)
theorem e3107 : o2.add b3293 b3276=b3304 := @add_cons V1 _ o1 b2663 (List.nil : V1) b2663 b3294 b3277 b3305 b3304 e3093 e3106 (by rfl)
theorem e3108 : o2.add b3292 b3275=b3303 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3293 b3276 b3304 b3303 e34 e3107 (by rfl)
theorem e3109 : o2.add b3291 b3274=b3302 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3292 b3275 b3303 b3302 e34 e3108 (by rfl)
theorem e3110 : o2.add b3290 b3179=b3301 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3291 b3274 b3302 b3301 e34 e3109 (by rfl)
theorem e3111 : o2.add b3289 b3300=b2673 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3290 b3179 b3301 b2673 e34 e3110 (by rfl)
theorem e3112 : o2.mul b76 b47=b2673 := @mul_cons V1 _ o1 b71 b2697 b47 b3179 b3289 b3300 b2673 e3076 e3092 (by rfl) e3111
theorem e3113 : o1.mul b75 b48=b3327 := by decide
theorem e3114 : o1.mul b75 b49=b3328 := by decide
theorem e3115 : o1.mul b75 b50=b3329 := by decide
theorem e3116 : o1.mul b75 b51=b3325 := by decide
theorem e3117 : o1.mul b75 b52=b414 := by decide
theorem e3118 : o1.scale b75 b1288=b3341 := @scale_cons V1 _ o1 b75 b52 b414 (List.nil : V2) (List.nil : V2) b3341 e3117 e2374 (by rfl)
theorem e3119 : o1.scale b75 b1286=b3340 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1288 b3341 b3340 e2367 e3118 (by rfl)
theorem e3120 : o1.scale b75 b1284=b3339 := @scale_cons V1 _ o1 b75 b51 b3325 b1286 b3340 b3339 e3116 e3119 (by rfl)
theorem e3121 : o1.scale b75 b1282=b3338 := @scale_cons V1 _ o1 b75 b50 b3329 b1284 b3339 b3338 e3115 e3120 (by rfl)
theorem e3122 : o1.scale b75 b1280=b3337 := @scale_cons V1 _ o1 b75 b49 b3328 b1282 b3338 b3337 e3114 e3121 (by rfl)
theorem e3123 : o1.scale b75 b1278=b3336 := @scale_cons V1 _ o1 b75 b48 b3327 b1280 b3337 b3336 e3113 e3122 (by rfl)
theorem e3124 : o1.scale b75 b1276=b3335 := @scale_cons V1 _ o1 b75 b17 b2722 b1278 b3336 b3335 e2371 e3123 (by rfl)
theorem e3125 : o1.scale b75 b1274=b3334 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1276 b3335 b3334 e2367 e3124 (by rfl)
theorem e3126 : o1.scale b75 b1272=b3333 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1274 b3334 b3333 e2367 e3125 (by rfl)
theorem e3127 : o1.scale b75 b1270=b3332 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1272 b3333 b3332 e2367 e3126 (by rfl)
theorem e3128 : o1.scale b75 b1268=b3331 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1270 b3332 b3331 e2367 e3127 (by rfl)
theorem e3129 : o1.scale b75 b53=b3330 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1268 b3331 b3330 e2367 e3128 (by rfl)
theorem e3130 : o2.add b3330 (List.nil : V2)=b3330 := by rfl
theorem e3131 : o2.mul b2718 b53=b3330 := @mul_cons V1 _ o1 b75 (List.nil : V2) b53 (List.nil : V2) b3330 (List.nil : V2) b3330 e753 e3129 (by rfl) e3130
theorem e3132 : o1.mul b74 b48=b3342 := by decide
theorem e3133 : o1.mul b74 b49=b3343 := by decide
theorem e3134 : o1.mul b74 b50=b3344 := by decide
theorem e3135 : o1.mul b74 b51=b3345 := by decide
theorem e3136 : o1.mul b74 b52=b2683 := by decide
theorem e3137 : o1.scale b74 b1288=b3357 := @scale_cons V1 _ o1 b74 b52 b2683 (List.nil : V2) (List.nil : V2) b3357 e3136 e2391 (by rfl)
theorem e3138 : o1.scale b74 b1286=b3356 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1288 b3357 b3356 e2384 e3137 (by rfl)
theorem e3139 : o1.scale b74 b1284=b3355 := @scale_cons V1 _ o1 b74 b51 b3345 b1286 b3356 b3355 e3135 e3138 (by rfl)
theorem e3140 : o1.scale b74 b1282=b3354 := @scale_cons V1 _ o1 b74 b50 b3344 b1284 b3355 b3354 e3134 e3139 (by rfl)
theorem e3141 : o1.scale b74 b1280=b3353 := @scale_cons V1 _ o1 b74 b49 b3343 b1282 b3354 b3353 e3133 e3140 (by rfl)
theorem e3142 : o1.scale b74 b1278=b3352 := @scale_cons V1 _ o1 b74 b48 b3342 b1280 b3353 b3352 e3132 e3141 (by rfl)
theorem e3143 : o1.scale b74 b1276=b3351 := @scale_cons V1 _ o1 b74 b17 b2733 b1278 b3352 b3351 e2388 e3142 (by rfl)
theorem e3144 : o1.scale b74 b1274=b3350 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1276 b3351 b3350 e2384 e3143 (by rfl)
theorem e3145 : o1.scale b74 b1272=b3349 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1274 b3350 b3349 e2384 e3144 (by rfl)
theorem e3146 : o1.scale b74 b1270=b3348 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1272 b3349 b3348 e2384 e3145 (by rfl)
theorem e3147 : o1.scale b74 b1268=b3347 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1270 b3348 b3347 e2384 e3146 (by rfl)
theorem e3148 : o1.scale b74 b53=b3346 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1268 b3347 b3346 e2384 e3147 (by rfl)
theorem e3149 : o1.add b2733 (List.nil : V1)=b2733 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
