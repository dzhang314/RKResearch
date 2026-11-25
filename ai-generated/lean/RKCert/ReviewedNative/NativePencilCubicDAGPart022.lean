module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart021

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3150 : o1.add b3342 b2722=b3322 := by decide
theorem e3151 : o1.add b3343 b3327=b3323 := by decide
theorem e3152 : o1.add b3344 b3328=b3324 := by decide
theorem e3153 : o1.add b3345 b3329=b3320 := by decide
theorem e3154 : o1.add (List.nil : V1) b3325=b3325 := by rfl
theorem e3155 : o1.add b2683 (List.nil : V1)=b2683 := by rfl
theorem e3156 : o2.add (List.nil : V2) b3341=b3341 := by rfl
theorem e3157 : o2.add b3357 b3340=b3369 := @add_cons V1 _ o1 b2683 (List.nil : V1) b2683 (List.nil : V2) b3341 b3341 b3369 e3155 e3156 (by rfl)
theorem e3158 : o2.add b3356 b3339=b3368 := @add_cons V1 _ o1 (List.nil : V1) b3325 b3325 b3357 b3340 b3369 b3368 e3154 e3157 (by rfl)
theorem e3159 : o2.add b3355 b3338=b3367 := @add_cons V1 _ o1 b3345 b3329 b3320 b3356 b3339 b3368 b3367 e3153 e3158 (by rfl)
theorem e3160 : o2.add b3354 b3337=b3366 := @add_cons V1 _ o1 b3344 b3328 b3324 b3355 b3338 b3367 b3366 e3152 e3159 (by rfl)
theorem e3161 : o2.add b3353 b3336=b3365 := @add_cons V1 _ o1 b3343 b3327 b3323 b3354 b3337 b3366 b3365 e3151 e3160 (by rfl)
theorem e3162 : o2.add b3352 b3335=b3364 := @add_cons V1 _ o1 b3342 b2722 b3322 b3353 b3336 b3365 b3364 e3150 e3161 (by rfl)
theorem e3163 : o2.add b3351 b3334=b3363 := @add_cons V1 _ o1 b2733 (List.nil : V1) b2733 b3352 b3335 b3364 b3363 e3149 e3162 (by rfl)
theorem e3164 : o2.add b3350 b3333=b3362 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3351 b3334 b3363 b3362 e34 e3163 (by rfl)
theorem e3165 : o2.add b3349 b3332=b3361 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3350 b3333 b3362 b3361 e34 e3164 (by rfl)
theorem e3166 : o2.add b3348 b3331=b3360 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3349 b3332 b3361 b3360 e34 e3165 (by rfl)
theorem e3167 : o2.add b3347 b3330=b3359 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3348 b3331 b3360 b3359 e34 e3166 (by rfl)
theorem e3168 : o2.add b3346 b3358=b3326 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3347 b3330 b3359 b3326 e34 e3167 (by rfl)
theorem e3169 : o2.mul b2711 b53=b3326 := @mul_cons V1 _ o1 b74 b2718 b53 b3330 b3346 b3358 b3326 e3131 e3148 (by rfl) e3168
theorem e3170 : o1.mul b73 b48=b3370 := by decide
theorem e3171 : o1.mul b73 b49=b3371 := by decide
theorem e3172 : o1.mul b73 b50=b3372 := by decide
theorem e3173 : o1.mul b73 b51=b3373 := by decide
theorem e3174 : o1.mul b73 b52=b3374 := by decide
theorem e3175 : o1.scale b73 b1288=b3386 := @scale_cons V1 _ o1 b73 b52 b3374 (List.nil : V2) (List.nil : V2) b3386 e3174 e2421 (by rfl)
theorem e3176 : o1.scale b73 b1286=b3385 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1288 b3386 b3385 e2414 e3175 (by rfl)
theorem e3177 : o1.scale b73 b1284=b3384 := @scale_cons V1 _ o1 b73 b51 b3373 b1286 b3385 b3384 e3173 e3176 (by rfl)
theorem e3178 : o1.scale b73 b1282=b3383 := @scale_cons V1 _ o1 b73 b50 b3372 b1284 b3384 b3383 e3172 e3177 (by rfl)
theorem e3179 : o1.scale b73 b1280=b3382 := @scale_cons V1 _ o1 b73 b49 b3371 b1282 b3383 b3382 e3171 e3178 (by rfl)
theorem e3180 : o1.scale b73 b1278=b3381 := @scale_cons V1 _ o1 b73 b48 b3370 b1280 b3382 b3381 e3170 e3179 (by rfl)
theorem e3181 : o1.scale b73 b1276=b3380 := @scale_cons V1 _ o1 b73 b17 b2752 b1278 b3381 b3380 e2418 e3180 (by rfl)
theorem e3182 : o1.scale b73 b1274=b3379 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1276 b3380 b3379 e2414 e3181 (by rfl)
theorem e3183 : o1.scale b73 b1272=b3378 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1274 b3379 b3378 e2414 e3182 (by rfl)
theorem e3184 : o1.scale b73 b1270=b3377 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1272 b3378 b3377 e2414 e3183 (by rfl)
theorem e3185 : o1.scale b73 b1268=b3376 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1270 b3377 b3376 e2414 e3184 (by rfl)
theorem e3186 : o1.scale b73 b53=b3375 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1268 b3376 b3375 e2414 e3185 (by rfl)
theorem e3187 : o1.add b2752 (List.nil : V1)=b2752 := by rfl
theorem e3188 : o1.add b3370 b2733=b3317 := by decide
theorem e3189 : o1.add b3371 b3322=b3318 := by decide
theorem e3190 : o1.add b3372 b3323=b3319 := by decide
theorem e3191 : o1.add b3373 b3324=b3315 := by decide
theorem e3192 : o1.add (List.nil : V1) b3320=b3320 := by rfl
theorem e3193 : o1.add b3374 b3325=b2682 := by decide
theorem e3194 : o2.add (List.nil : V2) b3369=b3369 := by rfl
theorem e3195 : o2.add b3386 b3368=b3398 := @add_cons V1 _ o1 b3374 b3325 b2682 (List.nil : V2) b3369 b3369 b3398 e3193 e3194 (by rfl)
theorem e3196 : o2.add b3385 b3367=b3397 := @add_cons V1 _ o1 (List.nil : V1) b3320 b3320 b3386 b3368 b3398 b3397 e3192 e3195 (by rfl)
theorem e3197 : o2.add b3384 b3366=b3396 := @add_cons V1 _ o1 b3373 b3324 b3315 b3385 b3367 b3397 b3396 e3191 e3196 (by rfl)
theorem e3198 : o2.add b3383 b3365=b3395 := @add_cons V1 _ o1 b3372 b3323 b3319 b3384 b3366 b3396 b3395 e3190 e3197 (by rfl)
theorem e3199 : o2.add b3382 b3364=b3394 := @add_cons V1 _ o1 b3371 b3322 b3318 b3383 b3365 b3395 b3394 e3189 e3198 (by rfl)
theorem e3200 : o2.add b3381 b3363=b3393 := @add_cons V1 _ o1 b3370 b2733 b3317 b3382 b3364 b3394 b3393 e3188 e3199 (by rfl)
theorem e3201 : o2.add b3380 b3362=b3392 := @add_cons V1 _ o1 b2752 (List.nil : V1) b2752 b3381 b3363 b3393 b3392 e3187 e3200 (by rfl)
theorem e3202 : o2.add b3379 b3361=b3391 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3380 b3362 b3392 b3391 e34 e3201 (by rfl)
theorem e3203 : o2.add b3378 b3360=b3390 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3379 b3361 b3391 b3390 e34 e3202 (by rfl)
theorem e3204 : o2.add b3377 b3359=b3389 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3378 b3360 b3390 b3389 e34 e3203 (by rfl)
theorem e3205 : o2.add b3376 b3326=b3388 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3377 b3359 b3389 b3388 e34 e3204 (by rfl)
theorem e3206 : o2.add b3375 b3387=b3321 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3376 b3326 b3388 b3321 e34 e3205 (by rfl)
theorem e3207 : o2.mul b2704 b53=b3321 := @mul_cons V1 _ o1 b73 b2711 b53 b3326 b3375 b3387 b3321 e3169 e3186 (by rfl) e3206
theorem e3208 : o1.mul b72 b48=b3399 := by decide
theorem e3209 : o1.mul b72 b49=b3400 := by decide
theorem e3210 : o1.mul b72 b50=b3401 := by decide
theorem e3211 : o1.mul b72 b51=b3402 := by decide
theorem e3212 : o1.mul b72 b52=b3403 := by decide
theorem e3213 : o1.scale b72 b1288=b3415 := @scale_cons V1 _ o1 b72 b52 b3403 (List.nil : V2) (List.nil : V2) b3415 e3212 e2451 (by rfl)
theorem e3214 : o1.scale b72 b1286=b3414 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1288 b3415 b3414 e2444 e3213 (by rfl)
theorem e3215 : o1.scale b72 b1284=b3413 := @scale_cons V1 _ o1 b72 b51 b3402 b1286 b3414 b3413 e3211 e3214 (by rfl)
theorem e3216 : o1.scale b72 b1282=b3412 := @scale_cons V1 _ o1 b72 b50 b3401 b1284 b3413 b3412 e3210 e3215 (by rfl)
theorem e3217 : o1.scale b72 b1280=b3411 := @scale_cons V1 _ o1 b72 b49 b3400 b1282 b3412 b3411 e3209 e3216 (by rfl)
theorem e3218 : o1.scale b72 b1278=b3410 := @scale_cons V1 _ o1 b72 b48 b3399 b1280 b3411 b3410 e3208 e3217 (by rfl)
theorem e3219 : o1.scale b72 b1276=b3409 := @scale_cons V1 _ o1 b72 b17 b2771 b1278 b3410 b3409 e2448 e3218 (by rfl)
theorem e3220 : o1.scale b72 b1274=b3408 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1276 b3409 b3408 e2444 e3219 (by rfl)
theorem e3221 : o1.scale b72 b1272=b3407 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1274 b3408 b3407 e2444 e3220 (by rfl)
theorem e3222 : o1.scale b72 b1270=b3406 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1272 b3407 b3406 e2444 e3221 (by rfl)
theorem e3223 : o1.scale b72 b1268=b3405 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1270 b3406 b3405 e2444 e3222 (by rfl)
theorem e3224 : o1.scale b72 b53=b3404 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1268 b3405 b3404 e2444 e3223 (by rfl)
theorem e3225 : o1.add b2771 (List.nil : V1)=b2771 := by rfl
theorem e3226 : o1.add b3399 b2752=b3312 := by decide
theorem e3227 : o1.add b3400 b3317=b3313 := by decide
theorem e3228 : o1.add b3401 b3318=b3314 := by decide
theorem e3229 : o1.add b3402 b3319=b2679 := by decide
theorem e3230 : o1.add (List.nil : V1) b3315=b3315 := by rfl
theorem e3231 : o1.add b3403 b3320=b2681 := by decide
theorem e3232 : o2.add (List.nil : V2) b3398=b3398 := by rfl
theorem e3233 : o2.add b3415 b3397=b3427 := @add_cons V1 _ o1 b3403 b3320 b2681 (List.nil : V2) b3398 b3398 b3427 e3231 e3232 (by rfl)
theorem e3234 : o2.add b3414 b3396=b3426 := @add_cons V1 _ o1 (List.nil : V1) b3315 b3315 b3415 b3397 b3427 b3426 e3230 e3233 (by rfl)
theorem e3235 : o2.add b3413 b3395=b3425 := @add_cons V1 _ o1 b3402 b3319 b2679 b3414 b3396 b3426 b3425 e3229 e3234 (by rfl)
theorem e3236 : o2.add b3412 b3394=b3424 := @add_cons V1 _ o1 b3401 b3318 b3314 b3413 b3395 b3425 b3424 e3228 e3235 (by rfl)
theorem e3237 : o2.add b3411 b3393=b3423 := @add_cons V1 _ o1 b3400 b3317 b3313 b3412 b3394 b3424 b3423 e3227 e3236 (by rfl)
theorem e3238 : o2.add b3410 b3392=b3422 := @add_cons V1 _ o1 b3399 b2752 b3312 b3411 b3393 b3423 b3422 e3226 e3237 (by rfl)
theorem e3239 : o2.add b3409 b3391=b3421 := @add_cons V1 _ o1 b2771 (List.nil : V1) b2771 b3410 b3392 b3422 b3421 e3225 e3238 (by rfl)
theorem e3240 : o2.add b3408 b3390=b3420 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3409 b3391 b3421 b3420 e34 e3239 (by rfl)
theorem e3241 : o2.add b3407 b3389=b3419 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3408 b3390 b3420 b3419 e34 e3240 (by rfl)
theorem e3242 : o2.add b3406 b3388=b3418 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3407 b3389 b3419 b3418 e34 e3241 (by rfl)
theorem e3243 : o2.add b3405 b3321=b3417 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3406 b3388 b3418 b3417 e34 e3242 (by rfl)
theorem e3244 : o2.add b3404 b3416=b3316 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3405 b3321 b3417 b3316 e34 e3243 (by rfl)
theorem e3245 : o2.mul b2697 b53=b3316 := @mul_cons V1 _ o1 b72 b2704 b53 b3321 b3404 b3416 b3316 e3207 e3224 (by rfl) e3244
theorem e3246 : o1.mul b71 b48=b3428 := by decide
theorem e3247 : o1.mul b71 b49=b3429 := by decide
theorem e3248 : o1.mul b71 b50=b3430 := by decide
theorem e3249 : o1.mul b71 b51=b3431 := by decide
theorem e3250 : o1.mul b71 b52=b3432 := by decide
theorem e3251 : o1.scale b71 b1288=b3444 := @scale_cons V1 _ o1 b71 b52 b3432 (List.nil : V2) (List.nil : V2) b3444 e3250 e2481 (by rfl)
theorem e3252 : o1.scale b71 b1286=b3443 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1288 b3444 b3443 e2474 e3251 (by rfl)
theorem e3253 : o1.scale b71 b1284=b3442 := @scale_cons V1 _ o1 b71 b51 b3431 b1286 b3443 b3442 e3249 e3252 (by rfl)
theorem e3254 : o1.scale b71 b1282=b3441 := @scale_cons V1 _ o1 b71 b50 b3430 b1284 b3442 b3441 e3248 e3253 (by rfl)
theorem e3255 : o1.scale b71 b1280=b3440 := @scale_cons V1 _ o1 b71 b49 b3429 b1282 b3441 b3440 e3247 e3254 (by rfl)
theorem e3256 : o1.scale b71 b1278=b3439 := @scale_cons V1 _ o1 b71 b48 b3428 b1280 b3440 b3439 e3246 e3255 (by rfl)
theorem e3257 : o1.scale b71 b1276=b3438 := @scale_cons V1 _ o1 b71 b17 b2674 b1278 b3439 b3438 e2478 e3256 (by rfl)
theorem e3258 : o1.scale b71 b1274=b3437 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1276 b3438 b3437 e2474 e3257 (by rfl)
theorem e3259 : o1.scale b71 b1272=b3436 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1274 b3437 b3436 e2474 e3258 (by rfl)
theorem e3260 : o1.scale b71 b1270=b3435 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1272 b3436 b3435 e2474 e3259 (by rfl)
theorem e3261 : o1.scale b71 b1268=b3434 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1270 b3435 b3434 e2474 e3260 (by rfl)
theorem e3262 : o1.scale b71 b53=b3433 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1268 b3434 b3433 e2474 e3261 (by rfl)
theorem e3263 : o1.add b2674 (List.nil : V1)=b2674 := by rfl
theorem e3264 : o1.add b3428 b2771=b2675 := by decide
theorem e3265 : o1.add b3429 b3312=b2676 := by decide
theorem e3266 : o1.add b3430 b3313=b2677 := by decide
theorem e3267 : o1.add b3431 b3314=b2678 := by decide
theorem e3268 : o1.add (List.nil : V1) b2679=b2679 := by rfl
theorem e3269 : o1.add b3432 b3315=b2680 := by decide
theorem e3270 : o2.add (List.nil : V2) b3427=b3427 := by rfl
theorem e3271 : o2.add b3444 b3426=b3456 := @add_cons V1 _ o1 b3432 b3315 b2680 (List.nil : V2) b3427 b3427 b3456 e3269 e3270 (by rfl)
theorem e3272 : o2.add b3443 b3425=b3455 := @add_cons V1 _ o1 (List.nil : V1) b2679 b2679 b3444 b3426 b3456 b3455 e3268 e3271 (by rfl)
theorem e3273 : o2.add b3442 b3424=b3454 := @add_cons V1 _ o1 b3431 b3314 b2678 b3443 b3425 b3455 b3454 e3267 e3272 (by rfl)
theorem e3274 : o2.add b3441 b3423=b3453 := @add_cons V1 _ o1 b3430 b3313 b2677 b3442 b3424 b3454 b3453 e3266 e3273 (by rfl)
theorem e3275 : o2.add b3440 b3422=b3452 := @add_cons V1 _ o1 b3429 b3312 b2676 b3441 b3423 b3453 b3452 e3265 e3274 (by rfl)
theorem e3276 : o2.add b3439 b3421=b3451 := @add_cons V1 _ o1 b3428 b2771 b2675 b3440 b3422 b3452 b3451 e3264 e3275 (by rfl)
theorem e3277 : o2.add b3438 b3420=b3450 := @add_cons V1 _ o1 b2674 (List.nil : V1) b2674 b3439 b3421 b3451 b3450 e3263 e3276 (by rfl)
theorem e3278 : o2.add b3437 b3419=b3449 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3438 b3420 b3450 b3449 e34 e3277 (by rfl)
theorem e3279 : o2.add b3436 b3418=b3448 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3437 b3419 b3449 b3448 e34 e3278 (by rfl)
theorem e3280 : o2.add b3435 b3417=b3447 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3436 b3418 b3448 b3447 e34 e3279 (by rfl)
theorem e3281 : o2.add b3434 b3316=b3446 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3435 b3417 b3447 b3446 e34 e3280 (by rfl)
theorem e3282 : o2.add b3433 b3445=b2684 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3434 b3316 b3446 b2684 e34 e3281 (by rfl)
theorem e3283 : o2.mul b76 b53=b2684 := @mul_cons V1 _ o1 b71 b2697 b53 b3316 b3433 b3445 b2684 e3245 e3262 (by rfl) e3282
theorem e3284 : o1.mul b75 b54=b3476 := by decide
theorem e3285 : o1.mul b75 b55=b3477 := by decide
theorem e3286 : o1.mul b75 b56=b3478 := by decide
theorem e3287 : o1.mul b75 b57=b3479 := by decide
theorem e3288 : o1.mul b75 b58=b3480 := by decide
theorem e3289 : o1.mul b75 b59=b2694 := by decide
theorem e3290 : o1.scale b75 b1451=b3492 := @scale_cons V1 _ o1 b75 b59 b2694 (List.nil : V2) (List.nil : V2) b3492 e3289 e2374 (by rfl)
theorem e3291 : o1.scale b75 b1449=b3491 := @scale_cons V1 _ o1 b75 b58 b3480 b1451 b3492 b3491 e3288 e3290 (by rfl)
theorem e3292 : o1.scale b75 b1447=b3490 := @scale_cons V1 _ o1 b75 b57 b3479 b1449 b3491 b3490 e3287 e3291 (by rfl)
theorem e3293 : o1.scale b75 b1445=b3489 := @scale_cons V1 _ o1 b75 b56 b3478 b1447 b3490 b3489 e3286 e3292 (by rfl)
theorem e3294 : o1.scale b75 b1443=b3488 := @scale_cons V1 _ o1 b75 b55 b3477 b1445 b3489 b3488 e3285 e3293 (by rfl)
theorem e3295 : o1.scale b75 b1441=b3487 := @scale_cons V1 _ o1 b75 b54 b3476 b1443 b3488 b3487 e3284 e3294 (by rfl)
theorem e3296 : o1.scale b75 b1439=b3486 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1441 b3487 b3486 e2367 e3295 (by rfl)
theorem e3297 : o1.scale b75 b1437=b3485 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1439 b3486 b3485 e2367 e3296 (by rfl)
theorem e3298 : o1.scale b75 b1435=b3484 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1437 b3485 b3484 e2367 e3297 (by rfl)
theorem e3299 : o1.scale b75 b1433=b3483 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1435 b3484 b3483 e2367 e3298 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
