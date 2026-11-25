module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart022

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3300 : o1.scale b75 b1431=b3482 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1433 b3483 b3482 e2367 e3299 (by rfl)
theorem e3301 : o1.scale b75 b60=b3481 := @scale_cons V1 _ o1 b75 (List.nil : V1) (List.nil : V1) b1431 b3482 b3481 e2367 e3300 (by rfl)
theorem e3302 : o2.add b3481 (List.nil : V2)=b3481 := by rfl
theorem e3303 : o2.mul b2718 b60=b3481 := @mul_cons V1 _ o1 b75 (List.nil : V2) b60 (List.nil : V2) b3481 (List.nil : V2) b3481 e925 e3301 (by rfl) e3302
theorem e3304 : o1.mul b74 b54=b3470 := by decide
theorem e3305 : o1.mul b74 b55=b3493 := by decide
theorem e3306 : o1.mul b74 b56=b3494 := by decide
theorem e3307 : o1.mul b74 b57=b3495 := by decide
theorem e3308 : o1.mul b74 b58=b3496 := by decide
theorem e3309 : o1.mul b74 b59=b3497 := by decide
theorem e3310 : o1.scale b74 b1451=b3509 := @scale_cons V1 _ o1 b74 b59 b3497 (List.nil : V2) (List.nil : V2) b3509 e3309 e2391 (by rfl)
theorem e3311 : o1.scale b74 b1449=b3508 := @scale_cons V1 _ o1 b74 b58 b3496 b1451 b3509 b3508 e3308 e3310 (by rfl)
theorem e3312 : o1.scale b74 b1447=b3507 := @scale_cons V1 _ o1 b74 b57 b3495 b1449 b3508 b3507 e3307 e3311 (by rfl)
theorem e3313 : o1.scale b74 b1445=b3506 := @scale_cons V1 _ o1 b74 b56 b3494 b1447 b3507 b3506 e3306 e3312 (by rfl)
theorem e3314 : o1.scale b74 b1443=b3505 := @scale_cons V1 _ o1 b74 b55 b3493 b1445 b3506 b3505 e3305 e3313 (by rfl)
theorem e3315 : o1.scale b74 b1441=b3504 := @scale_cons V1 _ o1 b74 b54 b3470 b1443 b3505 b3504 e3304 e3314 (by rfl)
theorem e3316 : o1.scale b74 b1439=b3503 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1441 b3504 b3503 e2384 e3315 (by rfl)
theorem e3317 : o1.scale b74 b1437=b3502 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1439 b3503 b3502 e2384 e3316 (by rfl)
theorem e3318 : o1.scale b74 b1435=b3501 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1437 b3502 b3501 e2384 e3317 (by rfl)
theorem e3319 : o1.scale b74 b1433=b3500 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1435 b3501 b3500 e2384 e3318 (by rfl)
theorem e3320 : o1.scale b74 b1431=b3499 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1433 b3500 b3499 e2384 e3319 (by rfl)
theorem e3321 : o1.scale b74 b60=b3498 := @scale_cons V1 _ o1 b74 (List.nil : V1) (List.nil : V1) b1431 b3499 b3498 e2384 e3320 (by rfl)
theorem e3322 : o1.add b3470 (List.nil : V1)=b3470 := by rfl
theorem e3323 : o1.add b3493 b3476=b3471 := by decide
theorem e3324 : o1.add b3494 b3477=b3472 := by decide
theorem e3325 : o1.add b3495 b3478=b3473 := by decide
theorem e3326 : o1.add b3496 b3479=b3474 := by decide
theorem e3327 : o1.add b3497 b3480=b2693 := by decide
theorem e3328 : o2.add (List.nil : V2) b3492=b3492 := by rfl
theorem e3329 : o2.add b3509 b3491=b3521 := @add_cons V1 _ o1 b3497 b3480 b2693 (List.nil : V2) b3492 b3492 b3521 e3327 e3328 (by rfl)
theorem e3330 : o2.add b3508 b3490=b3520 := @add_cons V1 _ o1 b3496 b3479 b3474 b3509 b3491 b3521 b3520 e3326 e3329 (by rfl)
theorem e3331 : o2.add b3507 b3489=b3519 := @add_cons V1 _ o1 b3495 b3478 b3473 b3508 b3490 b3520 b3519 e3325 e3330 (by rfl)
theorem e3332 : o2.add b3506 b3488=b3518 := @add_cons V1 _ o1 b3494 b3477 b3472 b3507 b3489 b3519 b3518 e3324 e3331 (by rfl)
theorem e3333 : o2.add b3505 b3487=b3517 := @add_cons V1 _ o1 b3493 b3476 b3471 b3506 b3488 b3518 b3517 e3323 e3332 (by rfl)
theorem e3334 : o2.add b3504 b3486=b3516 := @add_cons V1 _ o1 b3470 (List.nil : V1) b3470 b3505 b3487 b3517 b3516 e3322 e3333 (by rfl)
theorem e3335 : o2.add b3503 b3485=b3515 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3504 b3486 b3516 b3515 e34 e3334 (by rfl)
theorem e3336 : o2.add b3502 b3484=b3514 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3503 b3485 b3515 b3514 e34 e3335 (by rfl)
theorem e3337 : o2.add b3501 b3483=b3513 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3502 b3484 b3514 b3513 e34 e3336 (by rfl)
theorem e3338 : o2.add b3500 b3482=b3512 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3501 b3483 b3513 b3512 e34 e3337 (by rfl)
theorem e3339 : o2.add b3499 b3481=b3511 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3500 b3482 b3512 b3511 e34 e3338 (by rfl)
theorem e3340 : o2.add b3498 b3510=b3475 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3499 b3481 b3511 b3475 e34 e3339 (by rfl)
theorem e3341 : o2.mul b2711 b60=b3475 := @mul_cons V1 _ o1 b74 b2718 b60 b3481 b3498 b3510 b3475 e3303 e3321 (by rfl) e3340
theorem e3342 : o1.mul b73 b54=b3464 := by decide
theorem e3343 : o1.mul b73 b55=b3522 := by decide
theorem e3344 : o1.mul b73 b56=b3523 := by decide
theorem e3345 : o1.mul b73 b57=b3524 := by decide
theorem e3346 : o1.mul b73 b58=b3525 := by decide
theorem e3347 : o1.mul b73 b59=b3526 := by decide
theorem e3348 : o1.scale b73 b1451=b3538 := @scale_cons V1 _ o1 b73 b59 b3526 (List.nil : V2) (List.nil : V2) b3538 e3347 e2421 (by rfl)
theorem e3349 : o1.scale b73 b1449=b3537 := @scale_cons V1 _ o1 b73 b58 b3525 b1451 b3538 b3537 e3346 e3348 (by rfl)
theorem e3350 : o1.scale b73 b1447=b3536 := @scale_cons V1 _ o1 b73 b57 b3524 b1449 b3537 b3536 e3345 e3349 (by rfl)
theorem e3351 : o1.scale b73 b1445=b3535 := @scale_cons V1 _ o1 b73 b56 b3523 b1447 b3536 b3535 e3344 e3350 (by rfl)
theorem e3352 : o1.scale b73 b1443=b3534 := @scale_cons V1 _ o1 b73 b55 b3522 b1445 b3535 b3534 e3343 e3351 (by rfl)
theorem e3353 : o1.scale b73 b1441=b3533 := @scale_cons V1 _ o1 b73 b54 b3464 b1443 b3534 b3533 e3342 e3352 (by rfl)
theorem e3354 : o1.scale b73 b1439=b3532 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1441 b3533 b3532 e2414 e3353 (by rfl)
theorem e3355 : o1.scale b73 b1437=b3531 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1439 b3532 b3531 e2414 e3354 (by rfl)
theorem e3356 : o1.scale b73 b1435=b3530 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1437 b3531 b3530 e2414 e3355 (by rfl)
theorem e3357 : o1.scale b73 b1433=b3529 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1435 b3530 b3529 e2414 e3356 (by rfl)
theorem e3358 : o1.scale b73 b1431=b3528 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1433 b3529 b3528 e2414 e3357 (by rfl)
theorem e3359 : o1.scale b73 b60=b3527 := @scale_cons V1 _ o1 b73 (List.nil : V1) (List.nil : V1) b1431 b3528 b3527 e2414 e3358 (by rfl)
theorem e3360 : o1.add b3464 (List.nil : V1)=b3464 := by rfl
theorem e3361 : o1.add b3522 b3470=b3465 := by decide
theorem e3362 : o1.add b3523 b3471=b3466 := by decide
theorem e3363 : o1.add b3524 b3472=b3467 := by decide
theorem e3364 : o1.add b3525 b3473=b3468 := by decide
theorem e3365 : o1.add b3526 b3474=b2692 := by decide
theorem e3366 : o2.add (List.nil : V2) b3521=b3521 := by rfl
theorem e3367 : o2.add b3538 b3520=b3550 := @add_cons V1 _ o1 b3526 b3474 b2692 (List.nil : V2) b3521 b3521 b3550 e3365 e3366 (by rfl)
theorem e3368 : o2.add b3537 b3519=b3549 := @add_cons V1 _ o1 b3525 b3473 b3468 b3538 b3520 b3550 b3549 e3364 e3367 (by rfl)
theorem e3369 : o2.add b3536 b3518=b3548 := @add_cons V1 _ o1 b3524 b3472 b3467 b3537 b3519 b3549 b3548 e3363 e3368 (by rfl)
theorem e3370 : o2.add b3535 b3517=b3547 := @add_cons V1 _ o1 b3523 b3471 b3466 b3536 b3518 b3548 b3547 e3362 e3369 (by rfl)
theorem e3371 : o2.add b3534 b3516=b3546 := @add_cons V1 _ o1 b3522 b3470 b3465 b3535 b3517 b3547 b3546 e3361 e3370 (by rfl)
theorem e3372 : o2.add b3533 b3515=b3545 := @add_cons V1 _ o1 b3464 (List.nil : V1) b3464 b3534 b3516 b3546 b3545 e3360 e3371 (by rfl)
theorem e3373 : o2.add b3532 b3514=b3544 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3533 b3515 b3545 b3544 e34 e3372 (by rfl)
theorem e3374 : o2.add b3531 b3513=b3543 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3532 b3514 b3544 b3543 e34 e3373 (by rfl)
theorem e3375 : o2.add b3530 b3512=b3542 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3531 b3513 b3543 b3542 e34 e3374 (by rfl)
theorem e3376 : o2.add b3529 b3511=b3541 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3530 b3512 b3542 b3541 e34 e3375 (by rfl)
theorem e3377 : o2.add b3528 b3475=b3540 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3529 b3511 b3541 b3540 e34 e3376 (by rfl)
theorem e3378 : o2.add b3527 b3539=b3469 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3528 b3475 b3540 b3469 e34 e3377 (by rfl)
theorem e3379 : o2.mul b2704 b60=b3469 := @mul_cons V1 _ o1 b73 b2711 b60 b3475 b3527 b3539 b3469 e3341 e3359 (by rfl) e3378
theorem e3380 : o1.mul b72 b54=b3458 := by decide
theorem e3381 : o1.mul b72 b55=b3551 := by decide
theorem e3382 : o1.mul b72 b56=b3552 := by decide
theorem e3383 : o1.mul b72 b57=b3553 := by decide
theorem e3384 : o1.mul b72 b58=b3554 := by decide
theorem e3385 : o1.mul b72 b59=b3555 := by decide
theorem e3386 : o1.scale b72 b1451=b3567 := @scale_cons V1 _ o1 b72 b59 b3555 (List.nil : V2) (List.nil : V2) b3567 e3385 e2451 (by rfl)
theorem e3387 : o1.scale b72 b1449=b3566 := @scale_cons V1 _ o1 b72 b58 b3554 b1451 b3567 b3566 e3384 e3386 (by rfl)
theorem e3388 : o1.scale b72 b1447=b3565 := @scale_cons V1 _ o1 b72 b57 b3553 b1449 b3566 b3565 e3383 e3387 (by rfl)
theorem e3389 : o1.scale b72 b1445=b3564 := @scale_cons V1 _ o1 b72 b56 b3552 b1447 b3565 b3564 e3382 e3388 (by rfl)
theorem e3390 : o1.scale b72 b1443=b3563 := @scale_cons V1 _ o1 b72 b55 b3551 b1445 b3564 b3563 e3381 e3389 (by rfl)
theorem e3391 : o1.scale b72 b1441=b3562 := @scale_cons V1 _ o1 b72 b54 b3458 b1443 b3563 b3562 e3380 e3390 (by rfl)
theorem e3392 : o1.scale b72 b1439=b3561 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1441 b3562 b3561 e2444 e3391 (by rfl)
theorem e3393 : o1.scale b72 b1437=b3560 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1439 b3561 b3560 e2444 e3392 (by rfl)
theorem e3394 : o1.scale b72 b1435=b3559 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1437 b3560 b3559 e2444 e3393 (by rfl)
theorem e3395 : o1.scale b72 b1433=b3558 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1435 b3559 b3558 e2444 e3394 (by rfl)
theorem e3396 : o1.scale b72 b1431=b3557 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1433 b3558 b3557 e2444 e3395 (by rfl)
theorem e3397 : o1.scale b72 b60=b3556 := @scale_cons V1 _ o1 b72 (List.nil : V1) (List.nil : V1) b1431 b3557 b3556 e2444 e3396 (by rfl)
theorem e3398 : o1.add b3458 (List.nil : V1)=b3458 := by rfl
theorem e3399 : o1.add b3551 b3464=b3459 := by decide
theorem e3400 : o1.add b3552 b3465=b3460 := by decide
theorem e3401 : o1.add b3553 b3466=b3461 := by decide
theorem e3402 : o1.add b3554 b3467=b3462 := by decide
theorem e3403 : o1.add b3555 b3468=b2691 := by decide
theorem e3404 : o2.add (List.nil : V2) b3550=b3550 := by rfl
theorem e3405 : o2.add b3567 b3549=b3579 := @add_cons V1 _ o1 b3555 b3468 b2691 (List.nil : V2) b3550 b3550 b3579 e3403 e3404 (by rfl)
theorem e3406 : o2.add b3566 b3548=b3578 := @add_cons V1 _ o1 b3554 b3467 b3462 b3567 b3549 b3579 b3578 e3402 e3405 (by rfl)
theorem e3407 : o2.add b3565 b3547=b3577 := @add_cons V1 _ o1 b3553 b3466 b3461 b3566 b3548 b3578 b3577 e3401 e3406 (by rfl)
theorem e3408 : o2.add b3564 b3546=b3576 := @add_cons V1 _ o1 b3552 b3465 b3460 b3565 b3547 b3577 b3576 e3400 e3407 (by rfl)
theorem e3409 : o2.add b3563 b3545=b3575 := @add_cons V1 _ o1 b3551 b3464 b3459 b3564 b3546 b3576 b3575 e3399 e3408 (by rfl)
theorem e3410 : o2.add b3562 b3544=b3574 := @add_cons V1 _ o1 b3458 (List.nil : V1) b3458 b3563 b3545 b3575 b3574 e3398 e3409 (by rfl)
theorem e3411 : o2.add b3561 b3543=b3573 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3562 b3544 b3574 b3573 e34 e3410 (by rfl)
theorem e3412 : o2.add b3560 b3542=b3572 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3561 b3543 b3573 b3572 e34 e3411 (by rfl)
theorem e3413 : o2.add b3559 b3541=b3571 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3560 b3542 b3572 b3571 e34 e3412 (by rfl)
theorem e3414 : o2.add b3558 b3540=b3570 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3559 b3541 b3571 b3570 e34 e3413 (by rfl)
theorem e3415 : o2.add b3557 b3469=b3569 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3558 b3540 b3570 b3569 e34 e3414 (by rfl)
theorem e3416 : o2.add b3556 b3568=b3463 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3557 b3469 b3569 b3463 e34 e3415 (by rfl)
theorem e3417 : o2.mul b2697 b60=b3463 := @mul_cons V1 _ o1 b72 b2704 b60 b3469 b3556 b3568 b3463 e3379 e3397 (by rfl) e3416
theorem e3418 : o1.mul b71 b54=b2685 := by decide
theorem e3419 : o1.mul b71 b55=b3580 := by decide
theorem e3420 : o1.mul b71 b56=b3581 := by decide
theorem e3421 : o1.mul b71 b57=b3582 := by decide
theorem e3422 : o1.mul b71 b58=b3583 := by decide
theorem e3423 : o1.mul b71 b59=b3584 := by decide
theorem e3424 : o1.scale b71 b1451=b3596 := @scale_cons V1 _ o1 b71 b59 b3584 (List.nil : V2) (List.nil : V2) b3596 e3423 e2481 (by rfl)
theorem e3425 : o1.scale b71 b1449=b3595 := @scale_cons V1 _ o1 b71 b58 b3583 b1451 b3596 b3595 e3422 e3424 (by rfl)
theorem e3426 : o1.scale b71 b1447=b3594 := @scale_cons V1 _ o1 b71 b57 b3582 b1449 b3595 b3594 e3421 e3425 (by rfl)
theorem e3427 : o1.scale b71 b1445=b3593 := @scale_cons V1 _ o1 b71 b56 b3581 b1447 b3594 b3593 e3420 e3426 (by rfl)
theorem e3428 : o1.scale b71 b1443=b3592 := @scale_cons V1 _ o1 b71 b55 b3580 b1445 b3593 b3592 e3419 e3427 (by rfl)
theorem e3429 : o1.scale b71 b1441=b3591 := @scale_cons V1 _ o1 b71 b54 b2685 b1443 b3592 b3591 e3418 e3428 (by rfl)
theorem e3430 : o1.scale b71 b1439=b3590 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1441 b3591 b3590 e2474 e3429 (by rfl)
theorem e3431 : o1.scale b71 b1437=b3589 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1439 b3590 b3589 e2474 e3430 (by rfl)
theorem e3432 : o1.scale b71 b1435=b3588 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1437 b3589 b3588 e2474 e3431 (by rfl)
theorem e3433 : o1.scale b71 b1433=b3587 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1435 b3588 b3587 e2474 e3432 (by rfl)
theorem e3434 : o1.scale b71 b1431=b3586 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1433 b3587 b3586 e2474 e3433 (by rfl)
theorem e3435 : o1.scale b71 b60=b3585 := @scale_cons V1 _ o1 b71 (List.nil : V1) (List.nil : V1) b1431 b3586 b3585 e2474 e3434 (by rfl)
theorem e3436 : o1.add b2685 (List.nil : V1)=b2685 := by rfl
theorem e3437 : o1.add b3580 b3458=b2686 := by decide
theorem e3438 : o1.add b3581 b3459=b2687 := by decide
theorem e3439 : o1.add b3582 b3460=b2688 := by decide
theorem e3440 : o1.add b3583 b3461=b2689 := by decide
theorem e3441 : o1.add b3584 b3462=b2690 := by decide
theorem e3442 : o2.add (List.nil : V2) b3579=b3579 := by rfl
theorem e3443 : o2.add b3596 b3578=b3608 := @add_cons V1 _ o1 b3584 b3462 b2690 (List.nil : V2) b3579 b3579 b3608 e3441 e3442 (by rfl)
theorem e3444 : o2.add b3595 b3577=b3607 := @add_cons V1 _ o1 b3583 b3461 b2689 b3596 b3578 b3608 b3607 e3440 e3443 (by rfl)
theorem e3445 : o2.add b3594 b3576=b3606 := @add_cons V1 _ o1 b3582 b3460 b2688 b3595 b3577 b3607 b3606 e3439 e3444 (by rfl)
theorem e3446 : o2.add b3593 b3575=b3605 := @add_cons V1 _ o1 b3581 b3459 b2687 b3594 b3576 b3606 b3605 e3438 e3445 (by rfl)
theorem e3447 : o2.add b3592 b3574=b3604 := @add_cons V1 _ o1 b3580 b3458 b2686 b3593 b3575 b3605 b3604 e3437 e3446 (by rfl)
theorem e3448 : o2.add b3591 b3573=b3603 := @add_cons V1 _ o1 b2685 (List.nil : V1) b2685 b3592 b3574 b3604 b3603 e3436 e3447 (by rfl)
theorem e3449 : o2.add b3590 b3572=b3602 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3591 b3573 b3603 b3602 e34 e3448 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
