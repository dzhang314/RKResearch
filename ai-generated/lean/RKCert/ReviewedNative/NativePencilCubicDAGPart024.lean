module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart023

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3450 : o2.add b3589 b3571=b3601 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3590 b3572 b3602 b3601 e34 e3449 (by rfl)
theorem e3451 : o2.add b3588 b3570=b3600 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3589 b3571 b3601 b3600 e34 e3450 (by rfl)
theorem e3452 : o2.add b3587 b3569=b3599 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3588 b3570 b3600 b3599 e34 e3451 (by rfl)
theorem e3453 : o2.add b3586 b3463=b3598 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3587 b3569 b3599 b3598 e34 e3452 (by rfl)
theorem e3454 : o2.add b3585 b3597=b2695 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3586 b3463 b3598 b2695 e34 e3453 (by rfl)
theorem e3455 : o2.mul b76 b60=b2695 := @mul_cons V1 _ o1 b71 b2697 b60 b3463 b3585 b3597 b2695 e3417 e3435 (by rfl) e3454
theorem e3456 : o2.scale b76 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e3457 : o2.scale b76 b1405=b3457 := @scale_cons V2 _ o2 b76 b60 b2695 (List.nil : V3) (List.nil : V3) b3457 e3455 e3456 (by rfl)
theorem e3458 : o2.scale b76 b1247=b3311 := @scale_cons V2 _ o2 b76 b53 b2684 b1405 b3457 b3311 e3283 e3457 (by rfl)
theorem e3459 : o2.scale b76 b1099=b3174 := @scale_cons V2 _ o2 b76 b47 b2673 b1247 b3311 b3174 e3112 e3458 (by rfl)
theorem e3460 : o2.scale b76 b957=b3042 := @scale_cons V2 _ o2 b76 b41 b2662 b1099 b3174 b3042 e2950 e3459 (by rfl)
theorem e3461 : o2.scale b76 b825=b2919 := @scale_cons V2 _ o2 b76 b34 b2651 b957 b3042 b2919 e2792 e3460 (by rfl)
theorem e3462 : o2.scale b76 b703=b2805 := @scale_cons V2 _ o2 b76 b27 b2640 b825 b2919 b2805 e2643 e3461 (by rfl)
theorem e3463 : o2.scale b76 b61=b2696 := @scale_cons V2 _ o2 b76 b20 b348 b703 b2805 b2696 e2503 e3462 (by rfl)
theorem e3464 : o2.add b348 (List.nil : V2)=b348 := by rfl
theorem e3465 : o1.add b2630 b454=b349 := by decide
theorem e3466 : o1.add b2631 b455=b350 := by decide
theorem e3467 : o1.add b2632 b456=b351 := by decide
theorem e3468 : o1.add b2633 b457=b352 := by decide
theorem e3469 : o1.add b2634 b458=b353 := by decide
theorem e3470 : o1.add b2635 b459=b354 := by decide
theorem e3471 : o1.add b2636 b460=b355 := by decide
theorem e3472 : o1.add b2637 b461=b356 := by decide
theorem e3473 : o1.add b2638 b462=b357 := by decide
theorem e3474 : o1.add b2639 b463=b358 := by decide
theorem e3475 : o2.add b2835 (List.nil : V2)=b2835 := by rfl
theorem e3476 : o2.add b2855 b1669=b3620 := @add_cons V1 _ o1 b2639 b463 b358 b2835 (List.nil : V2) b2835 b3620 e3474 e3475 (by rfl)
theorem e3477 : o2.add b2876 b1688=b3619 := @add_cons V1 _ o1 b2638 b462 b357 b2855 b1669 b3620 b3619 e3473 e3476 (by rfl)
theorem e3478 : o2.add b2897 b1707=b3618 := @add_cons V1 _ o1 b2637 b461 b356 b2876 b1688 b3619 b3618 e3472 e3477 (by rfl)
theorem e3479 : o2.add b2918 b1726=b3617 := @add_cons V1 _ o1 b2636 b460 b355 b2897 b1707 b3618 b3617 e3471 e3478 (by rfl)
theorem e3480 : o2.add b2917 b1743=b3616 := @add_cons V1 _ o1 b2635 b459 b354 b2918 b1726 b3617 b3616 e3470 e3479 (by rfl)
theorem e3481 : o2.add b2916 b1742=b3615 := @add_cons V1 _ o1 b2634 b458 b353 b2917 b1743 b3616 b3615 e3469 e3480 (by rfl)
theorem e3482 : o2.add b2915 b1741=b3614 := @add_cons V1 _ o1 b2633 b457 b352 b2916 b1742 b3615 b3614 e3468 e3481 (by rfl)
theorem e3483 : o2.add b2914 b1740=b3613 := @add_cons V1 _ o1 b2632 b456 b351 b2915 b1741 b3614 b3613 e3467 e3482 (by rfl)
theorem e3484 : o2.add b2913 b1739=b3612 := @add_cons V1 _ o1 b2631 b455 b350 b2914 b1740 b3613 b3612 e3466 e3483 (by rfl)
theorem e3485 : o2.add b2912 b1738=b3611 := @add_cons V1 _ o1 b2630 b454 b349 b2913 b1739 b3612 b3611 e3465 e3484 (by rfl)
theorem e3486 : o2.add b2640 b464=b360 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b2912 b1738 b3611 b360 e34 e3485 (by rfl)
theorem e3487 : o1.add (List.nil : V1) b361=b361 := by rfl
theorem e3488 : o1.add b2641 b465=b362 := by decide
theorem e3489 : o1.add b2642 b466=b363 := by decide
theorem e3490 : o1.add b2643 b467=b364 := by decide
theorem e3491 : o1.add b2644 b468=b365 := by decide
theorem e3492 : o1.add b2645 b469=b366 := by decide
theorem e3493 : o1.add b2646 b470=b367 := by decide
theorem e3494 : o1.add b2647 b471=b368 := by decide
theorem e3495 : o1.add b2648 b472=b369 := by decide
theorem e3496 : o1.add b2649 b473=b370 := by decide
theorem e3497 : o1.add b2650 b474=b371 := by decide
theorem e3498 : o2.add b2950 (List.nil : V2)=b2950 := by rfl
theorem e3499 : o2.add b2972 b1774=b3632 := @add_cons V1 _ o1 b2650 b474 b371 b2950 (List.nil : V2) b2950 b3632 e3497 e3498 (by rfl)
theorem e3500 : o2.add b2995 b2559=b3631 := @add_cons V1 _ o1 b2649 b473 b370 b2972 b1774 b3632 b3631 e3496 e3499 (by rfl)
theorem e3501 : o2.add b3018 b2558=b3630 := @add_cons V1 _ o1 b2648 b472 b369 b2995 b2559 b3631 b3630 e3495 e3500 (by rfl)
theorem e3502 : o2.add b3041 b2557=b3629 := @add_cons V1 _ o1 b2647 b471 b368 b3018 b2558 b3630 b3629 e3494 e3501 (by rfl)
theorem e3503 : o2.add b3040 b2556=b3628 := @add_cons V1 _ o1 b2646 b470 b367 b3041 b2557 b3629 b3628 e3493 e3502 (by rfl)
theorem e3504 : o2.add b3039 b2555=b3627 := @add_cons V1 _ o1 b2645 b469 b366 b3040 b2556 b3628 b3627 e3492 e3503 (by rfl)
theorem e3505 : o2.add b3038 b2554=b3626 := @add_cons V1 _ o1 b2644 b468 b365 b3039 b2555 b3627 b3626 e3491 e3504 (by rfl)
theorem e3506 : o2.add b3037 b2553=b3625 := @add_cons V1 _ o1 b2643 b467 b364 b3038 b2554 b3626 b3625 e3490 e3505 (by rfl)
theorem e3507 : o2.add b3036 b2552=b3624 := @add_cons V1 _ o1 b2642 b466 b363 b3037 b2553 b3625 b3624 e3489 e3506 (by rfl)
theorem e3508 : o2.add b3035 b2551=b3623 := @add_cons V1 _ o1 b2641 b465 b362 b3036 b2552 b3624 b3623 e3488 e3507 (by rfl)
theorem e3509 : o2.add b3034 b2550=b3622 := @add_cons V1 _ o1 (List.nil : V1) b361 b361 b3035 b2551 b3623 b3622 e3487 e3508 (by rfl)
theorem e3510 : o2.add b2651 b475=b373 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3034 b2550 b3622 b373 e34 e3509 (by rfl)
theorem e3511 : o1.add (List.nil : V1) b375=b375 := by rfl
theorem e3512 : o1.add b2652 b476=b376 := by decide
theorem e3513 : o1.add b2653 b477=b377 := by decide
theorem e3514 : o1.add b2654 b478=b378 := by decide
theorem e3515 : o1.add b2655 b479=b379 := by decide
theorem e3516 : o1.add b2656 b480=b380 := by decide
theorem e3517 : o1.add b2657 b481=b381 := by decide
theorem e3518 : o1.add b2658 b482=b382 := by decide
theorem e3519 : o1.add b2659 b483=b383 := by decide
theorem e3520 : o1.add b2660 b484=b384 := by decide
theorem e3521 : o1.add b2661 b485=b385 := by decide
theorem e3522 : o2.add b3074 (List.nil : V2)=b3074 := by rfl
theorem e3523 : o2.add b3098 b1889=b3645 := @add_cons V1 _ o1 b2661 b485 b385 b3074 (List.nil : V2) b3074 b3645 e3521 e3522 (by rfl)
theorem e3524 : o2.add b3123 b2571=b3644 := @add_cons V1 _ o1 b2660 b484 b384 b3098 b1889 b3645 b3644 e3520 e3523 (by rfl)
theorem e3525 : o2.add b3148 b2570=b3643 := @add_cons V1 _ o1 b2659 b483 b383 b3123 b2571 b3644 b3643 e3519 e3524 (by rfl)
theorem e3526 : o2.add b3173 b2569=b3642 := @add_cons V1 _ o1 b2658 b482 b382 b3148 b2570 b3643 b3642 e3518 e3525 (by rfl)
theorem e3527 : o2.add b3172 b2568=b3641 := @add_cons V1 _ o1 b2657 b481 b381 b3173 b2569 b3642 b3641 e3517 e3526 (by rfl)
theorem e3528 : o2.add b3171 b2567=b3640 := @add_cons V1 _ o1 b2656 b480 b380 b3172 b2568 b3641 b3640 e3516 e3527 (by rfl)
theorem e3529 : o2.add b3170 b2566=b3639 := @add_cons V1 _ o1 b2655 b479 b379 b3171 b2567 b3640 b3639 e3515 e3528 (by rfl)
theorem e3530 : o2.add b3169 b2565=b3638 := @add_cons V1 _ o1 b2654 b478 b378 b3170 b2566 b3639 b3638 e3514 e3529 (by rfl)
theorem e3531 : o2.add b3168 b2564=b3637 := @add_cons V1 _ o1 b2653 b477 b377 b3169 b2565 b3638 b3637 e3513 e3530 (by rfl)
theorem e3532 : o2.add b3167 b2563=b3636 := @add_cons V1 _ o1 b2652 b476 b376 b3168 b2564 b3637 b3636 e3512 e3531 (by rfl)
theorem e3533 : o2.add b3166 b2562=b3635 := @add_cons V1 _ o1 (List.nil : V1) b375 b375 b3167 b2563 b3636 b3635 e3511 e3532 (by rfl)
theorem e3534 : o2.add b3165 b2561=b3634 := @add_cons V1 _ o1 (List.nil : V1) b374 b374 b3166 b2562 b3635 b3634 e2228 e3533 (by rfl)
theorem e3535 : o2.add b2662 b486=b387 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3165 b2561 b3634 b387 e34 e3534 (by rfl)
theorem e3536 : o1.add (List.nil : V1) b389=b389 := by rfl
theorem e3537 : o1.add b2663 b487=b390 := by decide
theorem e3538 : o1.add b2664 b488=b391 := by decide
theorem e3539 : o1.add b2665 b489=b392 := by decide
theorem e3540 : o1.add b2666 b490=b393 := by decide
theorem e3541 : o1.add b2667 b491=b394 := by decide
theorem e3542 : o1.add b2668 b492=b395 := by decide
theorem e3543 : o1.add b2669 b493=b396 := by decide
theorem e3544 : o1.add b2670 b494=b397 := by decide
theorem e3545 : o1.add b2671 b495=b398 := by decide
theorem e3546 : o1.add b2672 b496=b399 := by decide
theorem e3547 : o2.add b3203 (List.nil : V2)=b3203 := by rfl
theorem e3548 : o2.add b3229 b2013=b3659 := @add_cons V1 _ o1 b2672 b496 b399 b3203 (List.nil : V2) b3203 b3659 e3546 e3547 (by rfl)
theorem e3549 : o2.add b3256 b2584=b3658 := @add_cons V1 _ o1 b2671 b495 b398 b3229 b2013 b3659 b3658 e3545 e3548 (by rfl)
theorem e3550 : o2.add b3283 b2583=b3657 := @add_cons V1 _ o1 b2670 b494 b397 b3256 b2584 b3658 b3657 e3544 e3549 (by rfl)
theorem e3551 : o2.add b3310 b2582=b3656 := @add_cons V1 _ o1 b2669 b493 b396 b3283 b2583 b3657 b3656 e3543 e3550 (by rfl)
theorem e3552 : o2.add b3309 b2581=b3655 := @add_cons V1 _ o1 b2668 b492 b395 b3310 b2582 b3656 b3655 e3542 e3551 (by rfl)
theorem e3553 : o2.add b3308 b2580=b3654 := @add_cons V1 _ o1 b2667 b491 b394 b3309 b2581 b3655 b3654 e3541 e3552 (by rfl)
theorem e3554 : o2.add b3307 b2579=b3653 := @add_cons V1 _ o1 b2666 b490 b393 b3308 b2580 b3654 b3653 e3540 e3553 (by rfl)
theorem e3555 : o2.add b3306 b2578=b3652 := @add_cons V1 _ o1 b2665 b489 b392 b3307 b2579 b3653 b3652 e3539 e3554 (by rfl)
theorem e3556 : o2.add b3305 b2577=b3651 := @add_cons V1 _ o1 b2664 b488 b391 b3306 b2578 b3652 b3651 e3538 e3555 (by rfl)
theorem e3557 : o2.add b3304 b2576=b3650 := @add_cons V1 _ o1 b2663 b487 b390 b3305 b2577 b3651 b3650 e3537 e3556 (by rfl)
theorem e3558 : o2.add b3303 b2575=b3649 := @add_cons V1 _ o1 (List.nil : V1) b389 b389 b3304 b2576 b3650 b3649 e3536 e3557 (by rfl)
theorem e3559 : o2.add b3302 b2574=b3648 := @add_cons V1 _ o1 (List.nil : V1) b388 b388 b3303 b2575 b3649 b3648 e2252 e3558 (by rfl)
theorem e3560 : o2.add b3301 b2573=b3647 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3302 b2574 b3648 b3647 e34 e3559 (by rfl)
theorem e3561 : o2.add b2673 b497=b401 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3301 b2573 b3647 b401 e34 e3560 (by rfl)
theorem e3562 : o1.add (List.nil : V1) b403=b403 := by rfl
theorem e3563 : o1.add b2674 b498=b404 := by decide
theorem e3564 : o1.add b2675 b499=b405 := by decide
theorem e3565 : o1.add b2676 b500=b406 := by decide
theorem e3566 : o1.add b2677 b501=b407 := by decide
theorem e3567 : o1.add b2678 b502=b408 := by decide
theorem e3568 : o1.add b2679 b503=b409 := by decide
theorem e3569 : o1.add b2680 b504=b410 := by decide
theorem e3570 : o1.add b2681 b505=b411 := by decide
theorem e3571 : o1.add b2682 b506=b412 := by decide
theorem e3572 : o1.add b2683 b507=b413 := by decide
theorem e3573 : o2.add b3341 (List.nil : V2)=b3341 := by rfl
theorem e3574 : o2.add b3369 b2142=b3674 := @add_cons V1 _ o1 b2683 b507 b413 b3341 (List.nil : V2) b3341 b3674 e3572 e3573 (by rfl)
theorem e3575 : o2.add b3398 b2598=b3673 := @add_cons V1 _ o1 b2682 b506 b412 b3369 b2142 b3674 b3673 e3571 e3574 (by rfl)
theorem e3576 : o2.add b3427 b2597=b3672 := @add_cons V1 _ o1 b2681 b505 b411 b3398 b2598 b3673 b3672 e3570 e3575 (by rfl)
theorem e3577 : o2.add b3456 b2596=b3671 := @add_cons V1 _ o1 b2680 b504 b410 b3427 b2597 b3672 b3671 e3569 e3576 (by rfl)
theorem e3578 : o2.add b3455 b2595=b3670 := @add_cons V1 _ o1 b2679 b503 b409 b3456 b2596 b3671 b3670 e3568 e3577 (by rfl)
theorem e3579 : o2.add b3454 b2594=b3669 := @add_cons V1 _ o1 b2678 b502 b408 b3455 b2595 b3670 b3669 e3567 e3578 (by rfl)
theorem e3580 : o2.add b3453 b2593=b3668 := @add_cons V1 _ o1 b2677 b501 b407 b3454 b2594 b3669 b3668 e3566 e3579 (by rfl)
theorem e3581 : o2.add b3452 b2592=b3667 := @add_cons V1 _ o1 b2676 b500 b406 b3453 b2593 b3668 b3667 e3565 e3580 (by rfl)
theorem e3582 : o2.add b3451 b2591=b3666 := @add_cons V1 _ o1 b2675 b499 b405 b3452 b2592 b3667 b3666 e3564 e3581 (by rfl)
theorem e3583 : o2.add b3450 b2590=b3665 := @add_cons V1 _ o1 b2674 b498 b404 b3451 b2591 b3666 b3665 e3563 e3582 (by rfl)
theorem e3584 : o2.add b3449 b2589=b3664 := @add_cons V1 _ o1 (List.nil : V1) b403 b403 b3450 b2590 b3665 b3664 e3562 e3583 (by rfl)
theorem e3585 : o2.add b3448 b2588=b3663 := @add_cons V1 _ o1 (List.nil : V1) b402 b402 b3449 b2589 b3664 b3663 e2277 e3584 (by rfl)
theorem e3586 : o2.add b3447 b2587=b3662 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3448 b2588 b3663 b3662 e34 e3585 (by rfl)
theorem e3587 : o2.add b3446 b2586=b3661 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3447 b2587 b3662 b3661 e34 e3586 (by rfl)
theorem e3588 : o2.add b2684 b508=b415 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3446 b2586 b3661 b415 e34 e3587 (by rfl)
theorem e3589 : o1.add (List.nil : V1) b417=b417 := by rfl
theorem e3590 : o1.add b2685 b509=b418 := by decide
theorem e3591 : o1.add b2686 b510=b419 := by decide
theorem e3592 : o1.add b2687 b511=b420 := by decide
theorem e3593 : o1.add b2688 b512=b421 := by decide
theorem e3594 : o1.add b2689 b513=b422 := by decide
theorem e3595 : o1.add b2690 b514=b423 := by decide
theorem e3596 : o1.add b2691 b515=b424 := by decide
theorem e3597 : o1.add b2692 b516=b425 := by decide
theorem e3598 : o1.add b2693 b517=b426 := by decide
theorem e3599 : o1.add b2694 b518=b427 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
