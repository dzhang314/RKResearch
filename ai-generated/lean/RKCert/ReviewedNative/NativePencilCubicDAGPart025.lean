module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart024

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3600 : o2.add b3492 b2280=b3690 := @add_cons V1 _ o1 b2694 b518 b427 (List.nil : V2) (List.nil : V2) (List.nil : V2) b3690 e3599 e2341 (by rfl)
theorem e3601 : o2.add b3521 b2613=b3689 := @add_cons V1 _ o1 b2693 b517 b426 b3492 b2280 b3690 b3689 e3598 e3600 (by rfl)
theorem e3602 : o2.add b3550 b2612=b3688 := @add_cons V1 _ o1 b2692 b516 b425 b3521 b2613 b3689 b3688 e3597 e3601 (by rfl)
theorem e3603 : o2.add b3579 b2611=b3687 := @add_cons V1 _ o1 b2691 b515 b424 b3550 b2612 b3688 b3687 e3596 e3602 (by rfl)
theorem e3604 : o2.add b3608 b2610=b3686 := @add_cons V1 _ o1 b2690 b514 b423 b3579 b2611 b3687 b3686 e3595 e3603 (by rfl)
theorem e3605 : o2.add b3607 b2609=b3685 := @add_cons V1 _ o1 b2689 b513 b422 b3608 b2610 b3686 b3685 e3594 e3604 (by rfl)
theorem e3606 : o2.add b3606 b2608=b3684 := @add_cons V1 _ o1 b2688 b512 b421 b3607 b2609 b3685 b3684 e3593 e3605 (by rfl)
theorem e3607 : o2.add b3605 b2607=b3683 := @add_cons V1 _ o1 b2687 b511 b420 b3606 b2608 b3684 b3683 e3592 e3606 (by rfl)
theorem e3608 : o2.add b3604 b2606=b3682 := @add_cons V1 _ o1 b2686 b510 b419 b3605 b2607 b3683 b3682 e3591 e3607 (by rfl)
theorem e3609 : o2.add b3603 b2605=b3681 := @add_cons V1 _ o1 b2685 b509 b418 b3604 b2606 b3682 b3681 e3590 e3608 (by rfl)
theorem e3610 : o2.add b3602 b2604=b3680 := @add_cons V1 _ o1 (List.nil : V1) b417 b417 b3603 b2605 b3681 b3680 e3589 e3609 (by rfl)
theorem e3611 : o2.add b3601 b2603=b3679 := @add_cons V1 _ o1 (List.nil : V1) b416 b416 b3602 b2604 b3680 b3679 e2303 e3610 (by rfl)
theorem e3612 : o2.add b3600 b2602=b3678 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3601 b2603 b3679 b3678 e34 e3611 (by rfl)
theorem e3613 : o2.add b3599 b2601=b3677 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3600 b2602 b3678 b3677 e34 e3612 (by rfl)
theorem e3614 : o2.add b3598 b2600=b3676 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3599 b2601 b3677 b3676 e34 e3613 (by rfl)
theorem e3615 : o2.add b2695 b519=b428 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b3598 b2600 b3676 b428 e34 e3614 (by rfl)
theorem e3616 : o3.add (List.nil : V3) b2614=b2614 := by rfl
theorem e3617 : o3.add b3457 b2599=b3675 := @add_cons V2 _ o2 b2695 b519 b428 (List.nil : V3) b2614 b2614 b3675 e3615 e3616 (by rfl)
theorem e3618 : o3.add b3311 b2585=b3660 := @add_cons V2 _ o2 b2684 b508 b415 b3457 b2599 b3675 b3660 e3588 e3617 (by rfl)
theorem e3619 : o3.add b3174 b2572=b3646 := @add_cons V2 _ o2 b2673 b497 b401 b3311 b2585 b3660 b3646 e3561 e3618 (by rfl)
theorem e3620 : o3.add b3042 b2560=b3633 := @add_cons V2 _ o2 b2662 b486 b387 b3174 b2572 b3646 b3633 e3535 e3619 (by rfl)
theorem e3621 : o3.add b2919 b2549=b3621 := @add_cons V2 _ o2 b2651 b475 b373 b3042 b2560 b3633 b3621 e3510 e3620 (by rfl)
theorem e3622 : o3.add b2805 b520=b3610 := @add_cons V2 _ o2 b2640 b464 b360 b2919 b2549 b3621 b3610 e3486 e3621 (by rfl)
theorem e3623 : o3.add b2696 b3609=b452 := @add_cons V2 _ o2 b348 (List.nil : V2) b348 b2805 b520 b3610 b452 e3464 e3622 (by rfl)
theorem e3624 : o3.mul b89 b61=b452 := @mul_cons V2 _ o2 b76 b453 b61 b520 b2696 b3609 b452 e2366 e3463 (by rfl) e3623
theorem e3625 : o3.mul (List.nil : V3) b5=(List.nil : V3) := by rfl
theorem e3626 : o2.mul (List.nil : V2) b4=(List.nil : V2) := by rfl
theorem e3627 : o1.mul b218 b3=b3819 := by decide
theorem e3628 : o1.scale b218 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3629 : o1.scale b218 b4=b3867 := @scale_cons V1 _ o1 b218 b3 b3819 (List.nil : V2) (List.nil : V2) b3867 e3627 e3628 (by rfl)
theorem e3630 : o2.add b3867 (List.nil : V2)=b3867 := by rfl
theorem e3631 : o2.mul b3866 b4=b3867 := @mul_cons V1 _ o1 b218 (List.nil : V2) b4 (List.nil : V2) b3867 (List.nil : V2) b3867 e3626 e3629 (by rfl) e3630
theorem e3632 : o1.mul b217 b3=b3818 := by decide
theorem e3633 : o1.scale b217 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3634 : o1.scale b217 b4=b3868 := @scale_cons V1 _ o1 b217 b3 b3818 (List.nil : V2) (List.nil : V2) b3868 e3632 e3633 (by rfl)
theorem e3635 : o1.add b3818 (List.nil : V1)=b3818 := by rfl
theorem e3636 : o2.add (List.nil : V2) b3867=b3867 := by rfl
theorem e3637 : o2.add b3868 b3869=b3865 := @add_cons V1 _ o1 b3818 (List.nil : V1) b3818 (List.nil : V2) b3867 b3867 b3865 e3635 e3636 (by rfl)
theorem e3638 : o2.mul b3864 b4=b3865 := @mul_cons V1 _ o1 b217 b3866 b4 b3867 b3868 b3869 b3865 e3631 e3634 (by rfl) e3637
theorem e3639 : o1.mul b216 b3=b3817 := by decide
theorem e3640 : o1.scale b216 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3641 : o1.scale b216 b4=b3870 := @scale_cons V1 _ o1 b216 b3 b3817 (List.nil : V2) (List.nil : V2) b3870 e3639 e3640 (by rfl)
theorem e3642 : o1.add b3817 (List.nil : V1)=b3817 := by rfl
theorem e3643 : o2.add (List.nil : V2) b3865=b3865 := by rfl
theorem e3644 : o2.add b3870 b3871=b3863 := @add_cons V1 _ o1 b3817 (List.nil : V1) b3817 (List.nil : V2) b3865 b3865 b3863 e3642 e3643 (by rfl)
theorem e3645 : o2.mul b3862 b4=b3863 := @mul_cons V1 _ o1 b216 b3864 b4 b3865 b3870 b3871 b3863 e3638 e3641 (by rfl) e3644
theorem e3646 : o1.mul b215 b3=b3816 := by decide
theorem e3647 : o1.scale b215 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3648 : o1.scale b215 b4=b3872 := @scale_cons V1 _ o1 b215 b3 b3816 (List.nil : V2) (List.nil : V2) b3872 e3646 e3647 (by rfl)
theorem e3649 : o1.add b3816 (List.nil : V1)=b3816 := by rfl
theorem e3650 : o2.add (List.nil : V2) b3863=b3863 := by rfl
theorem e3651 : o2.add b3872 b3873=b3861 := @add_cons V1 _ o1 b3816 (List.nil : V1) b3816 (List.nil : V2) b3863 b3863 b3861 e3649 e3650 (by rfl)
theorem e3652 : o2.mul b3860 b4=b3861 := @mul_cons V1 _ o1 b215 b3862 b4 b3863 b3872 b3873 b3861 e3645 e3648 (by rfl) e3651
theorem e3653 : o1.mul b214 b3=b3815 := by decide
theorem e3654 : o1.scale b214 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3655 : o1.scale b214 b4=b3874 := @scale_cons V1 _ o1 b214 b3 b3815 (List.nil : V2) (List.nil : V2) b3874 e3653 e3654 (by rfl)
theorem e3656 : o1.add b3815 (List.nil : V1)=b3815 := by rfl
theorem e3657 : o2.add (List.nil : V2) b3861=b3861 := by rfl
theorem e3658 : o2.add b3874 b3875=b3859 := @add_cons V1 _ o1 b3815 (List.nil : V1) b3815 (List.nil : V2) b3861 b3861 b3859 e3656 e3657 (by rfl)
theorem e3659 : o2.mul b3858 b4=b3859 := @mul_cons V1 _ o1 b214 b3860 b4 b3861 b3874 b3875 b3859 e3652 e3655 (by rfl) e3658
theorem e3660 : o1.mul b213 b3=b3814 := by decide
theorem e3661 : o1.scale b213 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3662 : o1.scale b213 b4=b3876 := @scale_cons V1 _ o1 b213 b3 b3814 (List.nil : V2) (List.nil : V2) b3876 e3660 e3661 (by rfl)
theorem e3663 : o1.add b3814 (List.nil : V1)=b3814 := by rfl
theorem e3664 : o2.add (List.nil : V2) b3859=b3859 := by rfl
theorem e3665 : o2.add b3876 b3877=b3857 := @add_cons V1 _ o1 b3814 (List.nil : V1) b3814 (List.nil : V2) b3859 b3859 b3857 e3663 e3664 (by rfl)
theorem e3666 : o2.mul b3856 b4=b3857 := @mul_cons V1 _ o1 b213 b3858 b4 b3859 b3876 b3877 b3857 e3659 e3662 (by rfl) e3665
theorem e3667 : o1.mul b212 b3=b3813 := by decide
theorem e3668 : o1.scale b212 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3669 : o1.scale b212 b4=b3878 := @scale_cons V1 _ o1 b212 b3 b3813 (List.nil : V2) (List.nil : V2) b3878 e3667 e3668 (by rfl)
theorem e3670 : o1.add b3813 (List.nil : V1)=b3813 := by rfl
theorem e3671 : o2.add (List.nil : V2) b3857=b3857 := by rfl
theorem e3672 : o2.add b3878 b3879=b3855 := @add_cons V1 _ o1 b3813 (List.nil : V1) b3813 (List.nil : V2) b3857 b3857 b3855 e3670 e3671 (by rfl)
theorem e3673 : o2.mul b3854 b4=b3855 := @mul_cons V1 _ o1 b212 b3856 b4 b3857 b3878 b3879 b3855 e3666 e3669 (by rfl) e3672
theorem e3674 : o1.mul b211 b3=b3812 := by decide
theorem e3675 : o1.scale b211 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3676 : o1.scale b211 b4=b3880 := @scale_cons V1 _ o1 b211 b3 b3812 (List.nil : V2) (List.nil : V2) b3880 e3674 e3675 (by rfl)
theorem e3677 : o1.add b3812 (List.nil : V1)=b3812 := by rfl
theorem e3678 : o2.add (List.nil : V2) b3855=b3855 := by rfl
theorem e3679 : o2.add b3880 b3881=b3853 := @add_cons V1 _ o1 b3812 (List.nil : V1) b3812 (List.nil : V2) b3855 b3855 b3853 e3677 e3678 (by rfl)
theorem e3680 : o2.mul b3852 b4=b3853 := @mul_cons V1 _ o1 b211 b3854 b4 b3855 b3880 b3881 b3853 e3673 e3676 (by rfl) e3679
theorem e3681 : o1.mul b210 b3=b3811 := by decide
theorem e3682 : o1.scale b210 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3683 : o1.scale b210 b4=b3882 := @scale_cons V1 _ o1 b210 b3 b3811 (List.nil : V2) (List.nil : V2) b3882 e3681 e3682 (by rfl)
theorem e3684 : o1.add b3811 (List.nil : V1)=b3811 := by rfl
theorem e3685 : o2.add (List.nil : V2) b3853=b3853 := by rfl
theorem e3686 : o2.add b3882 b3883=b3851 := @add_cons V1 _ o1 b3811 (List.nil : V1) b3811 (List.nil : V2) b3853 b3853 b3851 e3684 e3685 (by rfl)
theorem e3687 : o2.mul b3850 b4=b3851 := @mul_cons V1 _ o1 b210 b3852 b4 b3853 b3882 b3883 b3851 e3680 e3683 (by rfl) e3686
theorem e3688 : o1.mul b209 b3=b3810 := by decide
theorem e3689 : o1.scale b209 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3690 : o1.scale b209 b4=b3884 := @scale_cons V1 _ o1 b209 b3 b3810 (List.nil : V2) (List.nil : V2) b3884 e3688 e3689 (by rfl)
theorem e3691 : o1.add b3810 (List.nil : V1)=b3810 := by rfl
theorem e3692 : o2.add (List.nil : V2) b3851=b3851 := by rfl
theorem e3693 : o2.add b3884 b3885=b3849 := @add_cons V1 _ o1 b3810 (List.nil : V1) b3810 (List.nil : V2) b3851 b3851 b3849 e3691 e3692 (by rfl)
theorem e3694 : o2.mul b3848 b4=b3849 := @mul_cons V1 _ o1 b209 b3850 b4 b3851 b3884 b3885 b3849 e3687 e3690 (by rfl) e3693
theorem e3695 : o1.mul (List.nil : V1) b3=(List.nil : V1) := by rfl
theorem e3696 : o1.scale (List.nil : V1) (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3697 : o1.scale (List.nil : V1) b4=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b3 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e3695 e3696 (by rfl)
theorem e3698 : o2.add (List.nil : V2) b3847=b3847 := by rfl
theorem e3699 : o2.mul b3846 b4=b3847 := @mul_cons V1 _ o1 (List.nil : V1) b3848 b4 b3849 (List.nil : V2) b3847 b3847 e3694 e3697 (by rfl) e3698
theorem e3700 : o2.add (List.nil : V2) b3845=b3845 := by rfl
theorem e3701 : o2.mul b3844 b4=b3845 := @mul_cons V1 _ o1 (List.nil : V1) b3846 b4 b3847 (List.nil : V2) b3845 b3845 e3699 e3697 (by rfl) e3700
theorem e3702 : o2.add (List.nil : V2) b3843=b3843 := by rfl
theorem e3703 : o2.mul b3842 b4=b3843 := @mul_cons V1 _ o1 (List.nil : V1) b3844 b4 b3845 (List.nil : V2) b3843 b3843 e3701 e3697 (by rfl) e3702
theorem e3704 : o2.add (List.nil : V2) b3841=b3841 := by rfl
theorem e3705 : o2.mul b3840 b4=b3841 := @mul_cons V1 _ o1 (List.nil : V1) b3842 b4 b3843 (List.nil : V2) b3841 b3841 e3703 e3697 (by rfl) e3704
theorem e3706 : o2.add (List.nil : V2) b3839=b3839 := by rfl
theorem e3707 : o2.mul b3838 b4=b3839 := @mul_cons V1 _ o1 (List.nil : V1) b3840 b4 b3841 (List.nil : V2) b3839 b3839 e3705 e3697 (by rfl) e3706
theorem e3708 : o2.add (List.nil : V2) b3820=b3820 := by rfl
theorem e3709 : o2.mul b219 b4=b3820 := @mul_cons V1 _ o1 (List.nil : V1) b3838 b4 b3839 (List.nil : V2) b3820 b3820 e3707 e3697 (by rfl) e3708
theorem e3710 : o2.scale b219 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e3711 : o2.scale b219 b5=b3837 := @scale_cons V2 _ o2 b219 b4 b3820 (List.nil : V3) (List.nil : V3) b3837 e3709 e3710 (by rfl)
theorem e3712 : o3.add b3837 (List.nil : V3)=b3837 := by rfl
theorem e3713 : o3.mul b3836 b5=b3837 := @mul_cons V2 _ o2 b219 (List.nil : V3) b5 (List.nil : V3) b3837 (List.nil : V3) b3837 e3625 e3711 (by rfl) e3712
theorem e3714 : o1.mul b207 b3=b3808 := by decide
theorem e3715 : o1.scale b207 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3716 : o1.scale b207 b4=b3916 := @scale_cons V1 _ o1 b207 b3 b3808 (List.nil : V2) (List.nil : V2) b3916 e3714 e3715 (by rfl)
theorem e3717 : o2.add b3916 (List.nil : V2)=b3916 := by rfl
theorem e3718 : o2.mul b3915 b4=b3916 := @mul_cons V1 _ o1 b207 (List.nil : V2) b4 (List.nil : V2) b3916 (List.nil : V2) b3916 e3626 e3716 (by rfl) e3717
theorem e3719 : o1.mul b206 b3=b3807 := by decide
theorem e3720 : o1.scale b206 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3721 : o1.scale b206 b4=b3917 := @scale_cons V1 _ o1 b206 b3 b3807 (List.nil : V2) (List.nil : V2) b3917 e3719 e3720 (by rfl)
theorem e3722 : o1.add b3807 (List.nil : V1)=b3807 := by rfl
theorem e3723 : o2.add (List.nil : V2) b3916=b3916 := by rfl
theorem e3724 : o2.add b3917 b3918=b3914 := @add_cons V1 _ o1 b3807 (List.nil : V1) b3807 (List.nil : V2) b3916 b3916 b3914 e3722 e3723 (by rfl)
theorem e3725 : o2.mul b3913 b4=b3914 := @mul_cons V1 _ o1 b206 b3915 b4 b3916 b3917 b3918 b3914 e3718 e3721 (by rfl) e3724
theorem e3726 : o1.mul b205 b3=b3806 := by decide
theorem e3727 : o1.scale b205 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3728 : o1.scale b205 b4=b3919 := @scale_cons V1 _ o1 b205 b3 b3806 (List.nil : V2) (List.nil : V2) b3919 e3726 e3727 (by rfl)
theorem e3729 : o1.add b3806 (List.nil : V1)=b3806 := by rfl
theorem e3730 : o2.add (List.nil : V2) b3914=b3914 := by rfl
theorem e3731 : o2.add b3919 b3920=b3912 := @add_cons V1 _ o1 b3806 (List.nil : V1) b3806 (List.nil : V2) b3914 b3914 b3912 e3729 e3730 (by rfl)
theorem e3732 : o2.mul b3911 b4=b3912 := @mul_cons V1 _ o1 b205 b3913 b4 b3914 b3919 b3920 b3912 e3725 e3728 (by rfl) e3731
theorem e3733 : o1.mul b204 b3=b3805 := by decide
theorem e3734 : o1.scale b204 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3735 : o1.scale b204 b4=b3921 := @scale_cons V1 _ o1 b204 b3 b3805 (List.nil : V2) (List.nil : V2) b3921 e3733 e3734 (by rfl)
theorem e3736 : o1.add b3805 (List.nil : V1)=b3805 := by rfl
theorem e3737 : o2.add (List.nil : V2) b3912=b3912 := by rfl
theorem e3738 : o2.add b3921 b3922=b3910 := @add_cons V1 _ o1 b3805 (List.nil : V1) b3805 (List.nil : V2) b3912 b3912 b3910 e3736 e3737 (by rfl)
theorem e3739 : o2.mul b3909 b4=b3910 := @mul_cons V1 _ o1 b204 b3911 b4 b3912 b3921 b3922 b3910 e3732 e3735 (by rfl) e3738
theorem e3740 : o1.mul b203 b3=b3804 := by decide
theorem e3741 : o1.scale b203 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3742 : o1.scale b203 b4=b3923 := @scale_cons V1 _ o1 b203 b3 b3804 (List.nil : V2) (List.nil : V2) b3923 e3740 e3741 (by rfl)
theorem e3743 : o1.add b3804 (List.nil : V1)=b3804 := by rfl
theorem e3744 : o2.add (List.nil : V2) b3910=b3910 := by rfl
theorem e3745 : o2.add b3923 b3924=b3908 := @add_cons V1 _ o1 b3804 (List.nil : V1) b3804 (List.nil : V2) b3910 b3910 b3908 e3743 e3744 (by rfl)
theorem e3746 : o2.mul b3907 b4=b3908 := @mul_cons V1 _ o1 b203 b3909 b4 b3910 b3923 b3924 b3908 e3739 e3742 (by rfl) e3745
theorem e3747 : o1.mul b202 b3=b3803 := by decide
theorem e3748 : o1.scale b202 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3749 : o1.scale b202 b4=b3925 := @scale_cons V1 _ o1 b202 b3 b3803 (List.nil : V2) (List.nil : V2) b3925 e3747 e3748 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
