module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart025

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3750 : o1.add b3803 (List.nil : V1)=b3803 := by rfl
theorem e3751 : o2.add (List.nil : V2) b3908=b3908 := by rfl
theorem e3752 : o2.add b3925 b3926=b3906 := @add_cons V1 _ o1 b3803 (List.nil : V1) b3803 (List.nil : V2) b3908 b3908 b3906 e3750 e3751 (by rfl)
theorem e3753 : o2.mul b3905 b4=b3906 := @mul_cons V1 _ o1 b202 b3907 b4 b3908 b3925 b3926 b3906 e3746 e3749 (by rfl) e3752
theorem e3754 : o1.mul b201 b3=b3802 := by decide
theorem e3755 : o1.scale b201 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3756 : o1.scale b201 b4=b3927 := @scale_cons V1 _ o1 b201 b3 b3802 (List.nil : V2) (List.nil : V2) b3927 e3754 e3755 (by rfl)
theorem e3757 : o1.add b3802 (List.nil : V1)=b3802 := by rfl
theorem e3758 : o2.add (List.nil : V2) b3906=b3906 := by rfl
theorem e3759 : o2.add b3927 b3928=b3904 := @add_cons V1 _ o1 b3802 (List.nil : V1) b3802 (List.nil : V2) b3906 b3906 b3904 e3757 e3758 (by rfl)
theorem e3760 : o2.mul b3903 b4=b3904 := @mul_cons V1 _ o1 b201 b3905 b4 b3906 b3927 b3928 b3904 e3753 e3756 (by rfl) e3759
theorem e3761 : o1.mul b200 b3=b3801 := by decide
theorem e3762 : o1.scale b200 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3763 : o1.scale b200 b4=b3929 := @scale_cons V1 _ o1 b200 b3 b3801 (List.nil : V2) (List.nil : V2) b3929 e3761 e3762 (by rfl)
theorem e3764 : o1.add b3801 (List.nil : V1)=b3801 := by rfl
theorem e3765 : o2.add (List.nil : V2) b3904=b3904 := by rfl
theorem e3766 : o2.add b3929 b3930=b3902 := @add_cons V1 _ o1 b3801 (List.nil : V1) b3801 (List.nil : V2) b3904 b3904 b3902 e3764 e3765 (by rfl)
theorem e3767 : o2.mul b3901 b4=b3902 := @mul_cons V1 _ o1 b200 b3903 b4 b3904 b3929 b3930 b3902 e3760 e3763 (by rfl) e3766
theorem e3768 : o1.mul b199 b3=b3800 := by decide
theorem e3769 : o1.scale b199 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3770 : o1.scale b199 b4=b3931 := @scale_cons V1 _ o1 b199 b3 b3800 (List.nil : V2) (List.nil : V2) b3931 e3768 e3769 (by rfl)
theorem e3771 : o1.add b3800 (List.nil : V1)=b3800 := by rfl
theorem e3772 : o2.add (List.nil : V2) b3902=b3902 := by rfl
theorem e3773 : o2.add b3931 b3932=b3900 := @add_cons V1 _ o1 b3800 (List.nil : V1) b3800 (List.nil : V2) b3902 b3902 b3900 e3771 e3772 (by rfl)
theorem e3774 : o2.mul b3899 b4=b3900 := @mul_cons V1 _ o1 b199 b3901 b4 b3902 b3931 b3932 b3900 e3767 e3770 (by rfl) e3773
theorem e3775 : o1.mul b198 b3=b3799 := by decide
theorem e3776 : o1.scale b198 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3777 : o1.scale b198 b4=b3933 := @scale_cons V1 _ o1 b198 b3 b3799 (List.nil : V2) (List.nil : V2) b3933 e3775 e3776 (by rfl)
theorem e3778 : o1.add b3799 (List.nil : V1)=b3799 := by rfl
theorem e3779 : o2.add (List.nil : V2) b3900=b3900 := by rfl
theorem e3780 : o2.add b3933 b3934=b3898 := @add_cons V1 _ o1 b3799 (List.nil : V1) b3799 (List.nil : V2) b3900 b3900 b3898 e3778 e3779 (by rfl)
theorem e3781 : o2.mul b3897 b4=b3898 := @mul_cons V1 _ o1 b198 b3899 b4 b3900 b3933 b3934 b3898 e3774 e3777 (by rfl) e3780
theorem e3782 : o1.mul b197 b3=b3798 := by decide
theorem e3783 : o1.scale b197 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3784 : o1.scale b197 b4=b3935 := @scale_cons V1 _ o1 b197 b3 b3798 (List.nil : V2) (List.nil : V2) b3935 e3782 e3783 (by rfl)
theorem e3785 : o1.add b3798 (List.nil : V1)=b3798 := by rfl
theorem e3786 : o2.add (List.nil : V2) b3898=b3898 := by rfl
theorem e3787 : o2.add b3935 b3936=b3896 := @add_cons V1 _ o1 b3798 (List.nil : V1) b3798 (List.nil : V2) b3898 b3898 b3896 e3785 e3786 (by rfl)
theorem e3788 : o2.mul b3895 b4=b3896 := @mul_cons V1 _ o1 b197 b3897 b4 b3898 b3935 b3936 b3896 e3781 e3784 (by rfl) e3787
theorem e3789 : o2.add (List.nil : V2) b3894=b3894 := by rfl
theorem e3790 : o2.mul b3893 b4=b3894 := @mul_cons V1 _ o1 (List.nil : V1) b3895 b4 b3896 (List.nil : V2) b3894 b3894 e3788 e3697 (by rfl) e3789
theorem e3791 : o2.add (List.nil : V2) b3892=b3892 := by rfl
theorem e3792 : o2.mul b3891 b4=b3892 := @mul_cons V1 _ o1 (List.nil : V1) b3893 b4 b3894 (List.nil : V2) b3892 b3892 e3790 e3697 (by rfl) e3791
theorem e3793 : o2.add (List.nil : V2) b3890=b3890 := by rfl
theorem e3794 : o2.mul b3889 b4=b3890 := @mul_cons V1 _ o1 (List.nil : V1) b3891 b4 b3892 (List.nil : V2) b3890 b3890 e3792 e3697 (by rfl) e3793
theorem e3795 : o2.add (List.nil : V2) b3888=b3888 := by rfl
theorem e3796 : o2.mul b3887 b4=b3888 := @mul_cons V1 _ o1 (List.nil : V1) b3889 b4 b3890 (List.nil : V2) b3888 b3888 e3794 e3697 (by rfl) e3795
theorem e3797 : o2.add (List.nil : V2) b3809=b3809 := by rfl
theorem e3798 : o2.mul b208 b4=b3809 := @mul_cons V1 _ o1 (List.nil : V1) b3887 b4 b3888 (List.nil : V2) b3809 b3809 e3796 e3697 (by rfl) e3797
theorem e3799 : o2.scale b208 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e3800 : o2.scale b208 b5=b3886 := @scale_cons V2 _ o2 b208 b4 b3809 (List.nil : V3) (List.nil : V3) b3886 e3798 e3799 (by rfl)
theorem e3801 : o2.add b3809 (List.nil : V2)=b3809 := by rfl
theorem e3802 : o3.add (List.nil : V3) b3837=b3837 := by rfl
theorem e3803 : o3.add b3886 b3937=b3835 := @add_cons V2 _ o2 b3809 (List.nil : V2) b3809 (List.nil : V3) b3837 b3837 b3835 e3801 e3802 (by rfl)
theorem e3804 : o3.mul b3834 b5=b3835 := @mul_cons V2 _ o2 b208 b3836 b5 b3837 b3886 b3937 b3835 e3713 e3800 (by rfl) e3803
theorem e3805 : o1.mul b195 b3=b3796 := by decide
theorem e3806 : o1.scale b195 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3807 : o1.scale b195 b4=b3968 := @scale_cons V1 _ o1 b195 b3 b3796 (List.nil : V2) (List.nil : V2) b3968 e3805 e3806 (by rfl)
theorem e3808 : o2.add b3968 (List.nil : V2)=b3968 := by rfl
theorem e3809 : o2.mul b3967 b4=b3968 := @mul_cons V1 _ o1 b195 (List.nil : V2) b4 (List.nil : V2) b3968 (List.nil : V2) b3968 e3626 e3807 (by rfl) e3808
theorem e3810 : o1.mul b194 b3=b3795 := by decide
theorem e3811 : o1.scale b194 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3812 : o1.scale b194 b4=b3969 := @scale_cons V1 _ o1 b194 b3 b3795 (List.nil : V2) (List.nil : V2) b3969 e3810 e3811 (by rfl)
theorem e3813 : o1.add b3795 (List.nil : V1)=b3795 := by rfl
theorem e3814 : o2.add (List.nil : V2) b3968=b3968 := by rfl
theorem e3815 : o2.add b3969 b3970=b3966 := @add_cons V1 _ o1 b3795 (List.nil : V1) b3795 (List.nil : V2) b3968 b3968 b3966 e3813 e3814 (by rfl)
theorem e3816 : o2.mul b3965 b4=b3966 := @mul_cons V1 _ o1 b194 b3967 b4 b3968 b3969 b3970 b3966 e3809 e3812 (by rfl) e3815
theorem e3817 : o1.mul b193 b3=b3794 := by decide
theorem e3818 : o1.scale b193 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3819 : o1.scale b193 b4=b3971 := @scale_cons V1 _ o1 b193 b3 b3794 (List.nil : V2) (List.nil : V2) b3971 e3817 e3818 (by rfl)
theorem e3820 : o1.add b3794 (List.nil : V1)=b3794 := by rfl
theorem e3821 : o2.add (List.nil : V2) b3966=b3966 := by rfl
theorem e3822 : o2.add b3971 b3972=b3964 := @add_cons V1 _ o1 b3794 (List.nil : V1) b3794 (List.nil : V2) b3966 b3966 b3964 e3820 e3821 (by rfl)
theorem e3823 : o2.mul b3963 b4=b3964 := @mul_cons V1 _ o1 b193 b3965 b4 b3966 b3971 b3972 b3964 e3816 e3819 (by rfl) e3822
theorem e3824 : o1.mul b192 b3=b3793 := by decide
theorem e3825 : o1.scale b192 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3826 : o1.scale b192 b4=b3973 := @scale_cons V1 _ o1 b192 b3 b3793 (List.nil : V2) (List.nil : V2) b3973 e3824 e3825 (by rfl)
theorem e3827 : o1.add b3793 (List.nil : V1)=b3793 := by rfl
theorem e3828 : o2.add (List.nil : V2) b3964=b3964 := by rfl
theorem e3829 : o2.add b3973 b3974=b3962 := @add_cons V1 _ o1 b3793 (List.nil : V1) b3793 (List.nil : V2) b3964 b3964 b3962 e3827 e3828 (by rfl)
theorem e3830 : o2.mul b3961 b4=b3962 := @mul_cons V1 _ o1 b192 b3963 b4 b3964 b3973 b3974 b3962 e3823 e3826 (by rfl) e3829
theorem e3831 : o1.mul b191 b3=b3792 := by decide
theorem e3832 : o1.scale b191 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3833 : o1.scale b191 b4=b3975 := @scale_cons V1 _ o1 b191 b3 b3792 (List.nil : V2) (List.nil : V2) b3975 e3831 e3832 (by rfl)
theorem e3834 : o1.add b3792 (List.nil : V1)=b3792 := by rfl
theorem e3835 : o2.add (List.nil : V2) b3962=b3962 := by rfl
theorem e3836 : o2.add b3975 b3976=b3960 := @add_cons V1 _ o1 b3792 (List.nil : V1) b3792 (List.nil : V2) b3962 b3962 b3960 e3834 e3835 (by rfl)
theorem e3837 : o2.mul b3959 b4=b3960 := @mul_cons V1 _ o1 b191 b3961 b4 b3962 b3975 b3976 b3960 e3830 e3833 (by rfl) e3836
theorem e3838 : o1.mul b190 b3=b3791 := by decide
theorem e3839 : o1.scale b190 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3840 : o1.scale b190 b4=b3977 := @scale_cons V1 _ o1 b190 b3 b3791 (List.nil : V2) (List.nil : V2) b3977 e3838 e3839 (by rfl)
theorem e3841 : o1.add b3791 (List.nil : V1)=b3791 := by rfl
theorem e3842 : o2.add (List.nil : V2) b3960=b3960 := by rfl
theorem e3843 : o2.add b3977 b3978=b3958 := @add_cons V1 _ o1 b3791 (List.nil : V1) b3791 (List.nil : V2) b3960 b3960 b3958 e3841 e3842 (by rfl)
theorem e3844 : o2.mul b3957 b4=b3958 := @mul_cons V1 _ o1 b190 b3959 b4 b3960 b3977 b3978 b3958 e3837 e3840 (by rfl) e3843
theorem e3845 : o1.mul b189 b3=b3790 := by decide
theorem e3846 : o1.scale b189 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3847 : o1.scale b189 b4=b3979 := @scale_cons V1 _ o1 b189 b3 b3790 (List.nil : V2) (List.nil : V2) b3979 e3845 e3846 (by rfl)
theorem e3848 : o1.add b3790 (List.nil : V1)=b3790 := by rfl
theorem e3849 : o2.add (List.nil : V2) b3958=b3958 := by rfl
theorem e3850 : o2.add b3979 b3980=b3956 := @add_cons V1 _ o1 b3790 (List.nil : V1) b3790 (List.nil : V2) b3958 b3958 b3956 e3848 e3849 (by rfl)
theorem e3851 : o2.mul b3955 b4=b3956 := @mul_cons V1 _ o1 b189 b3957 b4 b3958 b3979 b3980 b3956 e3844 e3847 (by rfl) e3850
theorem e3852 : o1.mul b188 b3=b3789 := by decide
theorem e3853 : o1.scale b188 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3854 : o1.scale b188 b4=b3981 := @scale_cons V1 _ o1 b188 b3 b3789 (List.nil : V2) (List.nil : V2) b3981 e3852 e3853 (by rfl)
theorem e3855 : o1.add b3789 (List.nil : V1)=b3789 := by rfl
theorem e3856 : o2.add (List.nil : V2) b3956=b3956 := by rfl
theorem e3857 : o2.add b3981 b3982=b3954 := @add_cons V1 _ o1 b3789 (List.nil : V1) b3789 (List.nil : V2) b3956 b3956 b3954 e3855 e3856 (by rfl)
theorem e3858 : o2.mul b3953 b4=b3954 := @mul_cons V1 _ o1 b188 b3955 b4 b3956 b3981 b3982 b3954 e3851 e3854 (by rfl) e3857
theorem e3859 : o1.mul b187 b3=b3788 := by decide
theorem e3860 : o1.scale b187 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3861 : o1.scale b187 b4=b3983 := @scale_cons V1 _ o1 b187 b3 b3788 (List.nil : V2) (List.nil : V2) b3983 e3859 e3860 (by rfl)
theorem e3862 : o1.add b3788 (List.nil : V1)=b3788 := by rfl
theorem e3863 : o2.add (List.nil : V2) b3954=b3954 := by rfl
theorem e3864 : o2.add b3983 b3984=b3952 := @add_cons V1 _ o1 b3788 (List.nil : V1) b3788 (List.nil : V2) b3954 b3954 b3952 e3862 e3863 (by rfl)
theorem e3865 : o2.mul b3951 b4=b3952 := @mul_cons V1 _ o1 b187 b3953 b4 b3954 b3983 b3984 b3952 e3858 e3861 (by rfl) e3864
theorem e3866 : o1.mul b186 b3=b3787 := by decide
theorem e3867 : o1.scale b186 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3868 : o1.scale b186 b4=b3985 := @scale_cons V1 _ o1 b186 b3 b3787 (List.nil : V2) (List.nil : V2) b3985 e3866 e3867 (by rfl)
theorem e3869 : o1.add b3787 (List.nil : V1)=b3787 := by rfl
theorem e3870 : o2.add (List.nil : V2) b3952=b3952 := by rfl
theorem e3871 : o2.add b3985 b3986=b3950 := @add_cons V1 _ o1 b3787 (List.nil : V1) b3787 (List.nil : V2) b3952 b3952 b3950 e3869 e3870 (by rfl)
theorem e3872 : o2.mul b3949 b4=b3950 := @mul_cons V1 _ o1 b186 b3951 b4 b3952 b3985 b3986 b3950 e3865 e3868 (by rfl) e3871
theorem e3873 : o1.mul b185 b3=b3786 := by decide
theorem e3874 : o1.scale b185 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3875 : o1.scale b185 b4=b3987 := @scale_cons V1 _ o1 b185 b3 b3786 (List.nil : V2) (List.nil : V2) b3987 e3873 e3874 (by rfl)
theorem e3876 : o1.add b3786 (List.nil : V1)=b3786 := by rfl
theorem e3877 : o2.add (List.nil : V2) b3950=b3950 := by rfl
theorem e3878 : o2.add b3987 b3988=b3948 := @add_cons V1 _ o1 b3786 (List.nil : V1) b3786 (List.nil : V2) b3950 b3950 b3948 e3876 e3877 (by rfl)
theorem e3879 : o2.mul b3947 b4=b3948 := @mul_cons V1 _ o1 b185 b3949 b4 b3950 b3987 b3988 b3948 e3872 e3875 (by rfl) e3878
theorem e3880 : o1.mul b184 b3=b3785 := by decide
theorem e3881 : o1.scale b184 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3882 : o1.scale b184 b4=b3989 := @scale_cons V1 _ o1 b184 b3 b3785 (List.nil : V2) (List.nil : V2) b3989 e3880 e3881 (by rfl)
theorem e3883 : o1.add b3785 (List.nil : V1)=b3785 := by rfl
theorem e3884 : o2.add (List.nil : V2) b3948=b3948 := by rfl
theorem e3885 : o2.add b3989 b3990=b3946 := @add_cons V1 _ o1 b3785 (List.nil : V1) b3785 (List.nil : V2) b3948 b3948 b3946 e3883 e3884 (by rfl)
theorem e3886 : o2.mul b3945 b4=b3946 := @mul_cons V1 _ o1 b184 b3947 b4 b3948 b3989 b3990 b3946 e3879 e3882 (by rfl) e3885
theorem e3887 : o2.add (List.nil : V2) b3944=b3944 := by rfl
theorem e3888 : o2.mul b3943 b4=b3944 := @mul_cons V1 _ o1 (List.nil : V1) b3945 b4 b3946 (List.nil : V2) b3944 b3944 e3886 e3697 (by rfl) e3887
theorem e3889 : o2.add (List.nil : V2) b3942=b3942 := by rfl
theorem e3890 : o2.mul b3941 b4=b3942 := @mul_cons V1 _ o1 (List.nil : V1) b3943 b4 b3944 (List.nil : V2) b3942 b3942 e3888 e3697 (by rfl) e3889
theorem e3891 : o2.add (List.nil : V2) b3940=b3940 := by rfl
theorem e3892 : o2.mul b3939 b4=b3940 := @mul_cons V1 _ o1 (List.nil : V1) b3941 b4 b3942 (List.nil : V2) b3940 b3940 e3890 e3697 (by rfl) e3891
theorem e3893 : o2.add (List.nil : V2) b3797=b3797 := by rfl
theorem e3894 : o2.mul b196 b4=b3797 := @mul_cons V1 _ o1 (List.nil : V1) b3939 b4 b3940 (List.nil : V2) b3797 b3797 e3892 e3697 (by rfl) e3893
theorem e3895 : o2.scale b196 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e3896 : o2.scale b196 b5=b3938 := @scale_cons V2 _ o2 b196 b4 b3797 (List.nil : V3) (List.nil : V3) b3938 e3894 e3895 (by rfl)
theorem e3897 : o2.add b3797 (List.nil : V2)=b3797 := by rfl
theorem e3898 : o3.add (List.nil : V3) b3835=b3835 := by rfl
theorem e3899 : o3.add b3938 b3991=b3833 := @add_cons V2 _ o2 b3797 (List.nil : V2) b3797 (List.nil : V3) b3835 b3835 b3833 e3897 e3898 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
