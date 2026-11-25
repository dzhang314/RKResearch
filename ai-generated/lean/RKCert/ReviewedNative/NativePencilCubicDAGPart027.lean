module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart026

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e3900 : o3.mul b3832 b5=b3833 := @mul_cons V2 _ o2 b196 b3834 b5 b3835 b3938 b3991 b3833 e3804 e3896 (by rfl) e3899
theorem e3901 : o1.mul b182 b3=b3783 := by decide
theorem e3902 : o1.scale b182 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3903 : o1.scale b182 b4=b4022 := @scale_cons V1 _ o1 b182 b3 b3783 (List.nil : V2) (List.nil : V2) b4022 e3901 e3902 (by rfl)
theorem e3904 : o2.add b4022 (List.nil : V2)=b4022 := by rfl
theorem e3905 : o2.mul b4021 b4=b4022 := @mul_cons V1 _ o1 b182 (List.nil : V2) b4 (List.nil : V2) b4022 (List.nil : V2) b4022 e3626 e3903 (by rfl) e3904
theorem e3906 : o1.mul b181 b3=b3782 := by decide
theorem e3907 : o1.scale b181 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3908 : o1.scale b181 b4=b4023 := @scale_cons V1 _ o1 b181 b3 b3782 (List.nil : V2) (List.nil : V2) b4023 e3906 e3907 (by rfl)
theorem e3909 : o1.add b3782 (List.nil : V1)=b3782 := by rfl
theorem e3910 : o2.add (List.nil : V2) b4022=b4022 := by rfl
theorem e3911 : o2.add b4023 b4024=b4020 := @add_cons V1 _ o1 b3782 (List.nil : V1) b3782 (List.nil : V2) b4022 b4022 b4020 e3909 e3910 (by rfl)
theorem e3912 : o2.mul b4019 b4=b4020 := @mul_cons V1 _ o1 b181 b4021 b4 b4022 b4023 b4024 b4020 e3905 e3908 (by rfl) e3911
theorem e3913 : o1.mul b180 b3=b3781 := by decide
theorem e3914 : o1.scale b180 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3915 : o1.scale b180 b4=b4025 := @scale_cons V1 _ o1 b180 b3 b3781 (List.nil : V2) (List.nil : V2) b4025 e3913 e3914 (by rfl)
theorem e3916 : o1.add b3781 (List.nil : V1)=b3781 := by rfl
theorem e3917 : o2.add (List.nil : V2) b4020=b4020 := by rfl
theorem e3918 : o2.add b4025 b4026=b4018 := @add_cons V1 _ o1 b3781 (List.nil : V1) b3781 (List.nil : V2) b4020 b4020 b4018 e3916 e3917 (by rfl)
theorem e3919 : o2.mul b4017 b4=b4018 := @mul_cons V1 _ o1 b180 b4019 b4 b4020 b4025 b4026 b4018 e3912 e3915 (by rfl) e3918
theorem e3920 : o1.mul b179 b3=b3780 := by decide
theorem e3921 : o1.scale b179 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3922 : o1.scale b179 b4=b4027 := @scale_cons V1 _ o1 b179 b3 b3780 (List.nil : V2) (List.nil : V2) b4027 e3920 e3921 (by rfl)
theorem e3923 : o1.add b3780 (List.nil : V1)=b3780 := by rfl
theorem e3924 : o2.add (List.nil : V2) b4018=b4018 := by rfl
theorem e3925 : o2.add b4027 b4028=b4016 := @add_cons V1 _ o1 b3780 (List.nil : V1) b3780 (List.nil : V2) b4018 b4018 b4016 e3923 e3924 (by rfl)
theorem e3926 : o2.mul b4015 b4=b4016 := @mul_cons V1 _ o1 b179 b4017 b4 b4018 b4027 b4028 b4016 e3919 e3922 (by rfl) e3925
theorem e3927 : o1.mul b178 b3=b3779 := by decide
theorem e3928 : o1.scale b178 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3929 : o1.scale b178 b4=b4029 := @scale_cons V1 _ o1 b178 b3 b3779 (List.nil : V2) (List.nil : V2) b4029 e3927 e3928 (by rfl)
theorem e3930 : o1.add b3779 (List.nil : V1)=b3779 := by rfl
theorem e3931 : o2.add (List.nil : V2) b4016=b4016 := by rfl
theorem e3932 : o2.add b4029 b4030=b4014 := @add_cons V1 _ o1 b3779 (List.nil : V1) b3779 (List.nil : V2) b4016 b4016 b4014 e3930 e3931 (by rfl)
theorem e3933 : o2.mul b4013 b4=b4014 := @mul_cons V1 _ o1 b178 b4015 b4 b4016 b4029 b4030 b4014 e3926 e3929 (by rfl) e3932
theorem e3934 : o1.mul b177 b3=b3778 := by decide
theorem e3935 : o1.scale b177 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3936 : o1.scale b177 b4=b4031 := @scale_cons V1 _ o1 b177 b3 b3778 (List.nil : V2) (List.nil : V2) b4031 e3934 e3935 (by rfl)
theorem e3937 : o1.add b3778 (List.nil : V1)=b3778 := by rfl
theorem e3938 : o2.add (List.nil : V2) b4014=b4014 := by rfl
theorem e3939 : o2.add b4031 b4032=b4012 := @add_cons V1 _ o1 b3778 (List.nil : V1) b3778 (List.nil : V2) b4014 b4014 b4012 e3937 e3938 (by rfl)
theorem e3940 : o2.mul b4011 b4=b4012 := @mul_cons V1 _ o1 b177 b4013 b4 b4014 b4031 b4032 b4012 e3933 e3936 (by rfl) e3939
theorem e3941 : o1.mul b176 b3=b3777 := by decide
theorem e3942 : o1.scale b176 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3943 : o1.scale b176 b4=b4033 := @scale_cons V1 _ o1 b176 b3 b3777 (List.nil : V2) (List.nil : V2) b4033 e3941 e3942 (by rfl)
theorem e3944 : o1.add b3777 (List.nil : V1)=b3777 := by rfl
theorem e3945 : o2.add (List.nil : V2) b4012=b4012 := by rfl
theorem e3946 : o2.add b4033 b4034=b4010 := @add_cons V1 _ o1 b3777 (List.nil : V1) b3777 (List.nil : V2) b4012 b4012 b4010 e3944 e3945 (by rfl)
theorem e3947 : o2.mul b4009 b4=b4010 := @mul_cons V1 _ o1 b176 b4011 b4 b4012 b4033 b4034 b4010 e3940 e3943 (by rfl) e3946
theorem e3948 : o1.mul b175 b3=b3776 := by decide
theorem e3949 : o1.scale b175 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3950 : o1.scale b175 b4=b4035 := @scale_cons V1 _ o1 b175 b3 b3776 (List.nil : V2) (List.nil : V2) b4035 e3948 e3949 (by rfl)
theorem e3951 : o1.add b3776 (List.nil : V1)=b3776 := by rfl
theorem e3952 : o2.add (List.nil : V2) b4010=b4010 := by rfl
theorem e3953 : o2.add b4035 b4036=b4008 := @add_cons V1 _ o1 b3776 (List.nil : V1) b3776 (List.nil : V2) b4010 b4010 b4008 e3951 e3952 (by rfl)
theorem e3954 : o2.mul b4007 b4=b4008 := @mul_cons V1 _ o1 b175 b4009 b4 b4010 b4035 b4036 b4008 e3947 e3950 (by rfl) e3953
theorem e3955 : o1.mul b174 b3=b3775 := by decide
theorem e3956 : o1.scale b174 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3957 : o1.scale b174 b4=b4037 := @scale_cons V1 _ o1 b174 b3 b3775 (List.nil : V2) (List.nil : V2) b4037 e3955 e3956 (by rfl)
theorem e3958 : o1.add b3775 (List.nil : V1)=b3775 := by rfl
theorem e3959 : o2.add (List.nil : V2) b4008=b4008 := by rfl
theorem e3960 : o2.add b4037 b4038=b4006 := @add_cons V1 _ o1 b3775 (List.nil : V1) b3775 (List.nil : V2) b4008 b4008 b4006 e3958 e3959 (by rfl)
theorem e3961 : o2.mul b4005 b4=b4006 := @mul_cons V1 _ o1 b174 b4007 b4 b4008 b4037 b4038 b4006 e3954 e3957 (by rfl) e3960
theorem e3962 : o1.mul b173 b3=b3774 := by decide
theorem e3963 : o1.scale b173 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3964 : o1.scale b173 b4=b4039 := @scale_cons V1 _ o1 b173 b3 b3774 (List.nil : V2) (List.nil : V2) b4039 e3962 e3963 (by rfl)
theorem e3965 : o1.add b3774 (List.nil : V1)=b3774 := by rfl
theorem e3966 : o2.add (List.nil : V2) b4006=b4006 := by rfl
theorem e3967 : o2.add b4039 b4040=b4004 := @add_cons V1 _ o1 b3774 (List.nil : V1) b3774 (List.nil : V2) b4006 b4006 b4004 e3965 e3966 (by rfl)
theorem e3968 : o2.mul b4003 b4=b4004 := @mul_cons V1 _ o1 b173 b4005 b4 b4006 b4039 b4040 b4004 e3961 e3964 (by rfl) e3967
theorem e3969 : o1.mul b172 b3=b3773 := by decide
theorem e3970 : o1.scale b172 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3971 : o1.scale b172 b4=b4041 := @scale_cons V1 _ o1 b172 b3 b3773 (List.nil : V2) (List.nil : V2) b4041 e3969 e3970 (by rfl)
theorem e3972 : o1.add b3773 (List.nil : V1)=b3773 := by rfl
theorem e3973 : o2.add (List.nil : V2) b4004=b4004 := by rfl
theorem e3974 : o2.add b4041 b4042=b4002 := @add_cons V1 _ o1 b3773 (List.nil : V1) b3773 (List.nil : V2) b4004 b4004 b4002 e3972 e3973 (by rfl)
theorem e3975 : o2.mul b4001 b4=b4002 := @mul_cons V1 _ o1 b172 b4003 b4 b4004 b4041 b4042 b4002 e3968 e3971 (by rfl) e3974
theorem e3976 : o1.mul b171 b3=b3772 := by decide
theorem e3977 : o1.scale b171 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3978 : o1.scale b171 b4=b4043 := @scale_cons V1 _ o1 b171 b3 b3772 (List.nil : V2) (List.nil : V2) b4043 e3976 e3977 (by rfl)
theorem e3979 : o1.add b3772 (List.nil : V1)=b3772 := by rfl
theorem e3980 : o2.add (List.nil : V2) b4002=b4002 := by rfl
theorem e3981 : o2.add b4043 b4044=b4000 := @add_cons V1 _ o1 b3772 (List.nil : V1) b3772 (List.nil : V2) b4002 b4002 b4000 e3979 e3980 (by rfl)
theorem e3982 : o2.mul b3999 b4=b4000 := @mul_cons V1 _ o1 b171 b4001 b4 b4002 b4043 b4044 b4000 e3975 e3978 (by rfl) e3981
theorem e3983 : o1.mul b170 b3=b3771 := by decide
theorem e3984 : o1.scale b170 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e3985 : o1.scale b170 b4=b4045 := @scale_cons V1 _ o1 b170 b3 b3771 (List.nil : V2) (List.nil : V2) b4045 e3983 e3984 (by rfl)
theorem e3986 : o1.add b3771 (List.nil : V1)=b3771 := by rfl
theorem e3987 : o2.add (List.nil : V2) b4000=b4000 := by rfl
theorem e3988 : o2.add b4045 b4046=b3998 := @add_cons V1 _ o1 b3771 (List.nil : V1) b3771 (List.nil : V2) b4000 b4000 b3998 e3986 e3987 (by rfl)
theorem e3989 : o2.mul b3997 b4=b3998 := @mul_cons V1 _ o1 b170 b3999 b4 b4000 b4045 b4046 b3998 e3982 e3985 (by rfl) e3988
theorem e3990 : o2.add (List.nil : V2) b3996=b3996 := by rfl
theorem e3991 : o2.mul b3995 b4=b3996 := @mul_cons V1 _ o1 (List.nil : V1) b3997 b4 b3998 (List.nil : V2) b3996 b3996 e3989 e3697 (by rfl) e3990
theorem e3992 : o2.add (List.nil : V2) b3994=b3994 := by rfl
theorem e3993 : o2.mul b3993 b4=b3994 := @mul_cons V1 _ o1 (List.nil : V1) b3995 b4 b3996 (List.nil : V2) b3994 b3994 e3991 e3697 (by rfl) e3992
theorem e3994 : o2.add (List.nil : V2) b3784=b3784 := by rfl
theorem e3995 : o2.mul b183 b4=b3784 := @mul_cons V1 _ o1 (List.nil : V1) b3993 b4 b3994 (List.nil : V2) b3784 b3784 e3993 e3697 (by rfl) e3994
theorem e3996 : o2.scale b183 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e3997 : o2.scale b183 b5=b3992 := @scale_cons V2 _ o2 b183 b4 b3784 (List.nil : V3) (List.nil : V3) b3992 e3995 e3996 (by rfl)
theorem e3998 : o2.add b3784 (List.nil : V2)=b3784 := by rfl
theorem e3999 : o3.add (List.nil : V3) b3833=b3833 := by rfl
theorem e4000 : o3.add b3992 b4047=b3831 := @add_cons V2 _ o2 b3784 (List.nil : V2) b3784 (List.nil : V3) b3833 b3833 b3831 e3998 e3999 (by rfl)
theorem e4001 : o3.mul b3830 b5=b3831 := @mul_cons V2 _ o2 b183 b3832 b5 b3833 b3992 b4047 b3831 e3900 e3997 (by rfl) e4000
theorem e4002 : o1.mul b168 b3=b3769 := by decide
theorem e4003 : o1.scale b168 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4004 : o1.scale b168 b4=b4078 := @scale_cons V1 _ o1 b168 b3 b3769 (List.nil : V2) (List.nil : V2) b4078 e4002 e4003 (by rfl)
theorem e4005 : o2.add b4078 (List.nil : V2)=b4078 := by rfl
theorem e4006 : o2.mul b4077 b4=b4078 := @mul_cons V1 _ o1 b168 (List.nil : V2) b4 (List.nil : V2) b4078 (List.nil : V2) b4078 e3626 e4004 (by rfl) e4005
theorem e4007 : o1.mul b167 b3=b3768 := by decide
theorem e4008 : o1.scale b167 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4009 : o1.scale b167 b4=b4079 := @scale_cons V1 _ o1 b167 b3 b3768 (List.nil : V2) (List.nil : V2) b4079 e4007 e4008 (by rfl)
theorem e4010 : o1.add b3768 (List.nil : V1)=b3768 := by rfl
theorem e4011 : o2.add (List.nil : V2) b4078=b4078 := by rfl
theorem e4012 : o2.add b4079 b4080=b4076 := @add_cons V1 _ o1 b3768 (List.nil : V1) b3768 (List.nil : V2) b4078 b4078 b4076 e4010 e4011 (by rfl)
theorem e4013 : o2.mul b4075 b4=b4076 := @mul_cons V1 _ o1 b167 b4077 b4 b4078 b4079 b4080 b4076 e4006 e4009 (by rfl) e4012
theorem e4014 : o1.mul b166 b3=b3767 := by decide
theorem e4015 : o1.scale b166 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4016 : o1.scale b166 b4=b4081 := @scale_cons V1 _ o1 b166 b3 b3767 (List.nil : V2) (List.nil : V2) b4081 e4014 e4015 (by rfl)
theorem e4017 : o1.add b3767 (List.nil : V1)=b3767 := by rfl
theorem e4018 : o2.add (List.nil : V2) b4076=b4076 := by rfl
theorem e4019 : o2.add b4081 b4082=b4074 := @add_cons V1 _ o1 b3767 (List.nil : V1) b3767 (List.nil : V2) b4076 b4076 b4074 e4017 e4018 (by rfl)
theorem e4020 : o2.mul b4073 b4=b4074 := @mul_cons V1 _ o1 b166 b4075 b4 b4076 b4081 b4082 b4074 e4013 e4016 (by rfl) e4019
theorem e4021 : o1.mul b165 b3=b3766 := by decide
theorem e4022 : o1.scale b165 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4023 : o1.scale b165 b4=b4083 := @scale_cons V1 _ o1 b165 b3 b3766 (List.nil : V2) (List.nil : V2) b4083 e4021 e4022 (by rfl)
theorem e4024 : o1.add b3766 (List.nil : V1)=b3766 := by rfl
theorem e4025 : o2.add (List.nil : V2) b4074=b4074 := by rfl
theorem e4026 : o2.add b4083 b4084=b4072 := @add_cons V1 _ o1 b3766 (List.nil : V1) b3766 (List.nil : V2) b4074 b4074 b4072 e4024 e4025 (by rfl)
theorem e4027 : o2.mul b4071 b4=b4072 := @mul_cons V1 _ o1 b165 b4073 b4 b4074 b4083 b4084 b4072 e4020 e4023 (by rfl) e4026
theorem e4028 : o1.mul b164 b3=b3765 := by decide
theorem e4029 : o1.scale b164 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4030 : o1.scale b164 b4=b4085 := @scale_cons V1 _ o1 b164 b3 b3765 (List.nil : V2) (List.nil : V2) b4085 e4028 e4029 (by rfl)
theorem e4031 : o1.add b3765 (List.nil : V1)=b3765 := by rfl
theorem e4032 : o2.add (List.nil : V2) b4072=b4072 := by rfl
theorem e4033 : o2.add b4085 b4086=b4070 := @add_cons V1 _ o1 b3765 (List.nil : V1) b3765 (List.nil : V2) b4072 b4072 b4070 e4031 e4032 (by rfl)
theorem e4034 : o2.mul b4069 b4=b4070 := @mul_cons V1 _ o1 b164 b4071 b4 b4072 b4085 b4086 b4070 e4027 e4030 (by rfl) e4033
theorem e4035 : o1.mul b163 b3=b3764 := by decide
theorem e4036 : o1.scale b163 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4037 : o1.scale b163 b4=b4087 := @scale_cons V1 _ o1 b163 b3 b3764 (List.nil : V2) (List.nil : V2) b4087 e4035 e4036 (by rfl)
theorem e4038 : o1.add b3764 (List.nil : V1)=b3764 := by rfl
theorem e4039 : o2.add (List.nil : V2) b4070=b4070 := by rfl
theorem e4040 : o2.add b4087 b4088=b4068 := @add_cons V1 _ o1 b3764 (List.nil : V1) b3764 (List.nil : V2) b4070 b4070 b4068 e4038 e4039 (by rfl)
theorem e4041 : o2.mul b4067 b4=b4068 := @mul_cons V1 _ o1 b163 b4069 b4 b4070 b4087 b4088 b4068 e4034 e4037 (by rfl) e4040
theorem e4042 : o1.mul b162 b3=b3763 := by decide
theorem e4043 : o1.scale b162 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4044 : o1.scale b162 b4=b4089 := @scale_cons V1 _ o1 b162 b3 b3763 (List.nil : V2) (List.nil : V2) b4089 e4042 e4043 (by rfl)
theorem e4045 : o1.add b3763 (List.nil : V1)=b3763 := by rfl
theorem e4046 : o2.add (List.nil : V2) b4068=b4068 := by rfl
theorem e4047 : o2.add b4089 b4090=b4066 := @add_cons V1 _ o1 b3763 (List.nil : V1) b3763 (List.nil : V2) b4068 b4068 b4066 e4045 e4046 (by rfl)
theorem e4048 : o2.mul b4065 b4=b4066 := @mul_cons V1 _ o1 b162 b4067 b4 b4068 b4089 b4090 b4066 e4041 e4044 (by rfl) e4047
theorem e4049 : o1.mul b161 b3=b3762 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
