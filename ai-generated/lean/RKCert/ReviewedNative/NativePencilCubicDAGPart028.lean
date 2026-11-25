module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart027

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4050 : o1.scale b161 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4051 : o1.scale b161 b4=b4091 := @scale_cons V1 _ o1 b161 b3 b3762 (List.nil : V2) (List.nil : V2) b4091 e4049 e4050 (by rfl)
theorem e4052 : o1.add b3762 (List.nil : V1)=b3762 := by rfl
theorem e4053 : o2.add (List.nil : V2) b4066=b4066 := by rfl
theorem e4054 : o2.add b4091 b4092=b4064 := @add_cons V1 _ o1 b3762 (List.nil : V1) b3762 (List.nil : V2) b4066 b4066 b4064 e4052 e4053 (by rfl)
theorem e4055 : o2.mul b4063 b4=b4064 := @mul_cons V1 _ o1 b161 b4065 b4 b4066 b4091 b4092 b4064 e4048 e4051 (by rfl) e4054
theorem e4056 : o1.mul b160 b3=b3761 := by decide
theorem e4057 : o1.scale b160 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4058 : o1.scale b160 b4=b4093 := @scale_cons V1 _ o1 b160 b3 b3761 (List.nil : V2) (List.nil : V2) b4093 e4056 e4057 (by rfl)
theorem e4059 : o1.add b3761 (List.nil : V1)=b3761 := by rfl
theorem e4060 : o2.add (List.nil : V2) b4064=b4064 := by rfl
theorem e4061 : o2.add b4093 b4094=b4062 := @add_cons V1 _ o1 b3761 (List.nil : V1) b3761 (List.nil : V2) b4064 b4064 b4062 e4059 e4060 (by rfl)
theorem e4062 : o2.mul b4061 b4=b4062 := @mul_cons V1 _ o1 b160 b4063 b4 b4064 b4093 b4094 b4062 e4055 e4058 (by rfl) e4061
theorem e4063 : o1.mul b159 b3=b3760 := by decide
theorem e4064 : o1.scale b159 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4065 : o1.scale b159 b4=b4095 := @scale_cons V1 _ o1 b159 b3 b3760 (List.nil : V2) (List.nil : V2) b4095 e4063 e4064 (by rfl)
theorem e4066 : o1.add b3760 (List.nil : V1)=b3760 := by rfl
theorem e4067 : o2.add (List.nil : V2) b4062=b4062 := by rfl
theorem e4068 : o2.add b4095 b4096=b4060 := @add_cons V1 _ o1 b3760 (List.nil : V1) b3760 (List.nil : V2) b4062 b4062 b4060 e4066 e4067 (by rfl)
theorem e4069 : o2.mul b4059 b4=b4060 := @mul_cons V1 _ o1 b159 b4061 b4 b4062 b4095 b4096 b4060 e4062 e4065 (by rfl) e4068
theorem e4070 : o1.mul b158 b3=b3759 := by decide
theorem e4071 : o1.scale b158 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4072 : o1.scale b158 b4=b4097 := @scale_cons V1 _ o1 b158 b3 b3759 (List.nil : V2) (List.nil : V2) b4097 e4070 e4071 (by rfl)
theorem e4073 : o1.add b3759 (List.nil : V1)=b3759 := by rfl
theorem e4074 : o2.add (List.nil : V2) b4060=b4060 := by rfl
theorem e4075 : o2.add b4097 b4098=b4058 := @add_cons V1 _ o1 b3759 (List.nil : V1) b3759 (List.nil : V2) b4060 b4060 b4058 e4073 e4074 (by rfl)
theorem e4076 : o2.mul b4057 b4=b4058 := @mul_cons V1 _ o1 b158 b4059 b4 b4060 b4097 b4098 b4058 e4069 e4072 (by rfl) e4075
theorem e4077 : o1.mul b157 b3=b3758 := by decide
theorem e4078 : o1.scale b157 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4079 : o1.scale b157 b4=b4099 := @scale_cons V1 _ o1 b157 b3 b3758 (List.nil : V2) (List.nil : V2) b4099 e4077 e4078 (by rfl)
theorem e4080 : o1.add b3758 (List.nil : V1)=b3758 := by rfl
theorem e4081 : o2.add (List.nil : V2) b4058=b4058 := by rfl
theorem e4082 : o2.add b4099 b4100=b4056 := @add_cons V1 _ o1 b3758 (List.nil : V1) b3758 (List.nil : V2) b4058 b4058 b4056 e4080 e4081 (by rfl)
theorem e4083 : o2.mul b4055 b4=b4056 := @mul_cons V1 _ o1 b157 b4057 b4 b4058 b4099 b4100 b4056 e4076 e4079 (by rfl) e4082
theorem e4084 : o1.mul b156 b3=b3757 := by decide
theorem e4085 : o1.scale b156 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4086 : o1.scale b156 b4=b4101 := @scale_cons V1 _ o1 b156 b3 b3757 (List.nil : V2) (List.nil : V2) b4101 e4084 e4085 (by rfl)
theorem e4087 : o1.add b3757 (List.nil : V1)=b3757 := by rfl
theorem e4088 : o2.add (List.nil : V2) b4056=b4056 := by rfl
theorem e4089 : o2.add b4101 b4102=b4054 := @add_cons V1 _ o1 b3757 (List.nil : V1) b3757 (List.nil : V2) b4056 b4056 b4054 e4087 e4088 (by rfl)
theorem e4090 : o2.mul b4053 b4=b4054 := @mul_cons V1 _ o1 b156 b4055 b4 b4056 b4101 b4102 b4054 e4083 e4086 (by rfl) e4089
theorem e4091 : o1.mul b155 b3=b3756 := by decide
theorem e4092 : o1.scale b155 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4093 : o1.scale b155 b4=b4103 := @scale_cons V1 _ o1 b155 b3 b3756 (List.nil : V2) (List.nil : V2) b4103 e4091 e4092 (by rfl)
theorem e4094 : o1.add b3756 (List.nil : V1)=b3756 := by rfl
theorem e4095 : o2.add (List.nil : V2) b4054=b4054 := by rfl
theorem e4096 : o2.add b4103 b4104=b4052 := @add_cons V1 _ o1 b3756 (List.nil : V1) b3756 (List.nil : V2) b4054 b4054 b4052 e4094 e4095 (by rfl)
theorem e4097 : o2.mul b4051 b4=b4052 := @mul_cons V1 _ o1 b155 b4053 b4 b4054 b4103 b4104 b4052 e4090 e4093 (by rfl) e4096
theorem e4098 : o2.add (List.nil : V2) b4050=b4050 := by rfl
theorem e4099 : o2.mul b4049 b4=b4050 := @mul_cons V1 _ o1 (List.nil : V1) b4051 b4 b4052 (List.nil : V2) b4050 b4050 e4097 e3697 (by rfl) e4098
theorem e4100 : o2.add (List.nil : V2) b3770=b3770 := by rfl
theorem e4101 : o2.mul b169 b4=b3770 := @mul_cons V1 _ o1 (List.nil : V1) b4049 b4 b4050 (List.nil : V2) b3770 b3770 e4099 e3697 (by rfl) e4100
theorem e4102 : o2.scale b169 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e4103 : o2.scale b169 b5=b4048 := @scale_cons V2 _ o2 b169 b4 b3770 (List.nil : V3) (List.nil : V3) b4048 e4101 e4102 (by rfl)
theorem e4104 : o2.add b3770 (List.nil : V2)=b3770 := by rfl
theorem e4105 : o3.add (List.nil : V3) b3831=b3831 := by rfl
theorem e4106 : o3.add b4048 b4105=b3829 := @add_cons V2 _ o2 b3770 (List.nil : V2) b3770 (List.nil : V3) b3831 b3831 b3829 e4104 e4105 (by rfl)
theorem e4107 : o3.mul b3828 b5=b3829 := @mul_cons V2 _ o2 b169 b3830 b5 b3831 b4048 b4105 b3829 e4001 e4103 (by rfl) e4106
theorem e4108 : o1.mul b153 b3=b3754 := by decide
theorem e4109 : o1.scale b153 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4110 : o1.scale b153 b4=b4136 := @scale_cons V1 _ o1 b153 b3 b3754 (List.nil : V2) (List.nil : V2) b4136 e4108 e4109 (by rfl)
theorem e4111 : o2.add b4136 (List.nil : V2)=b4136 := by rfl
theorem e4112 : o2.mul b4135 b4=b4136 := @mul_cons V1 _ o1 b153 (List.nil : V2) b4 (List.nil : V2) b4136 (List.nil : V2) b4136 e3626 e4110 (by rfl) e4111
theorem e4113 : o1.mul b152 b3=b3753 := by decide
theorem e4114 : o1.scale b152 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4115 : o1.scale b152 b4=b4137 := @scale_cons V1 _ o1 b152 b3 b3753 (List.nil : V2) (List.nil : V2) b4137 e4113 e4114 (by rfl)
theorem e4116 : o1.add b3753 (List.nil : V1)=b3753 := by rfl
theorem e4117 : o2.add (List.nil : V2) b4136=b4136 := by rfl
theorem e4118 : o2.add b4137 b4138=b4134 := @add_cons V1 _ o1 b3753 (List.nil : V1) b3753 (List.nil : V2) b4136 b4136 b4134 e4116 e4117 (by rfl)
theorem e4119 : o2.mul b4133 b4=b4134 := @mul_cons V1 _ o1 b152 b4135 b4 b4136 b4137 b4138 b4134 e4112 e4115 (by rfl) e4118
theorem e4120 : o1.mul b151 b3=b3752 := by decide
theorem e4121 : o1.scale b151 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4122 : o1.scale b151 b4=b4139 := @scale_cons V1 _ o1 b151 b3 b3752 (List.nil : V2) (List.nil : V2) b4139 e4120 e4121 (by rfl)
theorem e4123 : o1.add b3752 (List.nil : V1)=b3752 := by rfl
theorem e4124 : o2.add (List.nil : V2) b4134=b4134 := by rfl
theorem e4125 : o2.add b4139 b4140=b4132 := @add_cons V1 _ o1 b3752 (List.nil : V1) b3752 (List.nil : V2) b4134 b4134 b4132 e4123 e4124 (by rfl)
theorem e4126 : o2.mul b4131 b4=b4132 := @mul_cons V1 _ o1 b151 b4133 b4 b4134 b4139 b4140 b4132 e4119 e4122 (by rfl) e4125
theorem e4127 : o1.mul b150 b3=b3751 := by decide
theorem e4128 : o1.scale b150 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4129 : o1.scale b150 b4=b4141 := @scale_cons V1 _ o1 b150 b3 b3751 (List.nil : V2) (List.nil : V2) b4141 e4127 e4128 (by rfl)
theorem e4130 : o1.add b3751 (List.nil : V1)=b3751 := by rfl
theorem e4131 : o2.add (List.nil : V2) b4132=b4132 := by rfl
theorem e4132 : o2.add b4141 b4142=b4130 := @add_cons V1 _ o1 b3751 (List.nil : V1) b3751 (List.nil : V2) b4132 b4132 b4130 e4130 e4131 (by rfl)
theorem e4133 : o2.mul b4129 b4=b4130 := @mul_cons V1 _ o1 b150 b4131 b4 b4132 b4141 b4142 b4130 e4126 e4129 (by rfl) e4132
theorem e4134 : o1.mul b149 b3=b3750 := by decide
theorem e4135 : o1.scale b149 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4136 : o1.scale b149 b4=b4143 := @scale_cons V1 _ o1 b149 b3 b3750 (List.nil : V2) (List.nil : V2) b4143 e4134 e4135 (by rfl)
theorem e4137 : o1.add b3750 (List.nil : V1)=b3750 := by rfl
theorem e4138 : o2.add (List.nil : V2) b4130=b4130 := by rfl
theorem e4139 : o2.add b4143 b4144=b4128 := @add_cons V1 _ o1 b3750 (List.nil : V1) b3750 (List.nil : V2) b4130 b4130 b4128 e4137 e4138 (by rfl)
theorem e4140 : o2.mul b4127 b4=b4128 := @mul_cons V1 _ o1 b149 b4129 b4 b4130 b4143 b4144 b4128 e4133 e4136 (by rfl) e4139
theorem e4141 : o1.mul b148 b3=b3749 := by decide
theorem e4142 : o1.scale b148 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4143 : o1.scale b148 b4=b4145 := @scale_cons V1 _ o1 b148 b3 b3749 (List.nil : V2) (List.nil : V2) b4145 e4141 e4142 (by rfl)
theorem e4144 : o1.add b3749 (List.nil : V1)=b3749 := by rfl
theorem e4145 : o2.add (List.nil : V2) b4128=b4128 := by rfl
theorem e4146 : o2.add b4145 b4146=b4126 := @add_cons V1 _ o1 b3749 (List.nil : V1) b3749 (List.nil : V2) b4128 b4128 b4126 e4144 e4145 (by rfl)
theorem e4147 : o2.mul b4125 b4=b4126 := @mul_cons V1 _ o1 b148 b4127 b4 b4128 b4145 b4146 b4126 e4140 e4143 (by rfl) e4146
theorem e4148 : o1.mul b147 b3=b3748 := by decide
theorem e4149 : o1.scale b147 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4150 : o1.scale b147 b4=b4147 := @scale_cons V1 _ o1 b147 b3 b3748 (List.nil : V2) (List.nil : V2) b4147 e4148 e4149 (by rfl)
theorem e4151 : o1.add b3748 (List.nil : V1)=b3748 := by rfl
theorem e4152 : o2.add (List.nil : V2) b4126=b4126 := by rfl
theorem e4153 : o2.add b4147 b4148=b4124 := @add_cons V1 _ o1 b3748 (List.nil : V1) b3748 (List.nil : V2) b4126 b4126 b4124 e4151 e4152 (by rfl)
theorem e4154 : o2.mul b4123 b4=b4124 := @mul_cons V1 _ o1 b147 b4125 b4 b4126 b4147 b4148 b4124 e4147 e4150 (by rfl) e4153
theorem e4155 : o1.mul b146 b3=b3747 := by decide
theorem e4156 : o1.scale b146 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4157 : o1.scale b146 b4=b4149 := @scale_cons V1 _ o1 b146 b3 b3747 (List.nil : V2) (List.nil : V2) b4149 e4155 e4156 (by rfl)
theorem e4158 : o1.add b3747 (List.nil : V1)=b3747 := by rfl
theorem e4159 : o2.add (List.nil : V2) b4124=b4124 := by rfl
theorem e4160 : o2.add b4149 b4150=b4122 := @add_cons V1 _ o1 b3747 (List.nil : V1) b3747 (List.nil : V2) b4124 b4124 b4122 e4158 e4159 (by rfl)
theorem e4161 : o2.mul b4121 b4=b4122 := @mul_cons V1 _ o1 b146 b4123 b4 b4124 b4149 b4150 b4122 e4154 e4157 (by rfl) e4160
theorem e4162 : o1.mul b145 b3=b3746 := by decide
theorem e4163 : o1.scale b145 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4164 : o1.scale b145 b4=b4151 := @scale_cons V1 _ o1 b145 b3 b3746 (List.nil : V2) (List.nil : V2) b4151 e4162 e4163 (by rfl)
theorem e4165 : o1.add b3746 (List.nil : V1)=b3746 := by rfl
theorem e4166 : o2.add (List.nil : V2) b4122=b4122 := by rfl
theorem e4167 : o2.add b4151 b4152=b4120 := @add_cons V1 _ o1 b3746 (List.nil : V1) b3746 (List.nil : V2) b4122 b4122 b4120 e4165 e4166 (by rfl)
theorem e4168 : o2.mul b4119 b4=b4120 := @mul_cons V1 _ o1 b145 b4121 b4 b4122 b4151 b4152 b4120 e4161 e4164 (by rfl) e4167
theorem e4169 : o1.mul b144 b3=b3745 := by decide
theorem e4170 : o1.scale b144 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4171 : o1.scale b144 b4=b4153 := @scale_cons V1 _ o1 b144 b3 b3745 (List.nil : V2) (List.nil : V2) b4153 e4169 e4170 (by rfl)
theorem e4172 : o1.add b3745 (List.nil : V1)=b3745 := by rfl
theorem e4173 : o2.add (List.nil : V2) b4120=b4120 := by rfl
theorem e4174 : o2.add b4153 b4154=b4118 := @add_cons V1 _ o1 b3745 (List.nil : V1) b3745 (List.nil : V2) b4120 b4120 b4118 e4172 e4173 (by rfl)
theorem e4175 : o2.mul b4117 b4=b4118 := @mul_cons V1 _ o1 b144 b4119 b4 b4120 b4153 b4154 b4118 e4168 e4171 (by rfl) e4174
theorem e4176 : o1.mul b143 b3=b3744 := by decide
theorem e4177 : o1.scale b143 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4178 : o1.scale b143 b4=b4155 := @scale_cons V1 _ o1 b143 b3 b3744 (List.nil : V2) (List.nil : V2) b4155 e4176 e4177 (by rfl)
theorem e4179 : o1.add b3744 (List.nil : V1)=b3744 := by rfl
theorem e4180 : o2.add (List.nil : V2) b4118=b4118 := by rfl
theorem e4181 : o2.add b4155 b4156=b4116 := @add_cons V1 _ o1 b3744 (List.nil : V1) b3744 (List.nil : V2) b4118 b4118 b4116 e4179 e4180 (by rfl)
theorem e4182 : o2.mul b4115 b4=b4116 := @mul_cons V1 _ o1 b143 b4117 b4 b4118 b4155 b4156 b4116 e4175 e4178 (by rfl) e4181
theorem e4183 : o1.mul b142 b3=b3743 := by decide
theorem e4184 : o1.scale b142 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4185 : o1.scale b142 b4=b4157 := @scale_cons V1 _ o1 b142 b3 b3743 (List.nil : V2) (List.nil : V2) b4157 e4183 e4184 (by rfl)
theorem e4186 : o1.add b3743 (List.nil : V1)=b3743 := by rfl
theorem e4187 : o2.add (List.nil : V2) b4116=b4116 := by rfl
theorem e4188 : o2.add b4157 b4158=b4114 := @add_cons V1 _ o1 b3743 (List.nil : V1) b3743 (List.nil : V2) b4116 b4116 b4114 e4186 e4187 (by rfl)
theorem e4189 : o2.mul b4113 b4=b4114 := @mul_cons V1 _ o1 b142 b4115 b4 b4116 b4157 b4158 b4114 e4182 e4185 (by rfl) e4188
theorem e4190 : o1.mul b141 b3=b3742 := by decide
theorem e4191 : o1.scale b141 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4192 : o1.scale b141 b4=b4159 := @scale_cons V1 _ o1 b141 b3 b3742 (List.nil : V2) (List.nil : V2) b4159 e4190 e4191 (by rfl)
theorem e4193 : o1.add b3742 (List.nil : V1)=b3742 := by rfl
theorem e4194 : o2.add (List.nil : V2) b4114=b4114 := by rfl
theorem e4195 : o2.add b4159 b4160=b4112 := @add_cons V1 _ o1 b3742 (List.nil : V1) b3742 (List.nil : V2) b4114 b4114 b4112 e4193 e4194 (by rfl)
theorem e4196 : o2.mul b4111 b4=b4112 := @mul_cons V1 _ o1 b141 b4113 b4 b4114 b4159 b4160 b4112 e4189 e4192 (by rfl) e4195
theorem e4197 : o1.mul b140 b3=b3741 := by decide
theorem e4198 : o1.scale b140 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4199 : o1.scale b140 b4=b4161 := @scale_cons V1 _ o1 b140 b3 b3741 (List.nil : V2) (List.nil : V2) b4161 e4197 e4198 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
