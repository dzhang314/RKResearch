module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart028

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4200 : o1.add b3741 (List.nil : V1)=b3741 := by rfl
theorem e4201 : o2.add (List.nil : V2) b4112=b4112 := by rfl
theorem e4202 : o2.add b4161 b4162=b4110 := @add_cons V1 _ o1 b3741 (List.nil : V1) b3741 (List.nil : V2) b4112 b4112 b4110 e4200 e4201 (by rfl)
theorem e4203 : o2.mul b4109 b4=b4110 := @mul_cons V1 _ o1 b140 b4111 b4 b4112 b4161 b4162 b4110 e4196 e4199 (by rfl) e4202
theorem e4204 : o1.mul b139 b3=b3740 := by decide
theorem e4205 : o1.scale b139 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4206 : o1.scale b139 b4=b4163 := @scale_cons V1 _ o1 b139 b3 b3740 (List.nil : V2) (List.nil : V2) b4163 e4204 e4205 (by rfl)
theorem e4207 : o1.add b3740 (List.nil : V1)=b3740 := by rfl
theorem e4208 : o2.add (List.nil : V2) b4110=b4110 := by rfl
theorem e4209 : o2.add b4163 b4164=b4108 := @add_cons V1 _ o1 b3740 (List.nil : V1) b3740 (List.nil : V2) b4110 b4110 b4108 e4207 e4208 (by rfl)
theorem e4210 : o2.mul b4107 b4=b4108 := @mul_cons V1 _ o1 b139 b4109 b4 b4110 b4163 b4164 b4108 e4203 e4206 (by rfl) e4209
theorem e4211 : o2.add (List.nil : V2) b3755=b3755 := by rfl
theorem e4212 : o2.mul b154 b4=b3755 := @mul_cons V1 _ o1 (List.nil : V1) b4107 b4 b4108 (List.nil : V2) b3755 b3755 e4210 e3697 (by rfl) e4211
theorem e4213 : o2.scale b154 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e4214 : o2.scale b154 b5=b4106 := @scale_cons V2 _ o2 b154 b4 b3755 (List.nil : V3) (List.nil : V3) b4106 e4212 e4213 (by rfl)
theorem e4215 : o2.add b3755 (List.nil : V2)=b3755 := by rfl
theorem e4216 : o3.add (List.nil : V3) b3829=b3829 := by rfl
theorem e4217 : o3.add b4106 b4165=b3827 := @add_cons V2 _ o2 b3755 (List.nil : V2) b3755 (List.nil : V3) b3829 b3829 b3827 e4215 e4216 (by rfl)
theorem e4218 : o3.mul b3826 b5=b3827 := @mul_cons V2 _ o2 b154 b3828 b5 b3829 b4106 b4165 b3827 e4107 e4214 (by rfl) e4217
theorem e4219 : o1.mul b137 b3=b3738 := by decide
theorem e4220 : o1.scale b137 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4221 : o1.scale b137 b4=b4196 := @scale_cons V1 _ o1 b137 b3 b3738 (List.nil : V2) (List.nil : V2) b4196 e4219 e4220 (by rfl)
theorem e4222 : o2.add b4196 (List.nil : V2)=b4196 := by rfl
theorem e4223 : o2.mul b4195 b4=b4196 := @mul_cons V1 _ o1 b137 (List.nil : V2) b4 (List.nil : V2) b4196 (List.nil : V2) b4196 e3626 e4221 (by rfl) e4222
theorem e4224 : o1.mul b136 b3=b3737 := by decide
theorem e4225 : o1.scale b136 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4226 : o1.scale b136 b4=b4197 := @scale_cons V1 _ o1 b136 b3 b3737 (List.nil : V2) (List.nil : V2) b4197 e4224 e4225 (by rfl)
theorem e4227 : o1.add b3737 (List.nil : V1)=b3737 := by rfl
theorem e4228 : o2.add (List.nil : V2) b4196=b4196 := by rfl
theorem e4229 : o2.add b4197 b4198=b4194 := @add_cons V1 _ o1 b3737 (List.nil : V1) b3737 (List.nil : V2) b4196 b4196 b4194 e4227 e4228 (by rfl)
theorem e4230 : o2.mul b4193 b4=b4194 := @mul_cons V1 _ o1 b136 b4195 b4 b4196 b4197 b4198 b4194 e4223 e4226 (by rfl) e4229
theorem e4231 : o1.mul b135 b3=b3736 := by decide
theorem e4232 : o1.scale b135 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4233 : o1.scale b135 b4=b4199 := @scale_cons V1 _ o1 b135 b3 b3736 (List.nil : V2) (List.nil : V2) b4199 e4231 e4232 (by rfl)
theorem e4234 : o1.add b3736 (List.nil : V1)=b3736 := by rfl
theorem e4235 : o2.add (List.nil : V2) b4194=b4194 := by rfl
theorem e4236 : o2.add b4199 b4200=b4192 := @add_cons V1 _ o1 b3736 (List.nil : V1) b3736 (List.nil : V2) b4194 b4194 b4192 e4234 e4235 (by rfl)
theorem e4237 : o2.mul b4191 b4=b4192 := @mul_cons V1 _ o1 b135 b4193 b4 b4194 b4199 b4200 b4192 e4230 e4233 (by rfl) e4236
theorem e4238 : o1.mul b134 b3=b3735 := by decide
theorem e4239 : o1.scale b134 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4240 : o1.scale b134 b4=b4201 := @scale_cons V1 _ o1 b134 b3 b3735 (List.nil : V2) (List.nil : V2) b4201 e4238 e4239 (by rfl)
theorem e4241 : o1.add b3735 (List.nil : V1)=b3735 := by rfl
theorem e4242 : o2.add (List.nil : V2) b4192=b4192 := by rfl
theorem e4243 : o2.add b4201 b4202=b4190 := @add_cons V1 _ o1 b3735 (List.nil : V1) b3735 (List.nil : V2) b4192 b4192 b4190 e4241 e4242 (by rfl)
theorem e4244 : o2.mul b4189 b4=b4190 := @mul_cons V1 _ o1 b134 b4191 b4 b4192 b4201 b4202 b4190 e4237 e4240 (by rfl) e4243
theorem e4245 : o1.mul b133 b3=b3734 := by decide
theorem e4246 : o1.scale b133 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4247 : o1.scale b133 b4=b4203 := @scale_cons V1 _ o1 b133 b3 b3734 (List.nil : V2) (List.nil : V2) b4203 e4245 e4246 (by rfl)
theorem e4248 : o1.add b3734 (List.nil : V1)=b3734 := by rfl
theorem e4249 : o2.add (List.nil : V2) b4190=b4190 := by rfl
theorem e4250 : o2.add b4203 b4204=b4188 := @add_cons V1 _ o1 b3734 (List.nil : V1) b3734 (List.nil : V2) b4190 b4190 b4188 e4248 e4249 (by rfl)
theorem e4251 : o2.mul b4187 b4=b4188 := @mul_cons V1 _ o1 b133 b4189 b4 b4190 b4203 b4204 b4188 e4244 e4247 (by rfl) e4250
theorem e4252 : o1.mul b132 b3=b3733 := by decide
theorem e4253 : o1.scale b132 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4254 : o1.scale b132 b4=b4205 := @scale_cons V1 _ o1 b132 b3 b3733 (List.nil : V2) (List.nil : V2) b4205 e4252 e4253 (by rfl)
theorem e4255 : o1.add b3733 (List.nil : V1)=b3733 := by rfl
theorem e4256 : o2.add (List.nil : V2) b4188=b4188 := by rfl
theorem e4257 : o2.add b4205 b4206=b4186 := @add_cons V1 _ o1 b3733 (List.nil : V1) b3733 (List.nil : V2) b4188 b4188 b4186 e4255 e4256 (by rfl)
theorem e4258 : o2.mul b4185 b4=b4186 := @mul_cons V1 _ o1 b132 b4187 b4 b4188 b4205 b4206 b4186 e4251 e4254 (by rfl) e4257
theorem e4259 : o1.mul b131 b3=b3732 := by decide
theorem e4260 : o1.scale b131 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4261 : o1.scale b131 b4=b4207 := @scale_cons V1 _ o1 b131 b3 b3732 (List.nil : V2) (List.nil : V2) b4207 e4259 e4260 (by rfl)
theorem e4262 : o1.add b3732 (List.nil : V1)=b3732 := by rfl
theorem e4263 : o2.add (List.nil : V2) b4186=b4186 := by rfl
theorem e4264 : o2.add b4207 b4208=b4184 := @add_cons V1 _ o1 b3732 (List.nil : V1) b3732 (List.nil : V2) b4186 b4186 b4184 e4262 e4263 (by rfl)
theorem e4265 : o2.mul b4183 b4=b4184 := @mul_cons V1 _ o1 b131 b4185 b4 b4186 b4207 b4208 b4184 e4258 e4261 (by rfl) e4264
theorem e4266 : o1.mul b130 b3=b3731 := by decide
theorem e4267 : o1.scale b130 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4268 : o1.scale b130 b4=b4209 := @scale_cons V1 _ o1 b130 b3 b3731 (List.nil : V2) (List.nil : V2) b4209 e4266 e4267 (by rfl)
theorem e4269 : o1.add b3731 (List.nil : V1)=b3731 := by rfl
theorem e4270 : o2.add (List.nil : V2) b4184=b4184 := by rfl
theorem e4271 : o2.add b4209 b4210=b4182 := @add_cons V1 _ o1 b3731 (List.nil : V1) b3731 (List.nil : V2) b4184 b4184 b4182 e4269 e4270 (by rfl)
theorem e4272 : o2.mul b4181 b4=b4182 := @mul_cons V1 _ o1 b130 b4183 b4 b4184 b4209 b4210 b4182 e4265 e4268 (by rfl) e4271
theorem e4273 : o1.mul b129 b3=b3730 := by decide
theorem e4274 : o1.scale b129 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4275 : o1.scale b129 b4=b4211 := @scale_cons V1 _ o1 b129 b3 b3730 (List.nil : V2) (List.nil : V2) b4211 e4273 e4274 (by rfl)
theorem e4276 : o1.add b3730 (List.nil : V1)=b3730 := by rfl
theorem e4277 : o2.add (List.nil : V2) b4182=b4182 := by rfl
theorem e4278 : o2.add b4211 b4212=b4180 := @add_cons V1 _ o1 b3730 (List.nil : V1) b3730 (List.nil : V2) b4182 b4182 b4180 e4276 e4277 (by rfl)
theorem e4279 : o2.mul b4179 b4=b4180 := @mul_cons V1 _ o1 b129 b4181 b4 b4182 b4211 b4212 b4180 e4272 e4275 (by rfl) e4278
theorem e4280 : o1.mul b128 b3=b3729 := by decide
theorem e4281 : o1.scale b128 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4282 : o1.scale b128 b4=b4213 := @scale_cons V1 _ o1 b128 b3 b3729 (List.nil : V2) (List.nil : V2) b4213 e4280 e4281 (by rfl)
theorem e4283 : o1.add b3729 (List.nil : V1)=b3729 := by rfl
theorem e4284 : o2.add (List.nil : V2) b4180=b4180 := by rfl
theorem e4285 : o2.add b4213 b4214=b4178 := @add_cons V1 _ o1 b3729 (List.nil : V1) b3729 (List.nil : V2) b4180 b4180 b4178 e4283 e4284 (by rfl)
theorem e4286 : o2.mul b4177 b4=b4178 := @mul_cons V1 _ o1 b128 b4179 b4 b4180 b4213 b4214 b4178 e4279 e4282 (by rfl) e4285
theorem e4287 : o1.mul b127 b3=b3728 := by decide
theorem e4288 : o1.scale b127 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4289 : o1.scale b127 b4=b4215 := @scale_cons V1 _ o1 b127 b3 b3728 (List.nil : V2) (List.nil : V2) b4215 e4287 e4288 (by rfl)
theorem e4290 : o1.add b3728 (List.nil : V1)=b3728 := by rfl
theorem e4291 : o2.add (List.nil : V2) b4178=b4178 := by rfl
theorem e4292 : o2.add b4215 b4216=b4176 := @add_cons V1 _ o1 b3728 (List.nil : V1) b3728 (List.nil : V2) b4178 b4178 b4176 e4290 e4291 (by rfl)
theorem e4293 : o2.mul b4175 b4=b4176 := @mul_cons V1 _ o1 b127 b4177 b4 b4178 b4215 b4216 b4176 e4286 e4289 (by rfl) e4292
theorem e4294 : o1.mul b126 b3=b3727 := by decide
theorem e4295 : o1.scale b126 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4296 : o1.scale b126 b4=b4217 := @scale_cons V1 _ o1 b126 b3 b3727 (List.nil : V2) (List.nil : V2) b4217 e4294 e4295 (by rfl)
theorem e4297 : o1.add b3727 (List.nil : V1)=b3727 := by rfl
theorem e4298 : o2.add (List.nil : V2) b4176=b4176 := by rfl
theorem e4299 : o2.add b4217 b4218=b4174 := @add_cons V1 _ o1 b3727 (List.nil : V1) b3727 (List.nil : V2) b4176 b4176 b4174 e4297 e4298 (by rfl)
theorem e4300 : o2.mul b4173 b4=b4174 := @mul_cons V1 _ o1 b126 b4175 b4 b4176 b4217 b4218 b4174 e4293 e4296 (by rfl) e4299
theorem e4301 : o1.mul b125 b3=b3726 := by decide
theorem e4302 : o1.scale b125 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4303 : o1.scale b125 b4=b4219 := @scale_cons V1 _ o1 b125 b3 b3726 (List.nil : V2) (List.nil : V2) b4219 e4301 e4302 (by rfl)
theorem e4304 : o1.add b3726 (List.nil : V1)=b3726 := by rfl
theorem e4305 : o2.add (List.nil : V2) b4174=b4174 := by rfl
theorem e4306 : o2.add b4219 b4220=b4172 := @add_cons V1 _ o1 b3726 (List.nil : V1) b3726 (List.nil : V2) b4174 b4174 b4172 e4304 e4305 (by rfl)
theorem e4307 : o2.mul b4171 b4=b4172 := @mul_cons V1 _ o1 b125 b4173 b4 b4174 b4219 b4220 b4172 e4300 e4303 (by rfl) e4306
theorem e4308 : o1.mul b124 b3=b3725 := by decide
theorem e4309 : o1.scale b124 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4310 : o1.scale b124 b4=b4221 := @scale_cons V1 _ o1 b124 b3 b3725 (List.nil : V2) (List.nil : V2) b4221 e4308 e4309 (by rfl)
theorem e4311 : o1.add b3725 (List.nil : V1)=b3725 := by rfl
theorem e4312 : o2.add (List.nil : V2) b4172=b4172 := by rfl
theorem e4313 : o2.add b4221 b4222=b4170 := @add_cons V1 _ o1 b3725 (List.nil : V1) b3725 (List.nil : V2) b4172 b4172 b4170 e4311 e4312 (by rfl)
theorem e4314 : o2.mul b4169 b4=b4170 := @mul_cons V1 _ o1 b124 b4171 b4 b4172 b4221 b4222 b4170 e4307 e4310 (by rfl) e4313
theorem e4315 : o1.mul b123 b3=b3724 := by decide
theorem e4316 : o1.scale b123 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4317 : o1.scale b123 b4=b4223 := @scale_cons V1 _ o1 b123 b3 b3724 (List.nil : V2) (List.nil : V2) b4223 e4315 e4316 (by rfl)
theorem e4318 : o1.add b3724 (List.nil : V1)=b3724 := by rfl
theorem e4319 : o2.add (List.nil : V2) b4170=b4170 := by rfl
theorem e4320 : o2.add b4223 b4224=b4168 := @add_cons V1 _ o1 b3724 (List.nil : V1) b3724 (List.nil : V2) b4170 b4170 b4168 e4318 e4319 (by rfl)
theorem e4321 : o2.mul b4167 b4=b4168 := @mul_cons V1 _ o1 b123 b4169 b4 b4170 b4223 b4224 b4168 e4314 e4317 (by rfl) e4320
theorem e4322 : o2.add (List.nil : V2) b3739=b3739 := by rfl
theorem e4323 : o2.mul b138 b4=b3739 := @mul_cons V1 _ o1 (List.nil : V1) b4167 b4 b4168 (List.nil : V2) b3739 b3739 e4321 e3697 (by rfl) e4322
theorem e4324 : o2.scale b138 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e4325 : o2.scale b138 b5=b4166 := @scale_cons V2 _ o2 b138 b4 b3739 (List.nil : V3) (List.nil : V3) b4166 e4323 e4324 (by rfl)
theorem e4326 : o2.add b3739 (List.nil : V2)=b3739 := by rfl
theorem e4327 : o3.add (List.nil : V3) b3827=b3827 := by rfl
theorem e4328 : o3.add b4166 b4225=b3825 := @add_cons V2 _ o2 b3739 (List.nil : V2) b3739 (List.nil : V3) b3827 b3827 b3825 e4326 e4327 (by rfl)
theorem e4329 : o3.mul b3824 b5=b3825 := @mul_cons V2 _ o2 b138 b3826 b5 b3827 b4166 b4225 b3825 e4218 e4325 (by rfl) e4328
theorem e4330 : o1.mul b121 b3=b3722 := by decide
theorem e4331 : o1.scale b121 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4332 : o1.scale b121 b4=b4256 := @scale_cons V1 _ o1 b121 b3 b3722 (List.nil : V2) (List.nil : V2) b4256 e4330 e4331 (by rfl)
theorem e4333 : o2.add b4256 (List.nil : V2)=b4256 := by rfl
theorem e4334 : o2.mul b4255 b4=b4256 := @mul_cons V1 _ o1 b121 (List.nil : V2) b4 (List.nil : V2) b4256 (List.nil : V2) b4256 e3626 e4332 (by rfl) e4333
theorem e4335 : o1.mul b120 b3=b3721 := by decide
theorem e4336 : o1.scale b120 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4337 : o1.scale b120 b4=b4257 := @scale_cons V1 _ o1 b120 b3 b3721 (List.nil : V2) (List.nil : V2) b4257 e4335 e4336 (by rfl)
theorem e4338 : o1.add b3721 (List.nil : V1)=b3721 := by rfl
theorem e4339 : o2.add (List.nil : V2) b4256=b4256 := by rfl
theorem e4340 : o2.add b4257 b4258=b4254 := @add_cons V1 _ o1 b3721 (List.nil : V1) b3721 (List.nil : V2) b4256 b4256 b4254 e4338 e4339 (by rfl)
theorem e4341 : o2.mul b4253 b4=b4254 := @mul_cons V1 _ o1 b120 b4255 b4 b4256 b4257 b4258 b4254 e4334 e4337 (by rfl) e4340
theorem e4342 : o1.mul b119 b3=b3720 := by decide
theorem e4343 : o1.scale b119 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4344 : o1.scale b119 b4=b4259 := @scale_cons V1 _ o1 b119 b3 b3720 (List.nil : V2) (List.nil : V2) b4259 e4342 e4343 (by rfl)
theorem e4345 : o1.add b3720 (List.nil : V1)=b3720 := by rfl
theorem e4346 : o2.add (List.nil : V2) b4254=b4254 := by rfl
theorem e4347 : o2.add b4259 b4260=b4252 := @add_cons V1 _ o1 b3720 (List.nil : V1) b3720 (List.nil : V2) b4254 b4254 b4252 e4345 e4346 (by rfl)
theorem e4348 : o2.mul b4251 b4=b4252 := @mul_cons V1 _ o1 b119 b4253 b4 b4254 b4259 b4260 b4252 e4341 e4344 (by rfl) e4347
theorem e4349 : o1.mul b118 b3=b3719 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
