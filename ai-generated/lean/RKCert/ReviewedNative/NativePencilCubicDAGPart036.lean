module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart035

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5250 : o2.mul b4884 b12=b4890 := @mul_cons V1 _ o1 b226 b4891 b12 b4897 b5004 b5010 b4890 e5223 e5236 (by rfl) e5249
theorem e5251 : o1.mul b225 b6=b4878 := by decide
theorem e5252 : o1.mul b225 b7=b5016 := by decide
theorem e5253 : o1.mul b225 b8=b5017 := by decide
theorem e5254 : o1.mul b225 b9=b5018 := by decide
theorem e5255 : o1.mul b225 b10=b5019 := by decide
theorem e5256 : o1.mul b225 b11=b5020 := by decide
theorem e5257 : o1.scale b225 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5258 : o1.scale b225 b4475=b5026 := @scale_cons V1 _ o1 b225 b11 b5020 (List.nil : V2) (List.nil : V2) b5026 e5256 e5257 (by rfl)
theorem e5259 : o1.scale b225 b4473=b5025 := @scale_cons V1 _ o1 b225 b10 b5019 b4475 b5026 b5025 e5255 e5258 (by rfl)
theorem e5260 : o1.scale b225 b4471=b5024 := @scale_cons V1 _ o1 b225 b9 b5018 b4473 b5025 b5024 e5254 e5259 (by rfl)
theorem e5261 : o1.scale b225 b4469=b5023 := @scale_cons V1 _ o1 b225 b8 b5017 b4471 b5024 b5023 e5253 e5260 (by rfl)
theorem e5262 : o1.scale b225 b4467=b5022 := @scale_cons V1 _ o1 b225 b7 b5016 b4469 b5023 b5022 e5252 e5261 (by rfl)
theorem e5263 : o1.scale b225 b12=b5021 := @scale_cons V1 _ o1 b225 b6 b4878 b4467 b5022 b5021 e5251 e5262 (by rfl)
theorem e5264 : o1.add b4878 (List.nil : V1)=b4878 := by rfl
theorem e5265 : o1.add b5016 b4885=b4879 := by decide
theorem e5266 : o1.add b5017 b4886=b4880 := by decide
theorem e5267 : o1.add b5018 b4887=b4881 := by decide
theorem e5268 : o1.add b5019 b4888=b4882 := by decide
theorem e5269 : o1.add b5020 b4889=b4357 := by decide
theorem e5270 : o2.add (List.nil : V2) b5015=b5015 := by rfl
theorem e5271 : o2.add b5026 b5014=b5032 := @add_cons V1 _ o1 b5020 b4889 b4357 (List.nil : V2) b5015 b5015 b5032 e5269 e5270 (by rfl)
theorem e5272 : o2.add b5025 b5013=b5031 := @add_cons V1 _ o1 b5019 b4888 b4882 b5026 b5014 b5032 b5031 e5268 e5271 (by rfl)
theorem e5273 : o2.add b5024 b5012=b5030 := @add_cons V1 _ o1 b5018 b4887 b4881 b5025 b5013 b5031 b5030 e5267 e5272 (by rfl)
theorem e5274 : o2.add b5023 b5011=b5029 := @add_cons V1 _ o1 b5017 b4886 b4880 b5024 b5012 b5030 b5029 e5266 e5273 (by rfl)
theorem e5275 : o2.add b5022 b4890=b5028 := @add_cons V1 _ o1 b5016 b4885 b4879 b5023 b5011 b5029 b5028 e5265 e5274 (by rfl)
theorem e5276 : o2.add b5021 b5027=b4883 := @add_cons V1 _ o1 b4878 (List.nil : V1) b4878 b5022 b4890 b5028 b4883 e5264 e5275 (by rfl)
theorem e5277 : o2.mul b4877 b12=b4883 := @mul_cons V1 _ o1 b225 b4884 b12 b4890 b5021 b5027 b4883 e5250 e5263 (by rfl) e5276
theorem e5278 : o1.mul b224 b6=b4871 := by decide
theorem e5279 : o1.mul b224 b7=b5033 := by decide
theorem e5280 : o1.mul b224 b8=b5034 := by decide
theorem e5281 : o1.mul b224 b9=b5035 := by decide
theorem e5282 : o1.mul b224 b10=b5036 := by decide
theorem e5283 : o1.mul b224 b11=b5037 := by decide
theorem e5284 : o1.scale b224 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5285 : o1.scale b224 b4475=b5043 := @scale_cons V1 _ o1 b224 b11 b5037 (List.nil : V2) (List.nil : V2) b5043 e5283 e5284 (by rfl)
theorem e5286 : o1.scale b224 b4473=b5042 := @scale_cons V1 _ o1 b224 b10 b5036 b4475 b5043 b5042 e5282 e5285 (by rfl)
theorem e5287 : o1.scale b224 b4471=b5041 := @scale_cons V1 _ o1 b224 b9 b5035 b4473 b5042 b5041 e5281 e5286 (by rfl)
theorem e5288 : o1.scale b224 b4469=b5040 := @scale_cons V1 _ o1 b224 b8 b5034 b4471 b5041 b5040 e5280 e5287 (by rfl)
theorem e5289 : o1.scale b224 b4467=b5039 := @scale_cons V1 _ o1 b224 b7 b5033 b4469 b5040 b5039 e5279 e5288 (by rfl)
theorem e5290 : o1.scale b224 b12=b5038 := @scale_cons V1 _ o1 b224 b6 b4871 b4467 b5039 b5038 e5278 e5289 (by rfl)
theorem e5291 : o1.add b4871 (List.nil : V1)=b4871 := by rfl
theorem e5292 : o1.add b5033 b4878=b4872 := by decide
theorem e5293 : o1.add b5034 b4879=b4873 := by decide
theorem e5294 : o1.add b5035 b4880=b4874 := by decide
theorem e5295 : o1.add b5036 b4881=b4875 := by decide
theorem e5296 : o1.add b5037 b4882=b4356 := by decide
theorem e5297 : o2.add (List.nil : V2) b5032=b5032 := by rfl
theorem e5298 : o2.add b5043 b5031=b5049 := @add_cons V1 _ o1 b5037 b4882 b4356 (List.nil : V2) b5032 b5032 b5049 e5296 e5297 (by rfl)
theorem e5299 : o2.add b5042 b5030=b5048 := @add_cons V1 _ o1 b5036 b4881 b4875 b5043 b5031 b5049 b5048 e5295 e5298 (by rfl)
theorem e5300 : o2.add b5041 b5029=b5047 := @add_cons V1 _ o1 b5035 b4880 b4874 b5042 b5030 b5048 b5047 e5294 e5299 (by rfl)
theorem e5301 : o2.add b5040 b5028=b5046 := @add_cons V1 _ o1 b5034 b4879 b4873 b5041 b5029 b5047 b5046 e5293 e5300 (by rfl)
theorem e5302 : o2.add b5039 b4883=b5045 := @add_cons V1 _ o1 b5033 b4878 b4872 b5040 b5028 b5046 b5045 e5292 e5301 (by rfl)
theorem e5303 : o2.add b5038 b5044=b4876 := @add_cons V1 _ o1 b4871 (List.nil : V1) b4871 b5039 b4883 b5045 b4876 e5291 e5302 (by rfl)
theorem e5304 : o2.mul b4870 b12=b4876 := @mul_cons V1 _ o1 b224 b4877 b12 b4883 b5038 b5044 b4876 e5277 e5290 (by rfl) e5303
theorem e5305 : o1.mul b223 b6=b4864 := by decide
theorem e5306 : o1.mul b223 b7=b5050 := by decide
theorem e5307 : o1.mul b223 b8=b5051 := by decide
theorem e5308 : o1.mul b223 b9=b5052 := by decide
theorem e5309 : o1.mul b223 b10=b5053 := by decide
theorem e5310 : o1.mul b223 b11=b5054 := by decide
theorem e5311 : o1.scale b223 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5312 : o1.scale b223 b4475=b5060 := @scale_cons V1 _ o1 b223 b11 b5054 (List.nil : V2) (List.nil : V2) b5060 e5310 e5311 (by rfl)
theorem e5313 : o1.scale b223 b4473=b5059 := @scale_cons V1 _ o1 b223 b10 b5053 b4475 b5060 b5059 e5309 e5312 (by rfl)
theorem e5314 : o1.scale b223 b4471=b5058 := @scale_cons V1 _ o1 b223 b9 b5052 b4473 b5059 b5058 e5308 e5313 (by rfl)
theorem e5315 : o1.scale b223 b4469=b5057 := @scale_cons V1 _ o1 b223 b8 b5051 b4471 b5058 b5057 e5307 e5314 (by rfl)
theorem e5316 : o1.scale b223 b4467=b5056 := @scale_cons V1 _ o1 b223 b7 b5050 b4469 b5057 b5056 e5306 e5315 (by rfl)
theorem e5317 : o1.scale b223 b12=b5055 := @scale_cons V1 _ o1 b223 b6 b4864 b4467 b5056 b5055 e5305 e5316 (by rfl)
theorem e5318 : o1.add b4864 (List.nil : V1)=b4864 := by rfl
theorem e5319 : o1.add b5050 b4871=b4865 := by decide
theorem e5320 : o1.add b5051 b4872=b4866 := by decide
theorem e5321 : o1.add b5052 b4873=b4867 := by decide
theorem e5322 : o1.add b5053 b4874=b4868 := by decide
theorem e5323 : o1.add b5054 b4875=b4355 := by decide
theorem e5324 : o2.add (List.nil : V2) b5049=b5049 := by rfl
theorem e5325 : o2.add b5060 b5048=b5066 := @add_cons V1 _ o1 b5054 b4875 b4355 (List.nil : V2) b5049 b5049 b5066 e5323 e5324 (by rfl)
theorem e5326 : o2.add b5059 b5047=b5065 := @add_cons V1 _ o1 b5053 b4874 b4868 b5060 b5048 b5066 b5065 e5322 e5325 (by rfl)
theorem e5327 : o2.add b5058 b5046=b5064 := @add_cons V1 _ o1 b5052 b4873 b4867 b5059 b5047 b5065 b5064 e5321 e5326 (by rfl)
theorem e5328 : o2.add b5057 b5045=b5063 := @add_cons V1 _ o1 b5051 b4872 b4866 b5058 b5046 b5064 b5063 e5320 e5327 (by rfl)
theorem e5329 : o2.add b5056 b4876=b5062 := @add_cons V1 _ o1 b5050 b4871 b4865 b5057 b5045 b5063 b5062 e5319 e5328 (by rfl)
theorem e5330 : o2.add b5055 b5061=b4869 := @add_cons V1 _ o1 b4864 (List.nil : V1) b4864 b5056 b4876 b5062 b4869 e5318 e5329 (by rfl)
theorem e5331 : o2.mul b4863 b12=b4869 := @mul_cons V1 _ o1 b223 b4870 b12 b4876 b5055 b5061 b4869 e5304 e5317 (by rfl) e5330
theorem e5332 : o1.mul b222 b6=b4857 := by decide
theorem e5333 : o1.mul b222 b7=b5067 := by decide
theorem e5334 : o1.mul b222 b8=b5068 := by decide
theorem e5335 : o1.mul b222 b9=b5069 := by decide
theorem e5336 : o1.mul b222 b10=b5070 := by decide
theorem e5337 : o1.mul b222 b11=b5071 := by decide
theorem e5338 : o1.scale b222 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5339 : o1.scale b222 b4475=b5077 := @scale_cons V1 _ o1 b222 b11 b5071 (List.nil : V2) (List.nil : V2) b5077 e5337 e5338 (by rfl)
theorem e5340 : o1.scale b222 b4473=b5076 := @scale_cons V1 _ o1 b222 b10 b5070 b4475 b5077 b5076 e5336 e5339 (by rfl)
theorem e5341 : o1.scale b222 b4471=b5075 := @scale_cons V1 _ o1 b222 b9 b5069 b4473 b5076 b5075 e5335 e5340 (by rfl)
theorem e5342 : o1.scale b222 b4469=b5074 := @scale_cons V1 _ o1 b222 b8 b5068 b4471 b5075 b5074 e5334 e5341 (by rfl)
theorem e5343 : o1.scale b222 b4467=b5073 := @scale_cons V1 _ o1 b222 b7 b5067 b4469 b5074 b5073 e5333 e5342 (by rfl)
theorem e5344 : o1.scale b222 b12=b5072 := @scale_cons V1 _ o1 b222 b6 b4857 b4467 b5073 b5072 e5332 e5343 (by rfl)
theorem e5345 : o1.add b4857 (List.nil : V1)=b4857 := by rfl
theorem e5346 : o1.add b5067 b4864=b4858 := by decide
theorem e5347 : o1.add b5068 b4865=b4859 := by decide
theorem e5348 : o1.add b5069 b4866=b4860 := by decide
theorem e5349 : o1.add b5070 b4867=b4861 := by decide
theorem e5350 : o1.add b5071 b4868=b4354 := by decide
theorem e5351 : o2.add (List.nil : V2) b5066=b5066 := by rfl
theorem e5352 : o2.add b5077 b5065=b5083 := @add_cons V1 _ o1 b5071 b4868 b4354 (List.nil : V2) b5066 b5066 b5083 e5350 e5351 (by rfl)
theorem e5353 : o2.add b5076 b5064=b5082 := @add_cons V1 _ o1 b5070 b4867 b4861 b5077 b5065 b5083 b5082 e5349 e5352 (by rfl)
theorem e5354 : o2.add b5075 b5063=b5081 := @add_cons V1 _ o1 b5069 b4866 b4860 b5076 b5064 b5082 b5081 e5348 e5353 (by rfl)
theorem e5355 : o2.add b5074 b5062=b5080 := @add_cons V1 _ o1 b5068 b4865 b4859 b5075 b5063 b5081 b5080 e5347 e5354 (by rfl)
theorem e5356 : o2.add b5073 b4869=b5079 := @add_cons V1 _ o1 b5067 b4864 b4858 b5074 b5062 b5080 b5079 e5346 e5355 (by rfl)
theorem e5357 : o2.add b5072 b5078=b4862 := @add_cons V1 _ o1 b4857 (List.nil : V1) b4857 b5073 b4869 b5079 b4862 e5345 e5356 (by rfl)
theorem e5358 : o2.mul b4856 b12=b4862 := @mul_cons V1 _ o1 b222 b4863 b12 b4869 b5072 b5078 b4862 e5331 e5344 (by rfl) e5357
theorem e5359 : o1.mul b221 b6=b4348 := by decide
theorem e5360 : o1.mul b221 b7=b5084 := by decide
theorem e5361 : o1.mul b221 b8=b5085 := by decide
theorem e5362 : o1.mul b221 b9=b5086 := by decide
theorem e5363 : o1.mul b221 b10=b5087 := by decide
theorem e5364 : o1.mul b221 b11=b5088 := by decide
theorem e5365 : o1.scale b221 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5366 : o1.scale b221 b4475=b5094 := @scale_cons V1 _ o1 b221 b11 b5088 (List.nil : V2) (List.nil : V2) b5094 e5364 e5365 (by rfl)
theorem e5367 : o1.scale b221 b4473=b5093 := @scale_cons V1 _ o1 b221 b10 b5087 b4475 b5094 b5093 e5363 e5366 (by rfl)
theorem e5368 : o1.scale b221 b4471=b5092 := @scale_cons V1 _ o1 b221 b9 b5086 b4473 b5093 b5092 e5362 e5367 (by rfl)
theorem e5369 : o1.scale b221 b4469=b5091 := @scale_cons V1 _ o1 b221 b8 b5085 b4471 b5092 b5091 e5361 e5368 (by rfl)
theorem e5370 : o1.scale b221 b4467=b5090 := @scale_cons V1 _ o1 b221 b7 b5084 b4469 b5091 b5090 e5360 e5369 (by rfl)
theorem e5371 : o1.scale b221 b12=b5089 := @scale_cons V1 _ o1 b221 b6 b4348 b4467 b5090 b5089 e5359 e5370 (by rfl)
theorem e5372 : o1.add b4348 (List.nil : V1)=b4348 := by rfl
theorem e5373 : o1.add b5084 b4857=b4349 := by decide
theorem e5374 : o1.add b5085 b4858=b4350 := by decide
theorem e5375 : o1.add b5086 b4859=b4351 := by decide
theorem e5376 : o1.add b5087 b4860=b4352 := by decide
theorem e5377 : o1.add b5088 b4861=b4353 := by decide
theorem e5378 : o2.add (List.nil : V2) b5083=b5083 := by rfl
theorem e5379 : o2.add b5094 b5082=b5100 := @add_cons V1 _ o1 b5088 b4861 b4353 (List.nil : V2) b5083 b5083 b5100 e5377 e5378 (by rfl)
theorem e5380 : o2.add b5093 b5081=b5099 := @add_cons V1 _ o1 b5087 b4860 b4352 b5094 b5082 b5100 b5099 e5376 e5379 (by rfl)
theorem e5381 : o2.add b5092 b5080=b5098 := @add_cons V1 _ o1 b5086 b4859 b4351 b5093 b5081 b5099 b5098 e5375 e5380 (by rfl)
theorem e5382 : o2.add b5091 b5079=b5097 := @add_cons V1 _ o1 b5085 b4858 b4350 b5092 b5080 b5098 b5097 e5374 e5381 (by rfl)
theorem e5383 : o2.add b5090 b4862=b5096 := @add_cons V1 _ o1 b5084 b4857 b4349 b5091 b5079 b5097 b5096 e5373 e5382 (by rfl)
theorem e5384 : o2.add b5089 b5095=b4364 := @add_cons V1 _ o1 b4348 (List.nil : V1) b4348 b5090 b4862 b5096 b4364 e5372 e5383 (by rfl)
theorem e5385 : o2.mul b232 b12=b4364 := @mul_cons V1 _ o1 b221 b4856 b12 b4862 b5089 b5095 b4364 e5358 e5371 (by rfl) e5384
theorem e5386 : o2.scale b232 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e5387 : o2.scale b232 b13=b4855 := @scale_cons V2 _ o2 b232 b12 b4364 (List.nil : V3) (List.nil : V3) b4855 e5385 e5386 (by rfl)
theorem e5388 : o2.add b4364 (List.nil : V2)=b4364 := by rfl
theorem e5389 : o3.add (List.nil : V3) b4399=b4399 := by rfl
theorem e5390 : o3.add b4855 b5101=b4397 := @add_cons V2 _ o2 b4364 (List.nil : V2) b4364 (List.nil : V3) b4399 b4399 b4397 e5388 e5389 (by rfl)
theorem e5391 : o3.mul b255 b13=b4397 := @mul_cons V2 _ o2 b232 b4398 b13 b4399 b4855 b5101 b4397 e5100 e5387 (by rfl) e5390
theorem e5392 : o3.mul (List.nil : V3) b70=(List.nil : V3) := by rfl
theorem e5393 : o2.mul (List.nil : V2) b63=(List.nil : V2) := by rfl
theorem e5394 : o1.mul b335 b62=b5412 := by decide
theorem e5395 : o1.scale b335 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5396 : o1.scale b335 b63=b5466 := @scale_cons V1 _ o1 b335 b62 b5412 (List.nil : V2) (List.nil : V2) b5466 e5394 e5395 (by rfl)
theorem e5397 : o2.add b5466 (List.nil : V2)=b5466 := by rfl
theorem e5398 : o2.mul b5465 b63=b5466 := @mul_cons V1 _ o1 b335 (List.nil : V2) b63 (List.nil : V2) b5466 (List.nil : V2) b5466 e5393 e5396 (by rfl) e5397
theorem e5399 : o1.mul b334 b62=b5411 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
