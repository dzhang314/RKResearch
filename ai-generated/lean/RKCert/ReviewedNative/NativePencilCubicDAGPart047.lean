module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart046

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6900 : o1.add b6105 b5346=b5318 := by decide
theorem e6901 : o1.add b6106 b5347=b5319 := by decide
theorem e6902 : o1.add b6107 b5348=b5320 := by decide
theorem e6903 : o2.add b6232 b6050=b6329 := @add_cons V1 _ o1 b6107 b5348 b5320 (List.nil : V2) (List.nil : V2) (List.nil : V2) b6329 e6902 e2341 (by rfl)
theorem e6904 : o2.add b6231 b6049=b6328 := @add_cons V1 _ o1 b6106 b5347 b5319 b6232 b6050 b6329 b6328 e6901 e6903 (by rfl)
theorem e6905 : o2.add b6230 b6048=b6327 := @add_cons V1 _ o1 b6105 b5346 b5318 b6231 b6049 b6328 b6327 e6900 e6904 (by rfl)
theorem e6906 : o2.add b6229 b6047=b6326 := @add_cons V1 _ o1 b6104 b5345 b5317 b6230 b6048 b6327 b6326 e6899 e6905 (by rfl)
theorem e6907 : o2.add b6228 b6046=b6325 := @add_cons V1 _ o1 b6103 b5344 b5316 b6229 b6047 b6326 b6325 e6898 e6906 (by rfl)
theorem e6908 : o2.add b6227 b6045=b6324 := @add_cons V1 _ o1 b6102 b5343 b5315 b6228 b6046 b6325 b6324 e6897 e6907 (by rfl)
theorem e6909 : o2.add b6226 b6044=b6323 := @add_cons V1 _ o1 b6101 b5342 b5314 b6227 b6045 b6324 b6323 e6896 e6908 (by rfl)
theorem e6910 : o2.add b6225 b6043=b6322 := @add_cons V1 _ o1 b6100 b5341 b5313 b6226 b6044 b6323 b6322 e6895 e6909 (by rfl)
theorem e6911 : o2.add b6224 b6042=b6321 := @add_cons V1 _ o1 b6099 b5340 b5312 b6225 b6043 b6322 b6321 e6894 e6910 (by rfl)
theorem e6912 : o2.add b6223 b6041=b6320 := @add_cons V1 _ o1 b6098 b5339 b5311 b6224 b6042 b6321 b6320 e6893 e6911 (by rfl)
theorem e6913 : o2.add b6222 b6040=b6319 := @add_cons V1 _ o1 b6097 b5338 b5310 b6223 b6041 b6320 b6319 e6892 e6912 (by rfl)
theorem e6914 : o2.add b6221 b6039=b6318 := @add_cons V1 _ o1 b6096 b5337 b5309 b6222 b6040 b6319 b6318 e6891 e6913 (by rfl)
theorem e6915 : o2.add b6220 b6038=b6317 := @add_cons V1 _ o1 b5308 (List.nil : V1) b5308 b6221 b6039 b6318 b6317 e6765 e6914 (by rfl)
theorem e6916 : o2.add b6219 b6037=b6316 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6220 b6038 b6317 b6316 e34 e6915 (by rfl)
theorem e6917 : o2.add b6218 b6036=b6315 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6219 b6037 b6316 b6315 e34 e6916 (by rfl)
theorem e6918 : o2.add b6108 b5349=b5321 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6218 b6036 b6315 b5321 e34 e6917 (by rfl)
theorem e6919 : o1.add b6109 b5350=b5182 := by decide
theorem e6920 : o1.add b6110 b5351=b5183 := by decide
theorem e6921 : o1.add b6111 b5352=b5184 := by decide
theorem e6922 : o1.add b6112 b5353=b5185 := by decide
theorem e6923 : o1.add b6113 b5354=b5186 := by decide
theorem e6924 : o1.add b6114 b5355=b5187 := by decide
theorem e6925 : o1.add b6115 b5356=b5188 := by decide
theorem e6926 : o1.add b6116 b5357=b5189 := by decide
theorem e6927 : o1.add b6117 b5358=b5190 := by decide
theorem e6928 : o1.add b6118 b5359=b5191 := by decide
theorem e6929 : o1.add b6119 b5360=b5192 := by decide
theorem e6930 : o1.add b6120 b5361=b5193 := by decide
theorem e6931 : o2.add b6272 b6066=b6345 := @add_cons V1 _ o1 b6120 b5361 b5193 (List.nil : V2) (List.nil : V2) (List.nil : V2) b6345 e6930 e2341 (by rfl)
theorem e6932 : o2.add b6271 b6065=b6344 := @add_cons V1 _ o1 b6119 b5360 b5192 b6272 b6066 b6345 b6344 e6929 e6931 (by rfl)
theorem e6933 : o2.add b6270 b6064=b6343 := @add_cons V1 _ o1 b6118 b5359 b5191 b6271 b6065 b6344 b6343 e6928 e6932 (by rfl)
theorem e6934 : o2.add b6269 b6063=b6342 := @add_cons V1 _ o1 b6117 b5358 b5190 b6270 b6064 b6343 b6342 e6927 e6933 (by rfl)
theorem e6935 : o2.add b6268 b6062=b6341 := @add_cons V1 _ o1 b6116 b5357 b5189 b6269 b6063 b6342 b6341 e6926 e6934 (by rfl)
theorem e6936 : o2.add b6267 b6061=b6340 := @add_cons V1 _ o1 b6115 b5356 b5188 b6268 b6062 b6341 b6340 e6925 e6935 (by rfl)
theorem e6937 : o2.add b6266 b6060=b6339 := @add_cons V1 _ o1 b6114 b5355 b5187 b6267 b6061 b6340 b6339 e6924 e6936 (by rfl)
theorem e6938 : o2.add b6265 b6059=b6338 := @add_cons V1 _ o1 b6113 b5354 b5186 b6266 b6060 b6339 b6338 e6923 e6937 (by rfl)
theorem e6939 : o2.add b6264 b6058=b6337 := @add_cons V1 _ o1 b6112 b5353 b5185 b6265 b6059 b6338 b6337 e6922 e6938 (by rfl)
theorem e6940 : o2.add b6263 b6057=b6336 := @add_cons V1 _ o1 b6111 b5352 b5184 b6264 b6058 b6337 b6336 e6921 e6939 (by rfl)
theorem e6941 : o2.add b6262 b6056=b6335 := @add_cons V1 _ o1 b6110 b5351 b5183 b6263 b6057 b6336 b6335 e6920 e6940 (by rfl)
theorem e6942 : o2.add b6261 b6055=b6334 := @add_cons V1 _ o1 b6109 b5350 b5182 b6262 b6056 b6335 b6334 e6919 e6941 (by rfl)
theorem e6943 : o2.add b6260 b6054=b6333 := @add_cons V1 _ o1 b5181 (List.nil : V1) b5181 b6261 b6055 b6334 b6333 e6847 e6942 (by rfl)
theorem e6944 : o2.add b6259 b6053=b6332 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6260 b6054 b6333 b6332 e34 e6943 (by rfl)
theorem e6945 : o2.add b6258 b6052=b6331 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6259 b6053 b6332 b6331 e34 e6944 (by rfl)
theorem e6946 : o2.add b6121 b5362=b5194 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b6258 b6052 b6331 b5194 e34 e6945 (by rfl)
theorem e6947 : o3.add (List.nil : V3) b6067=b6067 := by rfl
theorem e6948 : o3.add b6257 b6051=b6330 := @add_cons V2 _ o2 b6121 b5362 b5194 (List.nil : V3) b6067 b6067 b6330 e6946 e6947 (by rfl)
theorem e6949 : o3.add b6217 b6035=b6314 := @add_cons V2 _ o2 b6108 b5349 b5321 b6257 b6051 b6330 b6314 e6918 e6948 (by rfl)
theorem e6950 : o3.add b6177 b5363=b6298 := @add_cons V2 _ o2 b6095 b5336 b5307 b6217 b6035 b6314 b6298 e6890 e6949 (by rfl)
theorem e6951 : o3.add b6122 b6297=b5322 := @add_cons V2 _ o2 b5293 (List.nil : V2) b5293 b6177 b5363 b6298 b5322 e6862 e6950 (by rfl)
theorem e6952 : o3.mul b5279 b70=b5322 := @mul_cons V2 _ o2 b300 b5323 b70 b5363 b6122 b6297 b5322 e6515 e6861 (by rfl) e6951
theorem e6953 : o1.mul b285 b62=b5246 := by decide
theorem e6954 : o1.scale b285 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6955 : o1.scale b285 b63=b6418 := @scale_cons V1 _ o1 b285 b62 b5246 (List.nil : V2) (List.nil : V2) b6418 e6953 e6954 (by rfl)
theorem e6956 : o2.add b6418 (List.nil : V2)=b6418 := by rfl
theorem e6957 : o2.mul b6417 b63=b6418 := @mul_cons V1 _ o1 b285 (List.nil : V2) b63 (List.nil : V2) b6418 (List.nil : V2) b6418 e5393 e6955 (by rfl) e6956
theorem e6958 : o1.mul b284 b62=b5245 := by decide
theorem e6959 : o1.scale b284 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6960 : o1.scale b284 b63=b6419 := @scale_cons V1 _ o1 b284 b62 b5245 (List.nil : V2) (List.nil : V2) b6419 e6958 e6959 (by rfl)
theorem e6961 : o1.add b5245 (List.nil : V1)=b5245 := by rfl
theorem e6962 : o2.add (List.nil : V2) b6418=b6418 := by rfl
theorem e6963 : o2.add b6419 b6420=b6416 := @add_cons V1 _ o1 b5245 (List.nil : V1) b5245 (List.nil : V2) b6418 b6418 b6416 e6961 e6962 (by rfl)
theorem e6964 : o2.mul b6415 b63=b6416 := @mul_cons V1 _ o1 b284 b6417 b63 b6418 b6419 b6420 b6416 e6957 e6960 (by rfl) e6963
theorem e6965 : o1.mul b283 b62=b5244 := by decide
theorem e6966 : o1.scale b283 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6967 : o1.scale b283 b63=b6421 := @scale_cons V1 _ o1 b283 b62 b5244 (List.nil : V2) (List.nil : V2) b6421 e6965 e6966 (by rfl)
theorem e6968 : o1.add b5244 (List.nil : V1)=b5244 := by rfl
theorem e6969 : o2.add (List.nil : V2) b6416=b6416 := by rfl
theorem e6970 : o2.add b6421 b6422=b6414 := @add_cons V1 _ o1 b5244 (List.nil : V1) b5244 (List.nil : V2) b6416 b6416 b6414 e6968 e6969 (by rfl)
theorem e6971 : o2.mul b6413 b63=b6414 := @mul_cons V1 _ o1 b283 b6415 b63 b6416 b6421 b6422 b6414 e6964 e6967 (by rfl) e6970
theorem e6972 : o1.mul b282 b62=b5243 := by decide
theorem e6973 : o1.scale b282 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6974 : o1.scale b282 b63=b6423 := @scale_cons V1 _ o1 b282 b62 b5243 (List.nil : V2) (List.nil : V2) b6423 e6972 e6973 (by rfl)
theorem e6975 : o1.add b5243 (List.nil : V1)=b5243 := by rfl
theorem e6976 : o2.add (List.nil : V2) b6414=b6414 := by rfl
theorem e6977 : o2.add b6423 b6424=b6412 := @add_cons V1 _ o1 b5243 (List.nil : V1) b5243 (List.nil : V2) b6414 b6414 b6412 e6975 e6976 (by rfl)
theorem e6978 : o2.mul b6411 b63=b6412 := @mul_cons V1 _ o1 b282 b6413 b63 b6414 b6423 b6424 b6412 e6971 e6974 (by rfl) e6977
theorem e6979 : o1.mul b281 b62=b5242 := by decide
theorem e6980 : o1.scale b281 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6981 : o1.scale b281 b63=b6425 := @scale_cons V1 _ o1 b281 b62 b5242 (List.nil : V2) (List.nil : V2) b6425 e6979 e6980 (by rfl)
theorem e6982 : o1.add b5242 (List.nil : V1)=b5242 := by rfl
theorem e6983 : o2.add (List.nil : V2) b6412=b6412 := by rfl
theorem e6984 : o2.add b6425 b6426=b6410 := @add_cons V1 _ o1 b5242 (List.nil : V1) b5242 (List.nil : V2) b6412 b6412 b6410 e6982 e6983 (by rfl)
theorem e6985 : o2.mul b6409 b63=b6410 := @mul_cons V1 _ o1 b281 b6411 b63 b6412 b6425 b6426 b6410 e6978 e6981 (by rfl) e6984
theorem e6986 : o1.mul b280 b62=b5241 := by decide
theorem e6987 : o1.scale b280 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6988 : o1.scale b280 b63=b6427 := @scale_cons V1 _ o1 b280 b62 b5241 (List.nil : V2) (List.nil : V2) b6427 e6986 e6987 (by rfl)
theorem e6989 : o1.add b5241 (List.nil : V1)=b5241 := by rfl
theorem e6990 : o2.add (List.nil : V2) b6410=b6410 := by rfl
theorem e6991 : o2.add b6427 b6428=b6408 := @add_cons V1 _ o1 b5241 (List.nil : V1) b5241 (List.nil : V2) b6410 b6410 b6408 e6989 e6990 (by rfl)
theorem e6992 : o2.mul b6407 b63=b6408 := @mul_cons V1 _ o1 b280 b6409 b63 b6410 b6427 b6428 b6408 e6985 e6988 (by rfl) e6991
theorem e6993 : o1.mul b279 b62=b5240 := by decide
theorem e6994 : o1.scale b279 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6995 : o1.scale b279 b63=b6429 := @scale_cons V1 _ o1 b279 b62 b5240 (List.nil : V2) (List.nil : V2) b6429 e6993 e6994 (by rfl)
theorem e6996 : o1.add b5240 (List.nil : V1)=b5240 := by rfl
theorem e6997 : o2.add (List.nil : V2) b6408=b6408 := by rfl
theorem e6998 : o2.add b6429 b6430=b6406 := @add_cons V1 _ o1 b5240 (List.nil : V1) b5240 (List.nil : V2) b6408 b6408 b6406 e6996 e6997 (by rfl)
theorem e6999 : o2.mul b6405 b63=b6406 := @mul_cons V1 _ o1 b279 b6407 b63 b6408 b6429 b6430 b6406 e6992 e6995 (by rfl) e6998
theorem e7000 : o1.mul b278 b62=b5239 := by decide
theorem e7001 : o1.scale b278 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7002 : o1.scale b278 b63=b6431 := @scale_cons V1 _ o1 b278 b62 b5239 (List.nil : V2) (List.nil : V2) b6431 e7000 e7001 (by rfl)
theorem e7003 : o1.add b5239 (List.nil : V1)=b5239 := by rfl
theorem e7004 : o2.add (List.nil : V2) b6406=b6406 := by rfl
theorem e7005 : o2.add b6431 b6432=b6404 := @add_cons V1 _ o1 b5239 (List.nil : V1) b5239 (List.nil : V2) b6406 b6406 b6404 e7003 e7004 (by rfl)
theorem e7006 : o2.mul b6403 b63=b6404 := @mul_cons V1 _ o1 b278 b6405 b63 b6406 b6431 b6432 b6404 e6999 e7002 (by rfl) e7005
theorem e7007 : o1.mul b277 b62=b5238 := by decide
theorem e7008 : o1.scale b277 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7009 : o1.scale b277 b63=b6433 := @scale_cons V1 _ o1 b277 b62 b5238 (List.nil : V2) (List.nil : V2) b6433 e7007 e7008 (by rfl)
theorem e7010 : o1.add b5238 (List.nil : V1)=b5238 := by rfl
theorem e7011 : o2.add (List.nil : V2) b6404=b6404 := by rfl
theorem e7012 : o2.add b6433 b6434=b6402 := @add_cons V1 _ o1 b5238 (List.nil : V1) b5238 (List.nil : V2) b6404 b6404 b6402 e7010 e7011 (by rfl)
theorem e7013 : o2.mul b6401 b63=b6402 := @mul_cons V1 _ o1 b277 b6403 b63 b6404 b6433 b6434 b6402 e7006 e7009 (by rfl) e7012
theorem e7014 : o1.mul b276 b62=b5237 := by decide
theorem e7015 : o1.scale b276 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7016 : o1.scale b276 b63=b6435 := @scale_cons V1 _ o1 b276 b62 b5237 (List.nil : V2) (List.nil : V2) b6435 e7014 e7015 (by rfl)
theorem e7017 : o1.add b5237 (List.nil : V1)=b5237 := by rfl
theorem e7018 : o2.add (List.nil : V2) b6402=b6402 := by rfl
theorem e7019 : o2.add b6435 b6436=b6400 := @add_cons V1 _ o1 b5237 (List.nil : V1) b5237 (List.nil : V2) b6402 b6402 b6400 e7017 e7018 (by rfl)
theorem e7020 : o2.mul b6399 b63=b6400 := @mul_cons V1 _ o1 b276 b6401 b63 b6402 b6435 b6436 b6400 e7013 e7016 (by rfl) e7019
theorem e7021 : o1.mul b275 b62=b5236 := by decide
theorem e7022 : o1.scale b275 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7023 : o1.scale b275 b63=b6437 := @scale_cons V1 _ o1 b275 b62 b5236 (List.nil : V2) (List.nil : V2) b6437 e7021 e7022 (by rfl)
theorem e7024 : o1.add b5236 (List.nil : V1)=b5236 := by rfl
theorem e7025 : o2.add (List.nil : V2) b6400=b6400 := by rfl
theorem e7026 : o2.add b6437 b6438=b6398 := @add_cons V1 _ o1 b5236 (List.nil : V1) b5236 (List.nil : V2) b6400 b6400 b6398 e7024 e7025 (by rfl)
theorem e7027 : o2.mul b6397 b63=b6398 := @mul_cons V1 _ o1 b275 b6399 b63 b6400 b6437 b6438 b6398 e7020 e7023 (by rfl) e7026
theorem e7028 : o1.mul b274 b62=b5235 := by decide
theorem e7029 : o1.scale b274 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7030 : o1.scale b274 b63=b6439 := @scale_cons V1 _ o1 b274 b62 b5235 (List.nil : V2) (List.nil : V2) b6439 e7028 e7029 (by rfl)
theorem e7031 : o1.add b5235 (List.nil : V1)=b5235 := by rfl
theorem e7032 : o2.add (List.nil : V2) b6398=b6398 := by rfl
theorem e7033 : o2.add b6439 b6440=b6396 := @add_cons V1 _ o1 b5235 (List.nil : V1) b5235 (List.nil : V2) b6398 b6398 b6396 e7031 e7032 (by rfl)
theorem e7034 : o2.mul b6395 b63=b6396 := @mul_cons V1 _ o1 b274 b6397 b63 b6398 b6439 b6440 b6396 e7027 e7030 (by rfl) e7033
theorem e7035 : o1.mul b273 b62=b5234 := by decide
theorem e7036 : o1.scale b273 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7037 : o1.scale b273 b63=b6441 := @scale_cons V1 _ o1 b273 b62 b5234 (List.nil : V2) (List.nil : V2) b6441 e7035 e7036 (by rfl)
theorem e7038 : o1.add b5234 (List.nil : V1)=b5234 := by rfl
theorem e7039 : o2.add (List.nil : V2) b6396=b6396 := by rfl
theorem e7040 : o2.add b6441 b6442=b6394 := @add_cons V1 _ o1 b5234 (List.nil : V1) b5234 (List.nil : V2) b6396 b6396 b6394 e7038 e7039 (by rfl)
theorem e7041 : o2.mul b6393 b63=b6394 := @mul_cons V1 _ o1 b273 b6395 b63 b6396 b6441 b6442 b6394 e7034 e7037 (by rfl) e7040
theorem e7042 : o1.mul b272 b62=b5233 := by decide
theorem e7043 : o1.scale b272 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7044 : o1.scale b272 b63=b6443 := @scale_cons V1 _ o1 b272 b62 b5233 (List.nil : V2) (List.nil : V2) b6443 e7042 e7043 (by rfl)
theorem e7045 : o1.add b5233 (List.nil : V1)=b5233 := by rfl
theorem e7046 : o2.add (List.nil : V2) b6394=b6394 := by rfl
theorem e7047 : o2.add b6443 b6444=b6392 := @add_cons V1 _ o1 b5233 (List.nil : V1) b5233 (List.nil : V2) b6394 b6394 b6392 e7045 e7046 (by rfl)
theorem e7048 : o2.mul b6391 b63=b6392 := @mul_cons V1 _ o1 b272 b6393 b63 b6394 b6443 b6444 b6392 e7041 e7044 (by rfl) e7047
theorem e7049 : o2.add (List.nil : V2) b6390=b6390 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
