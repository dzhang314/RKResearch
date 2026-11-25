module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart047

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e7050 : o2.mul b6389 b63=b6390 := @mul_cons V1 _ o1 (List.nil : V1) b6391 b63 b6392 (List.nil : V2) b6390 b6390 e7048 e5463 (by rfl) e7049
theorem e7051 : o2.add (List.nil : V2) b5247=b5247 := by rfl
theorem e7052 : o2.mul b286 b63=b5247 := @mul_cons V1 _ o1 (List.nil : V1) b6389 b63 b6390 (List.nil : V2) b5247 b5247 e7050 e5463 (by rfl) e7051
theorem e7053 : o1.mul b285 b64=b6358 := by decide
theorem e7054 : o1.scale b285 b65=b6460 := @scale_cons V1 _ o1 b285 b64 b6358 (List.nil : V2) (List.nil : V2) b6460 e7053 e6954 (by rfl)
theorem e7055 : o2.add b6460 (List.nil : V2)=b6460 := by rfl
theorem e7056 : o2.mul b6417 b65=b6460 := @mul_cons V1 _ o1 b285 (List.nil : V2) b65 (List.nil : V2) b6460 (List.nil : V2) b6460 e5476 e7054 (by rfl) e7055
theorem e7057 : o1.mul b284 b64=b6357 := by decide
theorem e7058 : o1.scale b284 b65=b6461 := @scale_cons V1 _ o1 b284 b64 b6357 (List.nil : V2) (List.nil : V2) b6461 e7057 e6959 (by rfl)
theorem e7059 : o1.add b6357 (List.nil : V1)=b6357 := by rfl
theorem e7060 : o2.add (List.nil : V2) b6460=b6460 := by rfl
theorem e7061 : o2.add b6461 b6462=b6459 := @add_cons V1 _ o1 b6357 (List.nil : V1) b6357 (List.nil : V2) b6460 b6460 b6459 e7059 e7060 (by rfl)
theorem e7062 : o2.mul b6415 b65=b6459 := @mul_cons V1 _ o1 b284 b6417 b65 b6460 b6461 b6462 b6459 e7056 e7058 (by rfl) e7061
theorem e7063 : o1.mul b283 b64=b6356 := by decide
theorem e7064 : o1.scale b283 b65=b6463 := @scale_cons V1 _ o1 b283 b64 b6356 (List.nil : V2) (List.nil : V2) b6463 e7063 e6966 (by rfl)
theorem e7065 : o1.add b6356 (List.nil : V1)=b6356 := by rfl
theorem e7066 : o2.add (List.nil : V2) b6459=b6459 := by rfl
theorem e7067 : o2.add b6463 b6464=b6458 := @add_cons V1 _ o1 b6356 (List.nil : V1) b6356 (List.nil : V2) b6459 b6459 b6458 e7065 e7066 (by rfl)
theorem e7068 : o2.mul b6413 b65=b6458 := @mul_cons V1 _ o1 b283 b6415 b65 b6459 b6463 b6464 b6458 e7062 e7064 (by rfl) e7067
theorem e7069 : o1.mul b282 b64=b6355 := by decide
theorem e7070 : o1.scale b282 b65=b6465 := @scale_cons V1 _ o1 b282 b64 b6355 (List.nil : V2) (List.nil : V2) b6465 e7069 e6973 (by rfl)
theorem e7071 : o1.add b6355 (List.nil : V1)=b6355 := by rfl
theorem e7072 : o2.add (List.nil : V2) b6458=b6458 := by rfl
theorem e7073 : o2.add b6465 b6466=b6457 := @add_cons V1 _ o1 b6355 (List.nil : V1) b6355 (List.nil : V2) b6458 b6458 b6457 e7071 e7072 (by rfl)
theorem e7074 : o2.mul b6411 b65=b6457 := @mul_cons V1 _ o1 b282 b6413 b65 b6458 b6465 b6466 b6457 e7068 e7070 (by rfl) e7073
theorem e7075 : o1.mul b281 b64=b6354 := by decide
theorem e7076 : o1.scale b281 b65=b6467 := @scale_cons V1 _ o1 b281 b64 b6354 (List.nil : V2) (List.nil : V2) b6467 e7075 e6980 (by rfl)
theorem e7077 : o1.add b6354 (List.nil : V1)=b6354 := by rfl
theorem e7078 : o2.add (List.nil : V2) b6457=b6457 := by rfl
theorem e7079 : o2.add b6467 b6468=b6456 := @add_cons V1 _ o1 b6354 (List.nil : V1) b6354 (List.nil : V2) b6457 b6457 b6456 e7077 e7078 (by rfl)
theorem e7080 : o2.mul b6409 b65=b6456 := @mul_cons V1 _ o1 b281 b6411 b65 b6457 b6467 b6468 b6456 e7074 e7076 (by rfl) e7079
theorem e7081 : o1.mul b280 b64=b6353 := by decide
theorem e7082 : o1.scale b280 b65=b6469 := @scale_cons V1 _ o1 b280 b64 b6353 (List.nil : V2) (List.nil : V2) b6469 e7081 e6987 (by rfl)
theorem e7083 : o1.add b6353 (List.nil : V1)=b6353 := by rfl
theorem e7084 : o2.add (List.nil : V2) b6456=b6456 := by rfl
theorem e7085 : o2.add b6469 b6470=b6455 := @add_cons V1 _ o1 b6353 (List.nil : V1) b6353 (List.nil : V2) b6456 b6456 b6455 e7083 e7084 (by rfl)
theorem e7086 : o2.mul b6407 b65=b6455 := @mul_cons V1 _ o1 b280 b6409 b65 b6456 b6469 b6470 b6455 e7080 e7082 (by rfl) e7085
theorem e7087 : o1.mul b279 b64=b6352 := by decide
theorem e7088 : o1.scale b279 b65=b6471 := @scale_cons V1 _ o1 b279 b64 b6352 (List.nil : V2) (List.nil : V2) b6471 e7087 e6994 (by rfl)
theorem e7089 : o1.add b6352 (List.nil : V1)=b6352 := by rfl
theorem e7090 : o2.add (List.nil : V2) b6455=b6455 := by rfl
theorem e7091 : o2.add b6471 b6472=b6454 := @add_cons V1 _ o1 b6352 (List.nil : V1) b6352 (List.nil : V2) b6455 b6455 b6454 e7089 e7090 (by rfl)
theorem e7092 : o2.mul b6405 b65=b6454 := @mul_cons V1 _ o1 b279 b6407 b65 b6455 b6471 b6472 b6454 e7086 e7088 (by rfl) e7091
theorem e7093 : o1.mul b278 b64=b6351 := by decide
theorem e7094 : o1.scale b278 b65=b6473 := @scale_cons V1 _ o1 b278 b64 b6351 (List.nil : V2) (List.nil : V2) b6473 e7093 e7001 (by rfl)
theorem e7095 : o1.add b6351 (List.nil : V1)=b6351 := by rfl
theorem e7096 : o2.add (List.nil : V2) b6454=b6454 := by rfl
theorem e7097 : o2.add b6473 b6474=b6453 := @add_cons V1 _ o1 b6351 (List.nil : V1) b6351 (List.nil : V2) b6454 b6454 b6453 e7095 e7096 (by rfl)
theorem e7098 : o2.mul b6403 b65=b6453 := @mul_cons V1 _ o1 b278 b6405 b65 b6454 b6473 b6474 b6453 e7092 e7094 (by rfl) e7097
theorem e7099 : o1.mul b277 b64=b6350 := by decide
theorem e7100 : o1.scale b277 b65=b6475 := @scale_cons V1 _ o1 b277 b64 b6350 (List.nil : V2) (List.nil : V2) b6475 e7099 e7008 (by rfl)
theorem e7101 : o1.add b6350 (List.nil : V1)=b6350 := by rfl
theorem e7102 : o2.add (List.nil : V2) b6453=b6453 := by rfl
theorem e7103 : o2.add b6475 b6476=b6452 := @add_cons V1 _ o1 b6350 (List.nil : V1) b6350 (List.nil : V2) b6453 b6453 b6452 e7101 e7102 (by rfl)
theorem e7104 : o2.mul b6401 b65=b6452 := @mul_cons V1 _ o1 b277 b6403 b65 b6453 b6475 b6476 b6452 e7098 e7100 (by rfl) e7103
theorem e7105 : o1.mul b276 b64=b6349 := by decide
theorem e7106 : o1.scale b276 b65=b6477 := @scale_cons V1 _ o1 b276 b64 b6349 (List.nil : V2) (List.nil : V2) b6477 e7105 e7015 (by rfl)
theorem e7107 : o1.add b6349 (List.nil : V1)=b6349 := by rfl
theorem e7108 : o2.add (List.nil : V2) b6452=b6452 := by rfl
theorem e7109 : o2.add b6477 b6478=b6451 := @add_cons V1 _ o1 b6349 (List.nil : V1) b6349 (List.nil : V2) b6452 b6452 b6451 e7107 e7108 (by rfl)
theorem e7110 : o2.mul b6399 b65=b6451 := @mul_cons V1 _ o1 b276 b6401 b65 b6452 b6477 b6478 b6451 e7104 e7106 (by rfl) e7109
theorem e7111 : o1.mul b275 b64=b6348 := by decide
theorem e7112 : o1.scale b275 b65=b6479 := @scale_cons V1 _ o1 b275 b64 b6348 (List.nil : V2) (List.nil : V2) b6479 e7111 e7022 (by rfl)
theorem e7113 : o1.add b6348 (List.nil : V1)=b6348 := by rfl
theorem e7114 : o2.add (List.nil : V2) b6451=b6451 := by rfl
theorem e7115 : o2.add b6479 b6480=b6450 := @add_cons V1 _ o1 b6348 (List.nil : V1) b6348 (List.nil : V2) b6451 b6451 b6450 e7113 e7114 (by rfl)
theorem e7116 : o2.mul b6397 b65=b6450 := @mul_cons V1 _ o1 b275 b6399 b65 b6451 b6479 b6480 b6450 e7110 e7112 (by rfl) e7115
theorem e7117 : o1.mul b274 b64=b6347 := by decide
theorem e7118 : o1.scale b274 b65=b6481 := @scale_cons V1 _ o1 b274 b64 b6347 (List.nil : V2) (List.nil : V2) b6481 e7117 e7029 (by rfl)
theorem e7119 : o1.add b6347 (List.nil : V1)=b6347 := by rfl
theorem e7120 : o2.add (List.nil : V2) b6450=b6450 := by rfl
theorem e7121 : o2.add b6481 b6482=b6449 := @add_cons V1 _ o1 b6347 (List.nil : V1) b6347 (List.nil : V2) b6450 b6450 b6449 e7119 e7120 (by rfl)
theorem e7122 : o2.mul b6395 b65=b6449 := @mul_cons V1 _ o1 b274 b6397 b65 b6450 b6481 b6482 b6449 e7116 e7118 (by rfl) e7121
theorem e7123 : o1.mul b273 b64=b6346 := by decide
theorem e7124 : o1.scale b273 b65=b6483 := @scale_cons V1 _ o1 b273 b64 b6346 (List.nil : V2) (List.nil : V2) b6483 e7123 e7036 (by rfl)
theorem e7125 : o1.add b6346 (List.nil : V1)=b6346 := by rfl
theorem e7126 : o2.add (List.nil : V2) b6449=b6449 := by rfl
theorem e7127 : o2.add b6483 b6484=b6448 := @add_cons V1 _ o1 b6346 (List.nil : V1) b6346 (List.nil : V2) b6449 b6449 b6448 e7125 e7126 (by rfl)
theorem e7128 : o2.mul b6393 b65=b6448 := @mul_cons V1 _ o1 b273 b6395 b65 b6449 b6483 b6484 b6448 e7122 e7124 (by rfl) e7127
theorem e7129 : o1.mul b272 b64=b5248 := by decide
theorem e7130 : o1.scale b272 b65=b6485 := @scale_cons V1 _ o1 b272 b64 b5248 (List.nil : V2) (List.nil : V2) b6485 e7129 e7043 (by rfl)
theorem e7131 : o1.add b5248 (List.nil : V1)=b5248 := by rfl
theorem e7132 : o2.add (List.nil : V2) b6448=b6448 := by rfl
theorem e7133 : o2.add b6485 b6486=b6447 := @add_cons V1 _ o1 b5248 (List.nil : V1) b5248 (List.nil : V2) b6448 b6448 b6447 e7131 e7132 (by rfl)
theorem e7134 : o2.mul b6391 b65=b6447 := @mul_cons V1 _ o1 b272 b6393 b65 b6448 b6485 b6486 b6447 e7128 e7130 (by rfl) e7133
theorem e7135 : o2.add (List.nil : V2) b6446=b6446 := by rfl
theorem e7136 : o2.mul b6389 b65=b6446 := @mul_cons V1 _ o1 (List.nil : V1) b6391 b65 b6447 (List.nil : V2) b6446 b6446 e7134 e5536 (by rfl) e7135
theorem e7137 : o2.add (List.nil : V2) b6359=b6359 := by rfl
theorem e7138 : o2.mul b286 b65=b6359 := @mul_cons V1 _ o1 (List.nil : V1) b6389 b65 b6446 (List.nil : V2) b6359 b6359 e7136 e5536 (by rfl) e7137
theorem e7139 : o1.mul b285 b66=b6372 := by decide
theorem e7140 : o1.scale b285 b67=b6502 := @scale_cons V1 _ o1 b285 b66 b6372 (List.nil : V2) (List.nil : V2) b6502 e7139 e6954 (by rfl)
theorem e7141 : o2.add b6502 (List.nil : V2)=b6502 := by rfl
theorem e7142 : o2.mul b6417 b67=b6502 := @mul_cons V1 _ o1 b285 (List.nil : V2) b67 (List.nil : V2) b6502 (List.nil : V2) b6502 e5549 e7140 (by rfl) e7141
theorem e7143 : o1.mul b284 b66=b6371 := by decide
theorem e7144 : o1.scale b284 b67=b6503 := @scale_cons V1 _ o1 b284 b66 b6371 (List.nil : V2) (List.nil : V2) b6503 e7143 e6959 (by rfl)
theorem e7145 : o1.add b6371 (List.nil : V1)=b6371 := by rfl
theorem e7146 : o2.add (List.nil : V2) b6502=b6502 := by rfl
theorem e7147 : o2.add b6503 b6504=b6501 := @add_cons V1 _ o1 b6371 (List.nil : V1) b6371 (List.nil : V2) b6502 b6502 b6501 e7145 e7146 (by rfl)
theorem e7148 : o2.mul b6415 b67=b6501 := @mul_cons V1 _ o1 b284 b6417 b67 b6502 b6503 b6504 b6501 e7142 e7144 (by rfl) e7147
theorem e7149 : o1.mul b283 b66=b6370 := by decide
theorem e7150 : o1.scale b283 b67=b6505 := @scale_cons V1 _ o1 b283 b66 b6370 (List.nil : V2) (List.nil : V2) b6505 e7149 e6966 (by rfl)
theorem e7151 : o1.add b6370 (List.nil : V1)=b6370 := by rfl
theorem e7152 : o2.add (List.nil : V2) b6501=b6501 := by rfl
theorem e7153 : o2.add b6505 b6506=b6500 := @add_cons V1 _ o1 b6370 (List.nil : V1) b6370 (List.nil : V2) b6501 b6501 b6500 e7151 e7152 (by rfl)
theorem e7154 : o2.mul b6413 b67=b6500 := @mul_cons V1 _ o1 b283 b6415 b67 b6501 b6505 b6506 b6500 e7148 e7150 (by rfl) e7153
theorem e7155 : o1.mul b282 b66=b6369 := by decide
theorem e7156 : o1.scale b282 b67=b6507 := @scale_cons V1 _ o1 b282 b66 b6369 (List.nil : V2) (List.nil : V2) b6507 e7155 e6973 (by rfl)
theorem e7157 : o1.add b6369 (List.nil : V1)=b6369 := by rfl
theorem e7158 : o2.add (List.nil : V2) b6500=b6500 := by rfl
theorem e7159 : o2.add b6507 b6508=b6499 := @add_cons V1 _ o1 b6369 (List.nil : V1) b6369 (List.nil : V2) b6500 b6500 b6499 e7157 e7158 (by rfl)
theorem e7160 : o2.mul b6411 b67=b6499 := @mul_cons V1 _ o1 b282 b6413 b67 b6500 b6507 b6508 b6499 e7154 e7156 (by rfl) e7159
theorem e7161 : o1.mul b281 b66=b6368 := by decide
theorem e7162 : o1.scale b281 b67=b6509 := @scale_cons V1 _ o1 b281 b66 b6368 (List.nil : V2) (List.nil : V2) b6509 e7161 e6980 (by rfl)
theorem e7163 : o1.add b6368 (List.nil : V1)=b6368 := by rfl
theorem e7164 : o2.add (List.nil : V2) b6499=b6499 := by rfl
theorem e7165 : o2.add b6509 b6510=b6498 := @add_cons V1 _ o1 b6368 (List.nil : V1) b6368 (List.nil : V2) b6499 b6499 b6498 e7163 e7164 (by rfl)
theorem e7166 : o2.mul b6409 b67=b6498 := @mul_cons V1 _ o1 b281 b6411 b67 b6499 b6509 b6510 b6498 e7160 e7162 (by rfl) e7165
theorem e7167 : o1.mul b280 b66=b6367 := by decide
theorem e7168 : o1.scale b280 b67=b6511 := @scale_cons V1 _ o1 b280 b66 b6367 (List.nil : V2) (List.nil : V2) b6511 e7167 e6987 (by rfl)
theorem e7169 : o1.add b6367 (List.nil : V1)=b6367 := by rfl
theorem e7170 : o2.add (List.nil : V2) b6498=b6498 := by rfl
theorem e7171 : o2.add b6511 b6512=b6497 := @add_cons V1 _ o1 b6367 (List.nil : V1) b6367 (List.nil : V2) b6498 b6498 b6497 e7169 e7170 (by rfl)
theorem e7172 : o2.mul b6407 b67=b6497 := @mul_cons V1 _ o1 b280 b6409 b67 b6498 b6511 b6512 b6497 e7166 e7168 (by rfl) e7171
theorem e7173 : o1.mul b279 b66=b6366 := by decide
theorem e7174 : o1.scale b279 b67=b6513 := @scale_cons V1 _ o1 b279 b66 b6366 (List.nil : V2) (List.nil : V2) b6513 e7173 e6994 (by rfl)
theorem e7175 : o1.add b6366 (List.nil : V1)=b6366 := by rfl
theorem e7176 : o2.add (List.nil : V2) b6497=b6497 := by rfl
theorem e7177 : o2.add b6513 b6514=b6496 := @add_cons V1 _ o1 b6366 (List.nil : V1) b6366 (List.nil : V2) b6497 b6497 b6496 e7175 e7176 (by rfl)
theorem e7178 : o2.mul b6405 b67=b6496 := @mul_cons V1 _ o1 b279 b6407 b67 b6497 b6513 b6514 b6496 e7172 e7174 (by rfl) e7177
theorem e7179 : o1.mul b278 b66=b6365 := by decide
theorem e7180 : o1.scale b278 b67=b6515 := @scale_cons V1 _ o1 b278 b66 b6365 (List.nil : V2) (List.nil : V2) b6515 e7179 e7001 (by rfl)
theorem e7181 : o1.add b6365 (List.nil : V1)=b6365 := by rfl
theorem e7182 : o2.add (List.nil : V2) b6496=b6496 := by rfl
theorem e7183 : o2.add b6515 b6516=b6495 := @add_cons V1 _ o1 b6365 (List.nil : V1) b6365 (List.nil : V2) b6496 b6496 b6495 e7181 e7182 (by rfl)
theorem e7184 : o2.mul b6403 b67=b6495 := @mul_cons V1 _ o1 b278 b6405 b67 b6496 b6515 b6516 b6495 e7178 e7180 (by rfl) e7183
theorem e7185 : o1.mul b277 b66=b6364 := by decide
theorem e7186 : o1.scale b277 b67=b6517 := @scale_cons V1 _ o1 b277 b66 b6364 (List.nil : V2) (List.nil : V2) b6517 e7185 e7008 (by rfl)
theorem e7187 : o1.add b6364 (List.nil : V1)=b6364 := by rfl
theorem e7188 : o2.add (List.nil : V2) b6495=b6495 := by rfl
theorem e7189 : o2.add b6517 b6518=b6494 := @add_cons V1 _ o1 b6364 (List.nil : V1) b6364 (List.nil : V2) b6495 b6495 b6494 e7187 e7188 (by rfl)
theorem e7190 : o2.mul b6401 b67=b6494 := @mul_cons V1 _ o1 b277 b6403 b67 b6495 b6517 b6518 b6494 e7184 e7186 (by rfl) e7189
theorem e7191 : o1.mul b276 b66=b6363 := by decide
theorem e7192 : o1.scale b276 b67=b6519 := @scale_cons V1 _ o1 b276 b66 b6363 (List.nil : V2) (List.nil : V2) b6519 e7191 e7015 (by rfl)
theorem e7193 : o1.add b6363 (List.nil : V1)=b6363 := by rfl
theorem e7194 : o2.add (List.nil : V2) b6494=b6494 := by rfl
theorem e7195 : o2.add b6519 b6520=b6493 := @add_cons V1 _ o1 b6363 (List.nil : V1) b6363 (List.nil : V2) b6494 b6494 b6493 e7193 e7194 (by rfl)
theorem e7196 : o2.mul b6399 b67=b6493 := @mul_cons V1 _ o1 b276 b6401 b67 b6494 b6519 b6520 b6493 e7190 e7192 (by rfl) e7195
theorem e7197 : o1.mul b275 b66=b6362 := by decide
theorem e7198 : o1.scale b275 b67=b6521 := @scale_cons V1 _ o1 b275 b66 b6362 (List.nil : V2) (List.nil : V2) b6521 e7197 e7022 (by rfl)
theorem e7199 : o1.add b6362 (List.nil : V1)=b6362 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
