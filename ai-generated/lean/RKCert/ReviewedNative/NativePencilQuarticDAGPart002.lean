module

public import RKCert.ReviewedNative.NativePencilQuarticDAGPart001

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e100 : o1.mul b41 b20=b313 := by decide
theorem e101 : o1.mul b41 b21=b314 := by decide
theorem e102 : o1.mul b41 b22=b315 := by decide
theorem e103 : o1.mul b41 b23=b316 := by decide
theorem e104 : o1.mul b41 b24=b317 := by decide
theorem e105 : o1.mul b41 b25=b318 := by decide
theorem e106 : o1.mul b41 b26=b319 := by decide
theorem e107 : o1.mul b41 b27=b320 := by decide
theorem e108 : o1.mul b41 b28=b321 := by decide
theorem e109 : o1.mul b41 b29=b322 := by decide
theorem e110 : o1.mul b41 b30=b323 := by decide
theorem e111 : o1.mul b41 b31=b324 := by decide
theorem e112 : o1.mul b41 b32=b325 := by decide
theorem e113 : o1.scale b41 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e114 : o1.scale b41 b266=b340 := @scale_cons V1 _ o1 b41 b32 b325 (List.nil : V2) (List.nil : V2) b340 e112 e113 (by rfl)
theorem e115 : o1.scale b41 b264=b339 := @scale_cons V1 _ o1 b41 b31 b324 b266 b340 b339 e111 e114 (by rfl)
theorem e116 : o1.scale b41 b262=b338 := @scale_cons V1 _ o1 b41 b30 b323 b264 b339 b338 e110 e115 (by rfl)
theorem e117 : o1.scale b41 b260=b337 := @scale_cons V1 _ o1 b41 b29 b322 b262 b338 b337 e109 e116 (by rfl)
theorem e118 : o1.scale b41 b258=b336 := @scale_cons V1 _ o1 b41 b28 b321 b260 b337 b336 e108 e117 (by rfl)
theorem e119 : o1.scale b41 b256=b335 := @scale_cons V1 _ o1 b41 b27 b320 b258 b336 b335 e107 e118 (by rfl)
theorem e120 : o1.scale b41 b254=b334 := @scale_cons V1 _ o1 b41 b26 b319 b256 b335 b334 e106 e119 (by rfl)
theorem e121 : o1.scale b41 b252=b333 := @scale_cons V1 _ o1 b41 b25 b318 b254 b334 b333 e105 e120 (by rfl)
theorem e122 : o1.scale b41 b250=b332 := @scale_cons V1 _ o1 b41 b24 b317 b252 b333 b332 e104 e121 (by rfl)
theorem e123 : o1.scale b41 b248=b331 := @scale_cons V1 _ o1 b41 b23 b316 b250 b332 b331 e103 e122 (by rfl)
theorem e124 : o1.scale b41 b246=b330 := @scale_cons V1 _ o1 b41 b22 b315 b248 b331 b330 e102 e123 (by rfl)
theorem e125 : o1.scale b41 b244=b329 := @scale_cons V1 _ o1 b41 b21 b314 b246 b330 b329 e101 e124 (by rfl)
theorem e126 : o1.scale b41 b242=b328 := @scale_cons V1 _ o1 b41 b20 b313 b244 b329 b328 e100 e125 (by rfl)
theorem e127 : o1.scale b41 b240=b327 := @scale_cons V1 _ o1 b41 b19 b312 b242 b328 b327 e99 e126 (by rfl)
theorem e128 : o1.scale b41 b33=b326 := @scale_cons V1 _ o1 b41 b18 b193 b240 b327 b326 e98 e127 (by rfl)
theorem e129 : o1.add b193 (List.nil : V1)=b193 := by rfl
theorem e130 : o1.add b312 b209=b194 := by decide
theorem e131 : o1.add b313 b210=b195 := by decide
theorem e132 : o1.add b314 b211=b196 := by decide
theorem e133 : o1.add b315 b212=b197 := by decide
theorem e134 : o1.add b316 b213=b198 := by decide
theorem e135 : o1.add b317 b214=b199 := by decide
theorem e136 : o1.add b318 b215=b200 := by decide
theorem e137 : o1.add b319 b216=b201 := by decide
theorem e138 : o1.add b320 b217=b202 := by decide
theorem e139 : o1.add b321 b218=b203 := by decide
theorem e140 : o1.add b322 b219=b204 := by decide
theorem e141 : o1.add b323 b220=b205 := by decide
theorem e142 : o1.add b324 b221=b206 := by decide
theorem e143 : o1.add b325 b222=b107 := by decide
theorem e144 : o2.add (List.nil : V2) b311=b311 := by rfl
theorem e145 : o2.add b340 b310=b355 := @add_cons V1 _ o1 b325 b222 b107 (List.nil : V2) b311 b311 b355 e143 e144 (by rfl)
theorem e146 : o2.add b339 b309=b354 := @add_cons V1 _ o1 b324 b221 b206 b340 b310 b355 b354 e142 e145 (by rfl)
theorem e147 : o2.add b338 b308=b353 := @add_cons V1 _ o1 b323 b220 b205 b339 b309 b354 b353 e141 e146 (by rfl)
theorem e148 : o2.add b337 b307=b352 := @add_cons V1 _ o1 b322 b219 b204 b338 b308 b353 b352 e140 e147 (by rfl)
theorem e149 : o2.add b336 b306=b351 := @add_cons V1 _ o1 b321 b218 b203 b337 b307 b352 b351 e139 e148 (by rfl)
theorem e150 : o2.add b335 b305=b350 := @add_cons V1 _ o1 b320 b217 b202 b336 b306 b351 b350 e138 e149 (by rfl)
theorem e151 : o2.add b334 b304=b349 := @add_cons V1 _ o1 b319 b216 b201 b335 b305 b350 b349 e137 e150 (by rfl)
theorem e152 : o2.add b333 b303=b348 := @add_cons V1 _ o1 b318 b215 b200 b334 b304 b349 b348 e136 e151 (by rfl)
theorem e153 : o2.add b332 b302=b347 := @add_cons V1 _ o1 b317 b214 b199 b333 b303 b348 b347 e135 e152 (by rfl)
theorem e154 : o2.add b331 b301=b346 := @add_cons V1 _ o1 b316 b213 b198 b332 b302 b347 b346 e134 e153 (by rfl)
theorem e155 : o2.add b330 b300=b345 := @add_cons V1 _ o1 b315 b212 b197 b331 b301 b346 b345 e133 e154 (by rfl)
theorem e156 : o2.add b329 b299=b344 := @add_cons V1 _ o1 b314 b211 b196 b330 b300 b345 b344 e132 e155 (by rfl)
theorem e157 : o2.add b328 b298=b343 := @add_cons V1 _ o1 b313 b210 b195 b329 b299 b344 b343 e131 e156 (by rfl)
theorem e158 : o2.add b327 b223=b342 := @add_cons V1 _ o1 b312 b209 b194 b328 b298 b343 b342 e130 e157 (by rfl)
theorem e159 : o2.add b326 b341=b207 := @add_cons V1 _ o1 b193 (List.nil : V1) b193 b327 b223 b342 b207 e129 e158 (by rfl)
theorem e160 : o2.mul b192 b33=b207 := @mul_cons V1 _ o1 b41 b208 b33 b223 b326 b341 b207 e97 e128 (by rfl) e159
theorem e161 : o1.mul b40 b18=b177 := by decide
theorem e162 : o1.mul b40 b19=b356 := by decide
theorem e163 : o1.mul b40 b20=b357 := by decide
theorem e164 : o1.mul b40 b21=b358 := by decide
theorem e165 : o1.mul b40 b22=b359 := by decide
theorem e166 : o1.mul b40 b23=b360 := by decide
theorem e167 : o1.mul b40 b24=b361 := by decide
theorem e168 : o1.mul b40 b25=b362 := by decide
theorem e169 : o1.mul b40 b26=b363 := by decide
theorem e170 : o1.mul b40 b27=b364 := by decide
theorem e171 : o1.mul b40 b28=b365 := by decide
theorem e172 : o1.mul b40 b29=b366 := by decide
theorem e173 : o1.mul b40 b30=b367 := by decide
theorem e174 : o1.mul b40 b31=b368 := by decide
theorem e175 : o1.mul b40 b32=b369 := by decide
theorem e176 : o1.scale b40 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e177 : o1.scale b40 b266=b384 := @scale_cons V1 _ o1 b40 b32 b369 (List.nil : V2) (List.nil : V2) b384 e175 e176 (by rfl)
theorem e178 : o1.scale b40 b264=b383 := @scale_cons V1 _ o1 b40 b31 b368 b266 b384 b383 e174 e177 (by rfl)
theorem e179 : o1.scale b40 b262=b382 := @scale_cons V1 _ o1 b40 b30 b367 b264 b383 b382 e173 e178 (by rfl)
theorem e180 : o1.scale b40 b260=b381 := @scale_cons V1 _ o1 b40 b29 b366 b262 b382 b381 e172 e179 (by rfl)
theorem e181 : o1.scale b40 b258=b380 := @scale_cons V1 _ o1 b40 b28 b365 b260 b381 b380 e171 e180 (by rfl)
theorem e182 : o1.scale b40 b256=b379 := @scale_cons V1 _ o1 b40 b27 b364 b258 b380 b379 e170 e181 (by rfl)
theorem e183 : o1.scale b40 b254=b378 := @scale_cons V1 _ o1 b40 b26 b363 b256 b379 b378 e169 e182 (by rfl)
theorem e184 : o1.scale b40 b252=b377 := @scale_cons V1 _ o1 b40 b25 b362 b254 b378 b377 e168 e183 (by rfl)
theorem e185 : o1.scale b40 b250=b376 := @scale_cons V1 _ o1 b40 b24 b361 b252 b377 b376 e167 e184 (by rfl)
theorem e186 : o1.scale b40 b248=b375 := @scale_cons V1 _ o1 b40 b23 b360 b250 b376 b375 e166 e185 (by rfl)
theorem e187 : o1.scale b40 b246=b374 := @scale_cons V1 _ o1 b40 b22 b359 b248 b375 b374 e165 e186 (by rfl)
theorem e188 : o1.scale b40 b244=b373 := @scale_cons V1 _ o1 b40 b21 b358 b246 b374 b373 e164 e187 (by rfl)
theorem e189 : o1.scale b40 b242=b372 := @scale_cons V1 _ o1 b40 b20 b357 b244 b373 b372 e163 e188 (by rfl)
theorem e190 : o1.scale b40 b240=b371 := @scale_cons V1 _ o1 b40 b19 b356 b242 b372 b371 e162 e189 (by rfl)
theorem e191 : o1.scale b40 b33=b370 := @scale_cons V1 _ o1 b40 b18 b177 b240 b371 b370 e161 e190 (by rfl)
theorem e192 : o1.add b177 (List.nil : V1)=b177 := by rfl
theorem e193 : o1.add b356 b193=b178 := by decide
theorem e194 : o1.add b357 b194=b179 := by decide
theorem e195 : o1.add b358 b195=b180 := by decide
theorem e196 : o1.add b359 b196=b181 := by decide
theorem e197 : o1.add b360 b197=b182 := by decide
theorem e198 : o1.add b361 b198=b183 := by decide
theorem e199 : o1.add b362 b199=b184 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticDAG
