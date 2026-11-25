module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGPart001

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e100 : o2.add b231 b211=b241 := @add_cons V1 _ o1 b221 b153 b143 b232 b212 b242 b241 e96 e99 (by rfl)
theorem e101 : o2.add b230 b210=b240 := @add_cons V1 _ o1 b220 b152 b142 b231 b211 b241 b240 e95 e100 (by rfl)
theorem e102 : o2.add b229 b209=b239 := @add_cons V1 _ o1 b219 b151 b141 b230 b210 b240 b239 e94 e101 (by rfl)
theorem e103 : o2.add b228 b208=b238 := @add_cons V1 _ o1 b218 b150 b140 b229 b209 b239 b238 e93 e102 (by rfl)
theorem e104 : o2.add b227 b207=b237 := @add_cons V1 _ o1 b217 b149 b139 b228 b208 b238 b237 e92 e103 (by rfl)
theorem e105 : o2.add b226 b206=b236 := @add_cons V1 _ o1 b216 b148 b138 b227 b207 b237 b236 e91 e104 (by rfl)
theorem e106 : o2.add b225 b205=b235 := @add_cons V1 _ o1 b215 b147 b137 b226 b206 b236 b235 e90 e105 (by rfl)
theorem e107 : o2.add b224 b155=b234 := @add_cons V1 _ o1 b214 b146 b136 b225 b205 b235 b234 e89 e106 (by rfl)
theorem e108 : o2.add b223 b233=b144 := @add_cons V1 _ o1 b135 (List.nil : V1) b135 b224 b155 b234 b144 e88 e107 (by rfl)
theorem e109 : o2.mul b134 b10=b144 := @mul_cons V1 _ o1 b30 b145 b10 b155 b223 b233 b144 e66 e87 (by rfl) e108
theorem e110 : o1.mul b29 b0=b124 := by decide
theorem e111 : o1.mul b29 b1=b243 := by decide
theorem e112 : o1.mul b29 b2=b244 := by decide
theorem e113 : o1.mul b29 b3=b245 := by decide
theorem e114 : o1.mul b29 b4=b246 := by decide
theorem e115 : o1.mul b29 b5=b247 := by decide
theorem e116 : o1.mul b29 b6=b248 := by decide
theorem e117 : o1.mul b29 b7=b249 := by decide
theorem e118 : o1.mul b29 b8=b250 := by decide
theorem e119 : o1.mul b29 b9=b251 := by decide
theorem e120 : o1.scale b29 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e121 : o1.scale b29 b183=b261 := @scale_cons V1 _ o1 b29 b9 b251 (List.nil : V2) (List.nil : V2) b261 e119 e120 (by rfl)
theorem e122 : o1.scale b29 b181=b260 := @scale_cons V1 _ o1 b29 b8 b250 b183 b261 b260 e118 e121 (by rfl)
theorem e123 : o1.scale b29 b179=b259 := @scale_cons V1 _ o1 b29 b7 b249 b181 b260 b259 e117 e122 (by rfl)
theorem e124 : o1.scale b29 b177=b258 := @scale_cons V1 _ o1 b29 b6 b248 b179 b259 b258 e116 e123 (by rfl)
theorem e125 : o1.scale b29 b175=b257 := @scale_cons V1 _ o1 b29 b5 b247 b177 b258 b257 e115 e124 (by rfl)
theorem e126 : o1.scale b29 b173=b256 := @scale_cons V1 _ o1 b29 b4 b246 b175 b257 b256 e114 e125 (by rfl)
theorem e127 : o1.scale b29 b171=b255 := @scale_cons V1 _ o1 b29 b3 b245 b173 b256 b255 e113 e126 (by rfl)
theorem e128 : o1.scale b29 b169=b254 := @scale_cons V1 _ o1 b29 b2 b244 b171 b255 b254 e112 e127 (by rfl)
theorem e129 : o1.scale b29 b167=b253 := @scale_cons V1 _ o1 b29 b1 b243 b169 b254 b253 e111 e128 (by rfl)
theorem e130 : o1.scale b29 b10=b252 := @scale_cons V1 _ o1 b29 b0 b124 b167 b253 b252 e110 e129 (by rfl)
theorem e131 : o1.add b124 (List.nil : V1)=b124 := by rfl
theorem e132 : o1.add b243 b135=b125 := by decide
theorem e133 : o1.add b244 b136=b126 := by decide
theorem e134 : o1.add b245 b137=b127 := by decide
theorem e135 : o1.add b246 b138=b128 := by decide
theorem e136 : o1.add b247 b139=b129 := by decide
theorem e137 : o1.add b248 b140=b130 := by decide
theorem e138 : o1.add b249 b141=b131 := by decide
theorem e139 : o1.add b250 b142=b132 := by decide
theorem e140 : o1.add b251 b143=b63 := by decide
theorem e141 : o2.add (List.nil : V2) b242=b242 := by rfl
theorem e142 : o2.add b261 b241=b271 := @add_cons V1 _ o1 b251 b143 b63 (List.nil : V2) b242 b242 b271 e140 e141 (by rfl)
theorem e143 : o2.add b260 b240=b270 := @add_cons V1 _ o1 b250 b142 b132 b261 b241 b271 b270 e139 e142 (by rfl)
theorem e144 : o2.add b259 b239=b269 := @add_cons V1 _ o1 b249 b141 b131 b260 b240 b270 b269 e138 e143 (by rfl)
theorem e145 : o2.add b258 b238=b268 := @add_cons V1 _ o1 b248 b140 b130 b259 b239 b269 b268 e137 e144 (by rfl)
theorem e146 : o2.add b257 b237=b267 := @add_cons V1 _ o1 b247 b139 b129 b258 b238 b268 b267 e136 e145 (by rfl)
theorem e147 : o2.add b256 b236=b266 := @add_cons V1 _ o1 b246 b138 b128 b257 b237 b267 b266 e135 e146 (by rfl)
theorem e148 : o2.add b255 b235=b265 := @add_cons V1 _ o1 b245 b137 b127 b256 b236 b266 b265 e134 e147 (by rfl)
theorem e149 : o2.add b254 b234=b264 := @add_cons V1 _ o1 b244 b136 b126 b255 b235 b265 b264 e133 e148 (by rfl)
theorem e150 : o2.add b253 b144=b263 := @add_cons V1 _ o1 b243 b135 b125 b254 b234 b264 b263 e132 e149 (by rfl)
theorem e151 : o2.add b252 b262=b133 := @add_cons V1 _ o1 b124 (List.nil : V1) b124 b253 b144 b263 b133 e131 e150 (by rfl)
theorem e152 : o2.mul b123 b10=b133 := @mul_cons V1 _ o1 b29 b134 b10 b144 b252 b262 b133 e109 e130 (by rfl) e151
theorem e153 : o1.mul b28 b0=b113 := by decide
theorem e154 : o1.mul b28 b1=b272 := by decide
theorem e155 : o1.mul b28 b2=b273 := by decide
theorem e156 : o1.mul b28 b3=b274 := by decide
theorem e157 : o1.mul b28 b4=b275 := by decide
theorem e158 : o1.mul b28 b5=b276 := by decide
theorem e159 : o1.mul b28 b6=b277 := by decide
theorem e160 : o1.mul b28 b7=b278 := by decide
theorem e161 : o1.mul b28 b8=b279 := by decide
theorem e162 : o1.mul b28 b9=b280 := by decide
theorem e163 : o1.scale b28 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e164 : o1.scale b28 b183=b290 := @scale_cons V1 _ o1 b28 b9 b280 (List.nil : V2) (List.nil : V2) b290 e162 e163 (by rfl)
theorem e165 : o1.scale b28 b181=b289 := @scale_cons V1 _ o1 b28 b8 b279 b183 b290 b289 e161 e164 (by rfl)
theorem e166 : o1.scale b28 b179=b288 := @scale_cons V1 _ o1 b28 b7 b278 b181 b289 b288 e160 e165 (by rfl)
theorem e167 : o1.scale b28 b177=b287 := @scale_cons V1 _ o1 b28 b6 b277 b179 b288 b287 e159 e166 (by rfl)
theorem e168 : o1.scale b28 b175=b286 := @scale_cons V1 _ o1 b28 b5 b276 b177 b287 b286 e158 e167 (by rfl)
theorem e169 : o1.scale b28 b173=b285 := @scale_cons V1 _ o1 b28 b4 b275 b175 b286 b285 e157 e168 (by rfl)
theorem e170 : o1.scale b28 b171=b284 := @scale_cons V1 _ o1 b28 b3 b274 b173 b285 b284 e156 e169 (by rfl)
theorem e171 : o1.scale b28 b169=b283 := @scale_cons V1 _ o1 b28 b2 b273 b171 b284 b283 e155 e170 (by rfl)
theorem e172 : o1.scale b28 b167=b282 := @scale_cons V1 _ o1 b28 b1 b272 b169 b283 b282 e154 e171 (by rfl)
theorem e173 : o1.scale b28 b10=b281 := @scale_cons V1 _ o1 b28 b0 b113 b167 b282 b281 e153 e172 (by rfl)
theorem e174 : o1.add b113 (List.nil : V1)=b113 := by rfl
theorem e175 : o1.add b272 b124=b114 := by decide
theorem e176 : o1.add b273 b125=b115 := by decide
theorem e177 : o1.add b274 b126=b116 := by decide
theorem e178 : o1.add b275 b127=b117 := by decide
theorem e179 : o1.add b276 b128=b118 := by decide
theorem e180 : o1.add b277 b129=b119 := by decide
theorem e181 : o1.add b278 b130=b120 := by decide
theorem e182 : o1.add b279 b131=b121 := by decide
theorem e183 : o1.add b280 b132=b62 := by decide
theorem e184 : o2.add (List.nil : V2) b271=b271 := by rfl
theorem e185 : o2.add b290 b270=b300 := @add_cons V1 _ o1 b280 b132 b62 (List.nil : V2) b271 b271 b300 e183 e184 (by rfl)
theorem e186 : o2.add b289 b269=b299 := @add_cons V1 _ o1 b279 b131 b121 b290 b270 b300 b299 e182 e185 (by rfl)
theorem e187 : o2.add b288 b268=b298 := @add_cons V1 _ o1 b278 b130 b120 b289 b269 b299 b298 e181 e186 (by rfl)
theorem e188 : o2.add b287 b267=b297 := @add_cons V1 _ o1 b277 b129 b119 b288 b268 b298 b297 e180 e187 (by rfl)
theorem e189 : o2.add b286 b266=b296 := @add_cons V1 _ o1 b276 b128 b118 b287 b267 b297 b296 e179 e188 (by rfl)
theorem e190 : o2.add b285 b265=b295 := @add_cons V1 _ o1 b275 b127 b117 b286 b266 b296 b295 e178 e189 (by rfl)
theorem e191 : o2.add b284 b264=b294 := @add_cons V1 _ o1 b274 b126 b116 b285 b265 b295 b294 e177 e190 (by rfl)
theorem e192 : o2.add b283 b263=b293 := @add_cons V1 _ o1 b273 b125 b115 b284 b264 b294 b293 e176 e191 (by rfl)
theorem e193 : o2.add b282 b133=b292 := @add_cons V1 _ o1 b272 b124 b114 b283 b263 b293 b292 e175 e192 (by rfl)
theorem e194 : o2.add b281 b291=b122 := @add_cons V1 _ o1 b113 (List.nil : V1) b113 b282 b133 b292 b122 e174 e193 (by rfl)
theorem e195 : o2.mul b112 b10=b122 := @mul_cons V1 _ o1 b28 b123 b10 b133 b281 b291 b122 e152 e173 (by rfl) e194
theorem e196 : o1.mul b27 b0=b102 := by decide
theorem e197 : o1.mul b27 b1=b301 := by decide
theorem e198 : o1.mul b27 b2=b302 := by decide
theorem e199 : o1.mul b27 b3=b303 := by decide

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
