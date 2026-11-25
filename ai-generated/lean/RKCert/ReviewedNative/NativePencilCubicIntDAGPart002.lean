module

public import RKCert.ReviewedNative.NativePencilCubicIntDAGPart001

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e100 : o1.mul b14 b3=b132 := by decide
theorem e101 : o1.mul b14 b4=b133 := by decide
theorem e102 : o1.mul b14 b5=b134 := by decide
theorem e103 : o1.scale b14 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e104 : o1.scale b14 b77=b140 := @scale_cons V1 _ o1 b14 b5 b134 (List.nil : V2) (List.nil : V2) b140 e102 e103 (by rfl)
theorem e105 : o1.scale b14 b75=b139 := @scale_cons V1 _ o1 b14 b4 b133 b77 b140 b139 e101 e104 (by rfl)
theorem e106 : o1.scale b14 b73=b138 := @scale_cons V1 _ o1 b14 b3 b132 b75 b139 b138 e100 e105 (by rfl)
theorem e107 : o1.scale b14 b71=b137 := @scale_cons V1 _ o1 b14 b2 b131 b73 b138 b137 e99 e106 (by rfl)
theorem e108 : o1.scale b14 b69=b136 := @scale_cons V1 _ o1 b14 b1 b130 b71 b137 b136 e98 e107 (by rfl)
theorem e109 : o1.scale b14 b6=b135 := @scale_cons V1 _ o1 b14 b0 b30 b69 b136 b135 e97 e108 (by rfl)
theorem e110 : o1.add b30 (List.nil : V1)=b30 := by rfl
theorem e111 : o1.add b130 b42=b31 := by decide
theorem e112 : o1.add b131 b43=b32 := by decide
theorem e113 : o1.add b132 b44=b33 := by decide
theorem e114 : o1.add b133 b45=b34 := by decide
theorem e115 : o1.add b134 b46=b35 := by decide
theorem e116 : o2.add (List.nil : V2) b129=b129 := by rfl
theorem e117 : o2.add b140 b128=b146 := @add_cons V1 _ o1 b134 b46 b35 (List.nil : V2) b129 b129 b146 e115 e116 (by rfl)
theorem e118 : o2.add b139 b127=b145 := @add_cons V1 _ o1 b133 b45 b34 b140 b128 b146 b145 e114 e117 (by rfl)
theorem e119 : o2.add b138 b126=b144 := @add_cons V1 _ o1 b132 b44 b33 b139 b127 b145 b144 e113 e118 (by rfl)
theorem e120 : o2.add b137 b125=b143 := @add_cons V1 _ o1 b131 b43 b32 b138 b126 b144 b143 e112 e119 (by rfl)
theorem e121 : o2.add b136 b47=b142 := @add_cons V1 _ o1 b130 b42 b31 b137 b125 b143 b142 e111 e120 (by rfl)
theorem e122 : o2.add b135 b141=b40 := @add_cons V1 _ o1 b30 (List.nil : V1) b30 b136 b47 b142 b40 e110 e121 (by rfl)
theorem e123 : o2.mul b19 b6=b40 := @mul_cons V1 _ o1 b14 b41 b6 b47 b135 b141 b40 e96 e109 (by rfl) e122
theorem e124 : o2.mul (List.nil : V2) b13=(List.nil : V2) := by rfl
theorem e125 : o1.mul b24 b7=b180 := by decide
theorem e126 : o1.mul b24 b8=b181 := by decide
theorem e127 : o1.mul b24 b9=b182 := by decide
theorem e128 : o1.mul b24 b10=b183 := by decide
theorem e129 : o1.mul b24 b11=b184 := by decide
theorem e130 : o1.mul b200 b12=b201 := by decide
theorem e131 : o0.scale 0 b12=(List.nil : V1) := by decide
theorem e132 : o1.add (List.nil : V1) b199=b199 := by rfl
theorem e133 : o1.mul b198 b12=b199 := @mul_cons V0 _ o0 0 b200 b12 b201 (List.nil : V1) b199 b199 e130 e131 (by rfl) e132
theorem e134 : o1.add (List.nil : V1) b197=b197 := by rfl
theorem e135 : o1.mul b196 b12=b197 := @mul_cons V0 _ o0 0 b198 b12 b199 (List.nil : V1) b197 b197 e133 e131 (by rfl) e134
theorem e136 : o1.add (List.nil : V1) b156=b156 := by rfl
theorem e137 : o1.mul b24 b12=b156 := @mul_cons V0 _ o0 0 b196 b12 b197 (List.nil : V1) b156 b156 e135 e131 (by rfl) e136
theorem e138 : o1.scale b24 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e139 : o1.scale b24 b194=b195 := @scale_cons V1 _ o1 b24 b12 b156 (List.nil : V2) (List.nil : V2) b195 e137 e138 (by rfl)
theorem e140 : o1.scale b24 b192=b193 := @scale_cons V1 _ o1 b24 b11 b184 b194 b195 b193 e129 e139 (by rfl)
theorem e141 : o1.scale b24 b190=b191 := @scale_cons V1 _ o1 b24 b10 b183 b192 b193 b191 e128 e140 (by rfl)
theorem e142 : o1.scale b24 b188=b189 := @scale_cons V1 _ o1 b24 b9 b182 b190 b191 b189 e127 e141 (by rfl)
theorem e143 : o1.scale b24 b186=b187 := @scale_cons V1 _ o1 b24 b8 b181 b188 b189 b187 e126 e142 (by rfl)
theorem e144 : o1.scale b24 b13=b185 := @scale_cons V1 _ o1 b24 b7 b180 b186 b187 b185 e125 e143 (by rfl)
theorem e145 : o2.add b185 (List.nil : V2)=b185 := by rfl
theorem e146 : o2.mul b179 b13=b185 := @mul_cons V1 _ o1 b24 (List.nil : V2) b13 (List.nil : V2) b185 (List.nil : V2) b185 e124 e144 (by rfl) e145
theorem e147 : o1.mul b23 b7=b173 := by decide
theorem e148 : o1.mul b23 b8=b202 := by decide
theorem e149 : o1.mul b23 b9=b203 := by decide
theorem e150 : o1.mul b23 b10=b204 := by decide
theorem e151 : o1.mul b23 b11=b205 := by decide
theorem e152 : o1.mul b217 b12=b218 := by decide
theorem e153 : o1.add (List.nil : V1) b216=b216 := by rfl
theorem e154 : o1.mul b215 b12=b216 := @mul_cons V0 _ o0 0 b217 b12 b218 (List.nil : V1) b216 b216 e152 e131 (by rfl) e153
theorem e155 : o1.add (List.nil : V1) b214=b214 := by rfl
theorem e156 : o1.mul b213 b12=b214 := @mul_cons V0 _ o0 0 b215 b12 b216 (List.nil : V1) b214 b214 e154 e131 (by rfl) e155
theorem e157 : o1.add (List.nil : V1) b206=b206 := by rfl
theorem e158 : o1.mul b23 b12=b206 := @mul_cons V0 _ o0 0 b213 b12 b214 (List.nil : V1) b206 b206 e156 e131 (by rfl) e157
theorem e159 : o1.scale b23 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e160 : o1.scale b23 b194=b212 := @scale_cons V1 _ o1 b23 b12 b206 (List.nil : V2) (List.nil : V2) b212 e158 e159 (by rfl)
theorem e161 : o1.scale b23 b192=b211 := @scale_cons V1 _ o1 b23 b11 b205 b194 b212 b211 e151 e160 (by rfl)
theorem e162 : o1.scale b23 b190=b210 := @scale_cons V1 _ o1 b23 b10 b204 b192 b211 b210 e150 e161 (by rfl)
theorem e163 : o1.scale b23 b188=b209 := @scale_cons V1 _ o1 b23 b9 b203 b190 b210 b209 e149 e162 (by rfl)
theorem e164 : o1.scale b23 b186=b208 := @scale_cons V1 _ o1 b23 b8 b202 b188 b209 b208 e148 e163 (by rfl)
theorem e165 : o1.scale b23 b13=b207 := @scale_cons V1 _ o1 b23 b7 b173 b186 b208 b207 e147 e164 (by rfl)
theorem e166 : o1.add b173 (List.nil : V1)=b173 := by rfl
theorem e167 : o1.add b202 b180=b174 := by decide
theorem e168 : o1.add b203 b181=b175 := by decide
theorem e169 : o1.add b204 b182=b176 := by decide
theorem e170 : o1.add b205 b183=b177 := by decide
theorem e171 : o1.add b206 b184=b155 := by decide
theorem e172 : o2.add (List.nil : V2) b195=b195 := by rfl
theorem e173 : o2.add b212 b193=b224 := @add_cons V1 _ o1 b206 b184 b155 (List.nil : V2) b195 b195 b224 e171 e172 (by rfl)
theorem e174 : o2.add b211 b191=b223 := @add_cons V1 _ o1 b205 b183 b177 b212 b193 b224 b223 e170 e173 (by rfl)
theorem e175 : o2.add b210 b189=b222 := @add_cons V1 _ o1 b204 b182 b176 b211 b191 b223 b222 e169 e174 (by rfl)
theorem e176 : o2.add b209 b187=b221 := @add_cons V1 _ o1 b203 b181 b175 b210 b189 b222 b221 e168 e175 (by rfl)
theorem e177 : o2.add b208 b185=b220 := @add_cons V1 _ o1 b202 b180 b174 b209 b187 b221 b220 e167 e176 (by rfl)
theorem e178 : o2.add b207 b219=b178 := @add_cons V1 _ o1 b173 (List.nil : V1) b173 b208 b185 b220 b178 e166 e177 (by rfl)
theorem e179 : o2.mul b172 b13=b178 := @mul_cons V1 _ o1 b23 b179 b13 b185 b207 b219 b178 e146 e165 (by rfl) e178
theorem e180 : o1.mul b22 b7=b166 := by decide
theorem e181 : o1.mul b22 b8=b225 := by decide
theorem e182 : o1.mul b22 b9=b226 := by decide
theorem e183 : o1.mul b22 b10=b227 := by decide
theorem e184 : o1.mul b22 b11=b228 := by decide
theorem e185 : o1.mul b240 b12=b241 := by decide
theorem e186 : o1.add (List.nil : V1) b239=b239 := by rfl
theorem e187 : o1.mul b238 b12=b239 := @mul_cons V0 _ o0 0 b240 b12 b241 (List.nil : V1) b239 b239 e185 e131 (by rfl) e186
theorem e188 : o1.add (List.nil : V1) b237=b237 := by rfl
theorem e189 : o1.mul b236 b12=b237 := @mul_cons V0 _ o0 0 b238 b12 b239 (List.nil : V1) b237 b237 e187 e131 (by rfl) e188
theorem e190 : o1.add (List.nil : V1) b229=b229 := by rfl
theorem e191 : o1.mul b22 b12=b229 := @mul_cons V0 _ o0 0 b236 b12 b237 (List.nil : V1) b229 b229 e189 e131 (by rfl) e190
theorem e192 : o1.scale b22 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e193 : o1.scale b22 b194=b235 := @scale_cons V1 _ o1 b22 b12 b229 (List.nil : V2) (List.nil : V2) b235 e191 e192 (by rfl)
theorem e194 : o1.scale b22 b192=b234 := @scale_cons V1 _ o1 b22 b11 b228 b194 b235 b234 e184 e193 (by rfl)
theorem e195 : o1.scale b22 b190=b233 := @scale_cons V1 _ o1 b22 b10 b227 b192 b234 b233 e183 e194 (by rfl)
theorem e196 : o1.scale b22 b188=b232 := @scale_cons V1 _ o1 b22 b9 b226 b190 b233 b232 e182 e195 (by rfl)
theorem e197 : o1.scale b22 b186=b231 := @scale_cons V1 _ o1 b22 b8 b225 b188 b232 b231 e181 e196 (by rfl)
theorem e198 : o1.scale b22 b13=b230 := @scale_cons V1 _ o1 b22 b7 b166 b186 b231 b230 e180 e197 (by rfl)
theorem e199 : o1.add b166 (List.nil : V1)=b166 := by rfl

end RKResearch.Certified.Graded.NativePencilCubicIntDAG
