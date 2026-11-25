module

public import RKCert.ReviewedNative.NativePencilQuarticIntDAGData

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilQuarticIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e0 : o2.mul (List.nil : V2) b10=(List.nil : V2) := by rfl
theorem e1 : o1.mul b32 b0=b157 := by decide
theorem e2 : o1.mul b32 b1=b158 := by decide
theorem e3 : o1.mul b32 b2=b159 := by decide
theorem e4 : o1.mul b32 b3=b160 := by decide
theorem e5 : o1.mul b32 b4=b161 := by decide
theorem e6 : o1.mul b32 b5=b162 := by decide
theorem e7 : o1.mul b32 b6=b163 := by decide
theorem e8 : o1.mul b32 b7=b164 := by decide
theorem e9 : o1.mul b32 b8=b165 := by decide
theorem e10 : o1.mul b32 b9=b66 := by decide
theorem e11 : o1.scale b32 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e12 : o1.scale b32 b183=b184 := @scale_cons V1 _ o1 b32 b9 b66 (List.nil : V2) (List.nil : V2) b184 e10 e11 (by rfl)
theorem e13 : o1.scale b32 b181=b182 := @scale_cons V1 _ o1 b32 b8 b165 b183 b184 b182 e9 e12 (by rfl)
theorem e14 : o1.scale b32 b179=b180 := @scale_cons V1 _ o1 b32 b7 b164 b181 b182 b180 e8 e13 (by rfl)
theorem e15 : o1.scale b32 b177=b178 := @scale_cons V1 _ o1 b32 b6 b163 b179 b180 b178 e7 e14 (by rfl)
theorem e16 : o1.scale b32 b175=b176 := @scale_cons V1 _ o1 b32 b5 b162 b177 b178 b176 e6 e15 (by rfl)
theorem e17 : o1.scale b32 b173=b174 := @scale_cons V1 _ o1 b32 b4 b161 b175 b176 b174 e5 e16 (by rfl)
theorem e18 : o1.scale b32 b171=b172 := @scale_cons V1 _ o1 b32 b3 b160 b173 b174 b172 e4 e17 (by rfl)
theorem e19 : o1.scale b32 b169=b170 := @scale_cons V1 _ o1 b32 b2 b159 b171 b172 b170 e3 e18 (by rfl)
theorem e20 : o1.scale b32 b167=b168 := @scale_cons V1 _ o1 b32 b1 b158 b169 b170 b168 e2 e19 (by rfl)
theorem e21 : o1.scale b32 b10=b166 := @scale_cons V1 _ o1 b32 b0 b157 b167 b168 b166 e1 e20 (by rfl)
theorem e22 : o2.add b166 (List.nil : V2)=b166 := by rfl
theorem e23 : o2.mul b156 b10=b166 := @mul_cons V1 _ o1 b32 (List.nil : V2) b10 (List.nil : V2) b166 (List.nil : V2) b166 e0 e21 (by rfl) e22
theorem e24 : o1.mul b31 b0=b146 := by decide
theorem e25 : o1.mul b31 b1=b185 := by decide
theorem e26 : o1.mul b31 b2=b186 := by decide
theorem e27 : o1.mul b31 b3=b187 := by decide
theorem e28 : o1.mul b31 b4=b188 := by decide
theorem e29 : o1.mul b31 b5=b189 := by decide
theorem e30 : o1.mul b31 b6=b190 := by decide
theorem e31 : o1.mul b31 b7=b191 := by decide
theorem e32 : o1.mul b31 b8=b192 := by decide
theorem e33 : o1.mul b31 b9=b193 := by decide
theorem e34 : o1.scale b31 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e35 : o1.scale b31 b183=b203 := @scale_cons V1 _ o1 b31 b9 b193 (List.nil : V2) (List.nil : V2) b203 e33 e34 (by rfl)
theorem e36 : o1.scale b31 b181=b202 := @scale_cons V1 _ o1 b31 b8 b192 b183 b203 b202 e32 e35 (by rfl)
theorem e37 : o1.scale b31 b179=b201 := @scale_cons V1 _ o1 b31 b7 b191 b181 b202 b201 e31 e36 (by rfl)
theorem e38 : o1.scale b31 b177=b200 := @scale_cons V1 _ o1 b31 b6 b190 b179 b201 b200 e30 e37 (by rfl)
theorem e39 : o1.scale b31 b175=b199 := @scale_cons V1 _ o1 b31 b5 b189 b177 b200 b199 e29 e38 (by rfl)
theorem e40 : o1.scale b31 b173=b198 := @scale_cons V1 _ o1 b31 b4 b188 b175 b199 b198 e28 e39 (by rfl)
theorem e41 : o1.scale b31 b171=b197 := @scale_cons V1 _ o1 b31 b3 b187 b173 b198 b197 e27 e40 (by rfl)
theorem e42 : o1.scale b31 b169=b196 := @scale_cons V1 _ o1 b31 b2 b186 b171 b197 b196 e26 e41 (by rfl)
theorem e43 : o1.scale b31 b167=b195 := @scale_cons V1 _ o1 b31 b1 b185 b169 b196 b195 e25 e42 (by rfl)
theorem e44 : o1.scale b31 b10=b194 := @scale_cons V1 _ o1 b31 b0 b146 b167 b195 b194 e24 e43 (by rfl)
theorem e45 : o1.add b146 (List.nil : V1)=b146 := by rfl
theorem e46 : o1.add b185 b157=b147 := by decide
theorem e47 : o1.add b186 b158=b148 := by decide
theorem e48 : o1.add b187 b159=b149 := by decide
theorem e49 : o1.add b188 b160=b150 := by decide
theorem e50 : o1.add b189 b161=b151 := by decide
theorem e51 : o1.add b190 b162=b152 := by decide
theorem e52 : o1.add b191 b163=b153 := by decide
theorem e53 : o1.add b192 b164=b154 := by decide
theorem e54 : o1.add b193 b165=b65 := by decide
theorem e55 : o2.add (List.nil : V2) b184=b184 := by rfl
theorem e56 : o2.add b203 b182=b213 := @add_cons V1 _ o1 b193 b165 b65 (List.nil : V2) b184 b184 b213 e54 e55 (by rfl)
theorem e57 : o2.add b202 b180=b212 := @add_cons V1 _ o1 b192 b164 b154 b203 b182 b213 b212 e53 e56 (by rfl)
theorem e58 : o2.add b201 b178=b211 := @add_cons V1 _ o1 b191 b163 b153 b202 b180 b212 b211 e52 e57 (by rfl)
theorem e59 : o2.add b200 b176=b210 := @add_cons V1 _ o1 b190 b162 b152 b201 b178 b211 b210 e51 e58 (by rfl)
theorem e60 : o2.add b199 b174=b209 := @add_cons V1 _ o1 b189 b161 b151 b200 b176 b210 b209 e50 e59 (by rfl)
theorem e61 : o2.add b198 b172=b208 := @add_cons V1 _ o1 b188 b160 b150 b199 b174 b209 b208 e49 e60 (by rfl)
theorem e62 : o2.add b197 b170=b207 := @add_cons V1 _ o1 b187 b159 b149 b198 b172 b208 b207 e48 e61 (by rfl)
theorem e63 : o2.add b196 b168=b206 := @add_cons V1 _ o1 b186 b158 b148 b197 b170 b207 b206 e47 e62 (by rfl)
theorem e64 : o2.add b195 b166=b205 := @add_cons V1 _ o1 b185 b157 b147 b196 b168 b206 b205 e46 e63 (by rfl)
theorem e65 : o2.add b194 b204=b155 := @add_cons V1 _ o1 b146 (List.nil : V1) b146 b195 b166 b205 b155 e45 e64 (by rfl)
theorem e66 : o2.mul b145 b10=b155 := @mul_cons V1 _ o1 b31 b156 b10 b166 b194 b204 b155 e23 e44 (by rfl) e65
theorem e67 : o1.mul b30 b0=b135 := by decide
theorem e68 : o1.mul b30 b1=b214 := by decide
theorem e69 : o1.mul b30 b2=b215 := by decide
theorem e70 : o1.mul b30 b3=b216 := by decide
theorem e71 : o1.mul b30 b4=b217 := by decide
theorem e72 : o1.mul b30 b5=b218 := by decide
theorem e73 : o1.mul b30 b6=b219 := by decide
theorem e74 : o1.mul b30 b7=b220 := by decide
theorem e75 : o1.mul b30 b8=b221 := by decide
theorem e76 : o1.mul b30 b9=b222 := by decide
theorem e77 : o1.scale b30 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e78 : o1.scale b30 b183=b232 := @scale_cons V1 _ o1 b30 b9 b222 (List.nil : V2) (List.nil : V2) b232 e76 e77 (by rfl)
theorem e79 : o1.scale b30 b181=b231 := @scale_cons V1 _ o1 b30 b8 b221 b183 b232 b231 e75 e78 (by rfl)
theorem e80 : o1.scale b30 b179=b230 := @scale_cons V1 _ o1 b30 b7 b220 b181 b231 b230 e74 e79 (by rfl)
theorem e81 : o1.scale b30 b177=b229 := @scale_cons V1 _ o1 b30 b6 b219 b179 b230 b229 e73 e80 (by rfl)
theorem e82 : o1.scale b30 b175=b228 := @scale_cons V1 _ o1 b30 b5 b218 b177 b229 b228 e72 e81 (by rfl)
theorem e83 : o1.scale b30 b173=b227 := @scale_cons V1 _ o1 b30 b4 b217 b175 b228 b227 e71 e82 (by rfl)
theorem e84 : o1.scale b30 b171=b226 := @scale_cons V1 _ o1 b30 b3 b216 b173 b227 b226 e70 e83 (by rfl)
theorem e85 : o1.scale b30 b169=b225 := @scale_cons V1 _ o1 b30 b2 b215 b171 b226 b225 e69 e84 (by rfl)
theorem e86 : o1.scale b30 b167=b224 := @scale_cons V1 _ o1 b30 b1 b214 b169 b225 b224 e68 e85 (by rfl)
theorem e87 : o1.scale b30 b10=b223 := @scale_cons V1 _ o1 b30 b0 b135 b167 b224 b223 e67 e86 (by rfl)
theorem e88 : o1.add b135 (List.nil : V1)=b135 := by rfl
theorem e89 : o1.add b214 b146=b136 := by decide
theorem e90 : o1.add b215 b147=b137 := by decide
theorem e91 : o1.add b216 b148=b138 := by decide
theorem e92 : o1.add b217 b149=b139 := by decide
theorem e93 : o1.add b218 b150=b140 := by decide
theorem e94 : o1.add b219 b151=b141 := by decide
theorem e95 : o1.add b220 b152=b142 := by decide
theorem e96 : o1.add b221 b153=b143 := by decide
theorem e97 : o1.add b222 b154=b64 := by decide
theorem e98 : o2.add (List.nil : V2) b213=b213 := by rfl
theorem e99 : o2.add b232 b212=b242 := @add_cons V1 _ o1 b222 b154 b64 (List.nil : V2) b213 b213 b242 e97 e98 (by rfl)

end RKResearch.Certified.Graded.NativePencilQuarticIntDAG
