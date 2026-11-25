module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart041

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6150 : o2.add (List.nil : V2) b5885=b5885 := by rfl
theorem e6151 : o2.add b5910 b5911=b5883 := @add_cons V1 _ o1 b5328 (List.nil : V1) b5328 (List.nil : V2) b5885 b5885 b5883 e6149 e6150 (by rfl)
theorem e6152 : o2.mul b5882 b63=b5883 := @mul_cons V1 _ o1 b305 b5884 b63 b5885 b5910 b5911 b5883 e6145 e6148 (by rfl) e6151
theorem e6153 : o1.mul b304 b62=b5327 := by decide
theorem e6154 : o1.scale b304 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6155 : o1.scale b304 b63=b5912 := @scale_cons V1 _ o1 b304 b62 b5327 (List.nil : V2) (List.nil : V2) b5912 e6153 e6154 (by rfl)
theorem e6156 : o1.add b5327 (List.nil : V1)=b5327 := by rfl
theorem e6157 : o2.add (List.nil : V2) b5883=b5883 := by rfl
theorem e6158 : o2.add b5912 b5913=b5881 := @add_cons V1 _ o1 b5327 (List.nil : V1) b5327 (List.nil : V2) b5883 b5883 b5881 e6156 e6157 (by rfl)
theorem e6159 : o2.mul b5880 b63=b5881 := @mul_cons V1 _ o1 b304 b5882 b63 b5883 b5912 b5913 b5881 e6152 e6155 (by rfl) e6158
theorem e6160 : o1.mul b303 b62=b5326 := by decide
theorem e6161 : o1.scale b303 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6162 : o1.scale b303 b63=b5914 := @scale_cons V1 _ o1 b303 b62 b5326 (List.nil : V2) (List.nil : V2) b5914 e6160 e6161 (by rfl)
theorem e6163 : o1.add b5326 (List.nil : V1)=b5326 := by rfl
theorem e6164 : o2.add (List.nil : V2) b5881=b5881 := by rfl
theorem e6165 : o2.add b5914 b5915=b5879 := @add_cons V1 _ o1 b5326 (List.nil : V1) b5326 (List.nil : V2) b5881 b5881 b5879 e6163 e6164 (by rfl)
theorem e6166 : o2.mul b5878 b63=b5879 := @mul_cons V1 _ o1 b303 b5880 b63 b5881 b5914 b5915 b5879 e6159 e6162 (by rfl) e6165
theorem e6167 : o1.mul b302 b62=b5325 := by decide
theorem e6168 : o1.scale b302 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6169 : o1.scale b302 b63=b5916 := @scale_cons V1 _ o1 b302 b62 b5325 (List.nil : V2) (List.nil : V2) b5916 e6167 e6168 (by rfl)
theorem e6170 : o1.add b5325 (List.nil : V1)=b5325 := by rfl
theorem e6171 : o2.add (List.nil : V2) b5879=b5879 := by rfl
theorem e6172 : o2.add b5916 b5917=b5877 := @add_cons V1 _ o1 b5325 (List.nil : V1) b5325 (List.nil : V2) b5879 b5879 b5877 e6170 e6171 (by rfl)
theorem e6173 : o2.mul b5876 b63=b5877 := @mul_cons V1 _ o1 b302 b5878 b63 b5879 b5916 b5917 b5877 e6166 e6169 (by rfl) e6172
theorem e6174 : o1.mul b301 b62=b5324 := by decide
theorem e6175 : o1.scale b301 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e6176 : o1.scale b301 b63=b5918 := @scale_cons V1 _ o1 b301 b62 b5324 (List.nil : V2) (List.nil : V2) b5918 e6174 e6175 (by rfl)
theorem e6177 : o1.add b5324 (List.nil : V1)=b5324 := by rfl
theorem e6178 : o2.add (List.nil : V2) b5877=b5877 := by rfl
theorem e6179 : o2.add b5918 b5919=b5875 := @add_cons V1 _ o1 b5324 (List.nil : V1) b5324 (List.nil : V2) b5877 b5877 b5875 e6177 e6178 (by rfl)
theorem e6180 : o2.mul b5874 b63=b5875 := @mul_cons V1 _ o1 b301 b5876 b63 b5877 b5918 b5919 b5875 e6173 e6176 (by rfl) e6179
theorem e6181 : o2.add (List.nil : V2) b5873=b5873 := by rfl
theorem e6182 : o2.mul b5872 b63=b5873 := @mul_cons V1 _ o1 (List.nil : V1) b5874 b63 b5875 (List.nil : V2) b5873 b5873 e6180 e5463 (by rfl) e6181
theorem e6183 : o2.add (List.nil : V2) b5871=b5871 := by rfl
theorem e6184 : o2.mul b5870 b63=b5871 := @mul_cons V1 _ o1 (List.nil : V1) b5872 b63 b5873 (List.nil : V2) b5871 b5871 e6182 e5463 (by rfl) e6183
theorem e6185 : o2.add (List.nil : V2) b5869=b5869 := by rfl
theorem e6186 : o2.mul b5868 b63=b5869 := @mul_cons V1 _ o1 (List.nil : V1) b5870 b63 b5871 (List.nil : V2) b5869 b5869 e6184 e5463 (by rfl) e6185
theorem e6187 : o2.add (List.nil : V2) b5336=b5336 := by rfl
theorem e6188 : o2.mul b313 b63=b5336 := @mul_cons V1 _ o1 (List.nil : V1) b5868 b63 b5869 (List.nil : V2) b5336 b5336 e6186 e5463 (by rfl) e6187
theorem e6189 : o1.mul b312 b64=b5841 := by decide
theorem e6190 : o1.scale b312 b65=b5935 := @scale_cons V1 _ o1 b312 b64 b5841 (List.nil : V2) (List.nil : V2) b5935 e6189 e6100 (by rfl)
theorem e6191 : o2.add b5935 (List.nil : V2)=b5935 := by rfl
theorem e6192 : o2.mul b5896 b65=b5935 := @mul_cons V1 _ o1 b312 (List.nil : V2) b65 (List.nil : V2) b5935 (List.nil : V2) b5935 e5476 e6190 (by rfl) e6191
theorem e6193 : o1.mul b311 b64=b5840 := by decide
theorem e6194 : o1.scale b311 b65=b5936 := @scale_cons V1 _ o1 b311 b64 b5840 (List.nil : V2) (List.nil : V2) b5936 e6193 e6105 (by rfl)
theorem e6195 : o1.add b5840 (List.nil : V1)=b5840 := by rfl
theorem e6196 : o2.add (List.nil : V2) b5935=b5935 := by rfl
theorem e6197 : o2.add b5936 b5937=b5934 := @add_cons V1 _ o1 b5840 (List.nil : V1) b5840 (List.nil : V2) b5935 b5935 b5934 e6195 e6196 (by rfl)
theorem e6198 : o2.mul b5894 b65=b5934 := @mul_cons V1 _ o1 b311 b5896 b65 b5935 b5936 b5937 b5934 e6192 e6194 (by rfl) e6197
theorem e6199 : o1.mul b310 b64=b5839 := by decide
theorem e6200 : o1.scale b310 b65=b5938 := @scale_cons V1 _ o1 b310 b64 b5839 (List.nil : V2) (List.nil : V2) b5938 e6199 e6112 (by rfl)
theorem e6201 : o1.add b5839 (List.nil : V1)=b5839 := by rfl
theorem e6202 : o2.add (List.nil : V2) b5934=b5934 := by rfl
theorem e6203 : o2.add b5938 b5939=b5933 := @add_cons V1 _ o1 b5839 (List.nil : V1) b5839 (List.nil : V2) b5934 b5934 b5933 e6201 e6202 (by rfl)
theorem e6204 : o2.mul b5892 b65=b5933 := @mul_cons V1 _ o1 b310 b5894 b65 b5934 b5938 b5939 b5933 e6198 e6200 (by rfl) e6203
theorem e6205 : o1.mul b309 b64=b5838 := by decide
theorem e6206 : o1.scale b309 b65=b5940 := @scale_cons V1 _ o1 b309 b64 b5838 (List.nil : V2) (List.nil : V2) b5940 e6205 e6119 (by rfl)
theorem e6207 : o1.add b5838 (List.nil : V1)=b5838 := by rfl
theorem e6208 : o2.add (List.nil : V2) b5933=b5933 := by rfl
theorem e6209 : o2.add b5940 b5941=b5932 := @add_cons V1 _ o1 b5838 (List.nil : V1) b5838 (List.nil : V2) b5933 b5933 b5932 e6207 e6208 (by rfl)
theorem e6210 : o2.mul b5890 b65=b5932 := @mul_cons V1 _ o1 b309 b5892 b65 b5933 b5940 b5941 b5932 e6204 e6206 (by rfl) e6209
theorem e6211 : o1.mul b308 b64=b5837 := by decide
theorem e6212 : o1.scale b308 b65=b5942 := @scale_cons V1 _ o1 b308 b64 b5837 (List.nil : V2) (List.nil : V2) b5942 e6211 e6126 (by rfl)
theorem e6213 : o1.add b5837 (List.nil : V1)=b5837 := by rfl
theorem e6214 : o2.add (List.nil : V2) b5932=b5932 := by rfl
theorem e6215 : o2.add b5942 b5943=b5931 := @add_cons V1 _ o1 b5837 (List.nil : V1) b5837 (List.nil : V2) b5932 b5932 b5931 e6213 e6214 (by rfl)
theorem e6216 : o2.mul b5888 b65=b5931 := @mul_cons V1 _ o1 b308 b5890 b65 b5932 b5942 b5943 b5931 e6210 e6212 (by rfl) e6215
theorem e6217 : o1.mul b307 b64=b5836 := by decide
theorem e6218 : o1.scale b307 b65=b5944 := @scale_cons V1 _ o1 b307 b64 b5836 (List.nil : V2) (List.nil : V2) b5944 e6217 e6133 (by rfl)
theorem e6219 : o1.add b5836 (List.nil : V1)=b5836 := by rfl
theorem e6220 : o2.add (List.nil : V2) b5931=b5931 := by rfl
theorem e6221 : o2.add b5944 b5945=b5930 := @add_cons V1 _ o1 b5836 (List.nil : V1) b5836 (List.nil : V2) b5931 b5931 b5930 e6219 e6220 (by rfl)
theorem e6222 : o2.mul b5886 b65=b5930 := @mul_cons V1 _ o1 b307 b5888 b65 b5931 b5944 b5945 b5930 e6216 e6218 (by rfl) e6221
theorem e6223 : o1.mul b306 b64=b5835 := by decide
theorem e6224 : o1.scale b306 b65=b5946 := @scale_cons V1 _ o1 b306 b64 b5835 (List.nil : V2) (List.nil : V2) b5946 e6223 e6140 (by rfl)
theorem e6225 : o1.add b5835 (List.nil : V1)=b5835 := by rfl
theorem e6226 : o2.add (List.nil : V2) b5930=b5930 := by rfl
theorem e6227 : o2.add b5946 b5947=b5929 := @add_cons V1 _ o1 b5835 (List.nil : V1) b5835 (List.nil : V2) b5930 b5930 b5929 e6225 e6226 (by rfl)
theorem e6228 : o2.mul b5884 b65=b5929 := @mul_cons V1 _ o1 b306 b5886 b65 b5930 b5946 b5947 b5929 e6222 e6224 (by rfl) e6227
theorem e6229 : o1.mul b305 b64=b5834 := by decide
theorem e6230 : o1.scale b305 b65=b5948 := @scale_cons V1 _ o1 b305 b64 b5834 (List.nil : V2) (List.nil : V2) b5948 e6229 e6147 (by rfl)
theorem e6231 : o1.add b5834 (List.nil : V1)=b5834 := by rfl
theorem e6232 : o2.add (List.nil : V2) b5929=b5929 := by rfl
theorem e6233 : o2.add b5948 b5949=b5928 := @add_cons V1 _ o1 b5834 (List.nil : V1) b5834 (List.nil : V2) b5929 b5929 b5928 e6231 e6232 (by rfl)
theorem e6234 : o2.mul b5882 b65=b5928 := @mul_cons V1 _ o1 b305 b5884 b65 b5929 b5948 b5949 b5928 e6228 e6230 (by rfl) e6233
theorem e6235 : o1.mul b304 b64=b5833 := by decide
theorem e6236 : o1.scale b304 b65=b5950 := @scale_cons V1 _ o1 b304 b64 b5833 (List.nil : V2) (List.nil : V2) b5950 e6235 e6154 (by rfl)
theorem e6237 : o1.add b5833 (List.nil : V1)=b5833 := by rfl
theorem e6238 : o2.add (List.nil : V2) b5928=b5928 := by rfl
theorem e6239 : o2.add b5950 b5951=b5927 := @add_cons V1 _ o1 b5833 (List.nil : V1) b5833 (List.nil : V2) b5928 b5928 b5927 e6237 e6238 (by rfl)
theorem e6240 : o2.mul b5880 b65=b5927 := @mul_cons V1 _ o1 b304 b5882 b65 b5928 b5950 b5951 b5927 e6234 e6236 (by rfl) e6239
theorem e6241 : o1.mul b303 b64=b5832 := by decide
theorem e6242 : o1.scale b303 b65=b5952 := @scale_cons V1 _ o1 b303 b64 b5832 (List.nil : V2) (List.nil : V2) b5952 e6241 e6161 (by rfl)
theorem e6243 : o1.add b5832 (List.nil : V1)=b5832 := by rfl
theorem e6244 : o2.add (List.nil : V2) b5927=b5927 := by rfl
theorem e6245 : o2.add b5952 b5953=b5926 := @add_cons V1 _ o1 b5832 (List.nil : V1) b5832 (List.nil : V2) b5927 b5927 b5926 e6243 e6244 (by rfl)
theorem e6246 : o2.mul b5878 b65=b5926 := @mul_cons V1 _ o1 b303 b5880 b65 b5927 b5952 b5953 b5926 e6240 e6242 (by rfl) e6245
theorem e6247 : o1.mul b302 b64=b5831 := by decide
theorem e6248 : o1.scale b302 b65=b5954 := @scale_cons V1 _ o1 b302 b64 b5831 (List.nil : V2) (List.nil : V2) b5954 e6247 e6168 (by rfl)
theorem e6249 : o1.add b5831 (List.nil : V1)=b5831 := by rfl
theorem e6250 : o2.add (List.nil : V2) b5926=b5926 := by rfl
theorem e6251 : o2.add b5954 b5955=b5925 := @add_cons V1 _ o1 b5831 (List.nil : V1) b5831 (List.nil : V2) b5926 b5926 b5925 e6249 e6250 (by rfl)
theorem e6252 : o2.mul b5876 b65=b5925 := @mul_cons V1 _ o1 b302 b5878 b65 b5926 b5954 b5955 b5925 e6246 e6248 (by rfl) e6251
theorem e6253 : o1.mul b301 b64=b5337 := by decide
theorem e6254 : o1.scale b301 b65=b5956 := @scale_cons V1 _ o1 b301 b64 b5337 (List.nil : V2) (List.nil : V2) b5956 e6253 e6175 (by rfl)
theorem e6255 : o1.add b5337 (List.nil : V1)=b5337 := by rfl
theorem e6256 : o2.add (List.nil : V2) b5925=b5925 := by rfl
theorem e6257 : o2.add b5956 b5957=b5924 := @add_cons V1 _ o1 b5337 (List.nil : V1) b5337 (List.nil : V2) b5925 b5925 b5924 e6255 e6256 (by rfl)
theorem e6258 : o2.mul b5874 b65=b5924 := @mul_cons V1 _ o1 b301 b5876 b65 b5925 b5956 b5957 b5924 e6252 e6254 (by rfl) e6257
theorem e6259 : o2.add (List.nil : V2) b5923=b5923 := by rfl
theorem e6260 : o2.mul b5872 b65=b5923 := @mul_cons V1 _ o1 (List.nil : V1) b5874 b65 b5924 (List.nil : V2) b5923 b5923 e6258 e5536 (by rfl) e6259
theorem e6261 : o2.add (List.nil : V2) b5922=b5922 := by rfl
theorem e6262 : o2.mul b5870 b65=b5922 := @mul_cons V1 _ o1 (List.nil : V1) b5872 b65 b5923 (List.nil : V2) b5922 b5922 e6260 e5536 (by rfl) e6261
theorem e6263 : o2.add (List.nil : V2) b5921=b5921 := by rfl
theorem e6264 : o2.mul b5868 b65=b5921 := @mul_cons V1 _ o1 (List.nil : V1) b5870 b65 b5922 (List.nil : V2) b5921 b5921 e6262 e5536 (by rfl) e6263
theorem e6265 : o2.add (List.nil : V2) b5842=b5842 := by rfl
theorem e6266 : o2.mul b313 b65=b5842 := @mul_cons V1 _ o1 (List.nil : V1) b5868 b65 b5921 (List.nil : V2) b5842 b5842 e6264 e5536 (by rfl) e6265
theorem e6267 : o1.mul b312 b66=b5853 := by decide
theorem e6268 : o1.scale b312 b67=b5973 := @scale_cons V1 _ o1 b312 b66 b5853 (List.nil : V2) (List.nil : V2) b5973 e6267 e6100 (by rfl)
theorem e6269 : o2.add b5973 (List.nil : V2)=b5973 := by rfl
theorem e6270 : o2.mul b5896 b67=b5973 := @mul_cons V1 _ o1 b312 (List.nil : V2) b67 (List.nil : V2) b5973 (List.nil : V2) b5973 e5549 e6268 (by rfl) e6269
theorem e6271 : o1.mul b311 b66=b5852 := by decide
theorem e6272 : o1.scale b311 b67=b5974 := @scale_cons V1 _ o1 b311 b66 b5852 (List.nil : V2) (List.nil : V2) b5974 e6271 e6105 (by rfl)
theorem e6273 : o1.add b5852 (List.nil : V1)=b5852 := by rfl
theorem e6274 : o2.add (List.nil : V2) b5973=b5973 := by rfl
theorem e6275 : o2.add b5974 b5975=b5972 := @add_cons V1 _ o1 b5852 (List.nil : V1) b5852 (List.nil : V2) b5973 b5973 b5972 e6273 e6274 (by rfl)
theorem e6276 : o2.mul b5894 b67=b5972 := @mul_cons V1 _ o1 b311 b5896 b67 b5973 b5974 b5975 b5972 e6270 e6272 (by rfl) e6275
theorem e6277 : o1.mul b310 b66=b5851 := by decide
theorem e6278 : o1.scale b310 b67=b5976 := @scale_cons V1 _ o1 b310 b66 b5851 (List.nil : V2) (List.nil : V2) b5976 e6277 e6112 (by rfl)
theorem e6279 : o1.add b5851 (List.nil : V1)=b5851 := by rfl
theorem e6280 : o2.add (List.nil : V2) b5972=b5972 := by rfl
theorem e6281 : o2.add b5976 b5977=b5971 := @add_cons V1 _ o1 b5851 (List.nil : V1) b5851 (List.nil : V2) b5972 b5972 b5971 e6279 e6280 (by rfl)
theorem e6282 : o2.mul b5892 b67=b5971 := @mul_cons V1 _ o1 b310 b5894 b67 b5972 b5976 b5977 b5971 e6276 e6278 (by rfl) e6281
theorem e6283 : o1.mul b309 b66=b5850 := by decide
theorem e6284 : o1.scale b309 b67=b5978 := @scale_cons V1 _ o1 b309 b66 b5850 (List.nil : V2) (List.nil : V2) b5978 e6283 e6119 (by rfl)
theorem e6285 : o1.add b5850 (List.nil : V1)=b5850 := by rfl
theorem e6286 : o2.add (List.nil : V2) b5971=b5971 := by rfl
theorem e6287 : o2.add b5978 b5979=b5970 := @add_cons V1 _ o1 b5850 (List.nil : V1) b5850 (List.nil : V2) b5971 b5971 b5970 e6285 e6286 (by rfl)
theorem e6288 : o2.mul b5890 b67=b5970 := @mul_cons V1 _ o1 b309 b5892 b67 b5971 b5978 b5979 b5970 e6282 e6284 (by rfl) e6287
theorem e6289 : o1.mul b308 b66=b5849 := by decide
theorem e6290 : o1.scale b308 b67=b5980 := @scale_cons V1 _ o1 b308 b66 b5849 (List.nil : V2) (List.nil : V2) b5980 e6289 e6126 (by rfl)
theorem e6291 : o1.add b5849 (List.nil : V1)=b5849 := by rfl
theorem e6292 : o2.add (List.nil : V2) b5970=b5970 := by rfl
theorem e6293 : o2.add b5980 b5981=b5969 := @add_cons V1 _ o1 b5849 (List.nil : V1) b5849 (List.nil : V2) b5970 b5970 b5969 e6291 e6292 (by rfl)
theorem e6294 : o2.mul b5888 b67=b5969 := @mul_cons V1 _ o1 b308 b5890 b67 b5970 b5980 b5981 b5969 e6288 e6290 (by rfl) e6293
theorem e6295 : o1.mul b307 b66=b5848 := by decide
theorem e6296 : o1.scale b307 b67=b5982 := @scale_cons V1 _ o1 b307 b66 b5848 (List.nil : V2) (List.nil : V2) b5982 e6295 e6133 (by rfl)
theorem e6297 : o1.add b5848 (List.nil : V1)=b5848 := by rfl
theorem e6298 : o2.add (List.nil : V2) b5969=b5969 := by rfl
theorem e6299 : o2.add b5982 b5983=b5968 := @add_cons V1 _ o1 b5848 (List.nil : V1) b5848 (List.nil : V2) b5969 b5969 b5968 e6297 e6298 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
