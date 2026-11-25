module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart042

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e6300 : o2.mul b5886 b67=b5968 := @mul_cons V1 _ o1 b307 b5888 b67 b5969 b5982 b5983 b5968 e6294 e6296 (by rfl) e6299
theorem e6301 : o1.mul b306 b66=b5847 := by decide
theorem e6302 : o1.scale b306 b67=b5984 := @scale_cons V1 _ o1 b306 b66 b5847 (List.nil : V2) (List.nil : V2) b5984 e6301 e6140 (by rfl)
theorem e6303 : o1.add b5847 (List.nil : V1)=b5847 := by rfl
theorem e6304 : o2.add (List.nil : V2) b5968=b5968 := by rfl
theorem e6305 : o2.add b5984 b5985=b5967 := @add_cons V1 _ o1 b5847 (List.nil : V1) b5847 (List.nil : V2) b5968 b5968 b5967 e6303 e6304 (by rfl)
theorem e6306 : o2.mul b5884 b67=b5967 := @mul_cons V1 _ o1 b306 b5886 b67 b5968 b5984 b5985 b5967 e6300 e6302 (by rfl) e6305
theorem e6307 : o1.mul b305 b66=b5846 := by decide
theorem e6308 : o1.scale b305 b67=b5986 := @scale_cons V1 _ o1 b305 b66 b5846 (List.nil : V2) (List.nil : V2) b5986 e6307 e6147 (by rfl)
theorem e6309 : o1.add b5846 (List.nil : V1)=b5846 := by rfl
theorem e6310 : o2.add (List.nil : V2) b5967=b5967 := by rfl
theorem e6311 : o2.add b5986 b5987=b5966 := @add_cons V1 _ o1 b5846 (List.nil : V1) b5846 (List.nil : V2) b5967 b5967 b5966 e6309 e6310 (by rfl)
theorem e6312 : o2.mul b5882 b67=b5966 := @mul_cons V1 _ o1 b305 b5884 b67 b5967 b5986 b5987 b5966 e6306 e6308 (by rfl) e6311
theorem e6313 : o1.mul b304 b66=b5845 := by decide
theorem e6314 : o1.scale b304 b67=b5988 := @scale_cons V1 _ o1 b304 b66 b5845 (List.nil : V2) (List.nil : V2) b5988 e6313 e6154 (by rfl)
theorem e6315 : o1.add b5845 (List.nil : V1)=b5845 := by rfl
theorem e6316 : o2.add (List.nil : V2) b5966=b5966 := by rfl
theorem e6317 : o2.add b5988 b5989=b5965 := @add_cons V1 _ o1 b5845 (List.nil : V1) b5845 (List.nil : V2) b5966 b5966 b5965 e6315 e6316 (by rfl)
theorem e6318 : o2.mul b5880 b67=b5965 := @mul_cons V1 _ o1 b304 b5882 b67 b5966 b5988 b5989 b5965 e6312 e6314 (by rfl) e6317
theorem e6319 : o1.mul b303 b66=b5844 := by decide
theorem e6320 : o1.scale b303 b67=b5990 := @scale_cons V1 _ o1 b303 b66 b5844 (List.nil : V2) (List.nil : V2) b5990 e6319 e6161 (by rfl)
theorem e6321 : o1.add b5844 (List.nil : V1)=b5844 := by rfl
theorem e6322 : o2.add (List.nil : V2) b5965=b5965 := by rfl
theorem e6323 : o2.add b5990 b5991=b5964 := @add_cons V1 _ o1 b5844 (List.nil : V1) b5844 (List.nil : V2) b5965 b5965 b5964 e6321 e6322 (by rfl)
theorem e6324 : o2.mul b5878 b67=b5964 := @mul_cons V1 _ o1 b303 b5880 b67 b5965 b5990 b5991 b5964 e6318 e6320 (by rfl) e6323
theorem e6325 : o1.mul b302 b66=b5843 := by decide
theorem e6326 : o1.scale b302 b67=b5992 := @scale_cons V1 _ o1 b302 b66 b5843 (List.nil : V2) (List.nil : V2) b5992 e6325 e6168 (by rfl)
theorem e6327 : o1.add b5843 (List.nil : V1)=b5843 := by rfl
theorem e6328 : o2.add (List.nil : V2) b5964=b5964 := by rfl
theorem e6329 : o2.add b5992 b5993=b5963 := @add_cons V1 _ o1 b5843 (List.nil : V1) b5843 (List.nil : V2) b5964 b5964 b5963 e6327 e6328 (by rfl)
theorem e6330 : o2.mul b5876 b67=b5963 := @mul_cons V1 _ o1 b302 b5878 b67 b5964 b5992 b5993 b5963 e6324 e6326 (by rfl) e6329
theorem e6331 : o1.mul b301 b66=b5350 := by decide
theorem e6332 : o1.scale b301 b67=b5994 := @scale_cons V1 _ o1 b301 b66 b5350 (List.nil : V2) (List.nil : V2) b5994 e6331 e6175 (by rfl)
theorem e6333 : o1.add b5350 (List.nil : V1)=b5350 := by rfl
theorem e6334 : o2.add (List.nil : V2) b5963=b5963 := by rfl
theorem e6335 : o2.add b5994 b5995=b5962 := @add_cons V1 _ o1 b5350 (List.nil : V1) b5350 (List.nil : V2) b5963 b5963 b5962 e6333 e6334 (by rfl)
theorem e6336 : o2.mul b5874 b67=b5962 := @mul_cons V1 _ o1 b301 b5876 b67 b5963 b5994 b5995 b5962 e6330 e6332 (by rfl) e6335
theorem e6337 : o2.add (List.nil : V2) b5961=b5961 := by rfl
theorem e6338 : o2.mul b5872 b67=b5961 := @mul_cons V1 _ o1 (List.nil : V1) b5874 b67 b5962 (List.nil : V2) b5961 b5961 e6336 e5609 (by rfl) e6337
theorem e6339 : o2.add (List.nil : V2) b5960=b5960 := by rfl
theorem e6340 : o2.mul b5870 b67=b5960 := @mul_cons V1 _ o1 (List.nil : V1) b5872 b67 b5961 (List.nil : V2) b5960 b5960 e6338 e5609 (by rfl) e6339
theorem e6341 : o2.add (List.nil : V2) b5959=b5959 := by rfl
theorem e6342 : o2.mul b5868 b67=b5959 := @mul_cons V1 _ o1 (List.nil : V1) b5870 b67 b5960 (List.nil : V2) b5959 b5959 e6340 e5609 (by rfl) e6341
theorem e6343 : o2.add (List.nil : V2) b5854=b5854 := by rfl
theorem e6344 : o2.mul b313 b67=b5854 := @mul_cons V1 _ o1 (List.nil : V1) b5868 b67 b5959 (List.nil : V2) b5854 b5854 e6342 e5609 (by rfl) e6343
theorem e6345 : o1.mul b312 b68=b5865 := by decide
theorem e6346 : o1.scale b312 b69=b6011 := @scale_cons V1 _ o1 b312 b68 b5865 (List.nil : V2) (List.nil : V2) b6011 e6345 e6100 (by rfl)
theorem e6347 : o2.add b6011 (List.nil : V2)=b6011 := by rfl
theorem e6348 : o2.mul b5896 b69=b6011 := @mul_cons V1 _ o1 b312 (List.nil : V2) b69 (List.nil : V2) b6011 (List.nil : V2) b6011 e5622 e6346 (by rfl) e6347
theorem e6349 : o1.mul b311 b68=b5864 := by decide
theorem e6350 : o1.scale b311 b69=b6012 := @scale_cons V1 _ o1 b311 b68 b5864 (List.nil : V2) (List.nil : V2) b6012 e6349 e6105 (by rfl)
theorem e6351 : o1.add b5864 (List.nil : V1)=b5864 := by rfl
theorem e6352 : o2.add (List.nil : V2) b6011=b6011 := by rfl
theorem e6353 : o2.add b6012 b6013=b6010 := @add_cons V1 _ o1 b5864 (List.nil : V1) b5864 (List.nil : V2) b6011 b6011 b6010 e6351 e6352 (by rfl)
theorem e6354 : o2.mul b5894 b69=b6010 := @mul_cons V1 _ o1 b311 b5896 b69 b6011 b6012 b6013 b6010 e6348 e6350 (by rfl) e6353
theorem e6355 : o1.mul b310 b68=b5863 := by decide
theorem e6356 : o1.scale b310 b69=b6014 := @scale_cons V1 _ o1 b310 b68 b5863 (List.nil : V2) (List.nil : V2) b6014 e6355 e6112 (by rfl)
theorem e6357 : o1.add b5863 (List.nil : V1)=b5863 := by rfl
theorem e6358 : o2.add (List.nil : V2) b6010=b6010 := by rfl
theorem e6359 : o2.add b6014 b6015=b6009 := @add_cons V1 _ o1 b5863 (List.nil : V1) b5863 (List.nil : V2) b6010 b6010 b6009 e6357 e6358 (by rfl)
theorem e6360 : o2.mul b5892 b69=b6009 := @mul_cons V1 _ o1 b310 b5894 b69 b6010 b6014 b6015 b6009 e6354 e6356 (by rfl) e6359
theorem e6361 : o1.mul b309 b68=b5862 := by decide
theorem e6362 : o1.scale b309 b69=b6016 := @scale_cons V1 _ o1 b309 b68 b5862 (List.nil : V2) (List.nil : V2) b6016 e6361 e6119 (by rfl)
theorem e6363 : o1.add b5862 (List.nil : V1)=b5862 := by rfl
theorem e6364 : o2.add (List.nil : V2) b6009=b6009 := by rfl
theorem e6365 : o2.add b6016 b6017=b6008 := @add_cons V1 _ o1 b5862 (List.nil : V1) b5862 (List.nil : V2) b6009 b6009 b6008 e6363 e6364 (by rfl)
theorem e6366 : o2.mul b5890 b69=b6008 := @mul_cons V1 _ o1 b309 b5892 b69 b6009 b6016 b6017 b6008 e6360 e6362 (by rfl) e6365
theorem e6367 : o1.mul b308 b68=b5861 := by decide
theorem e6368 : o1.scale b308 b69=b6018 := @scale_cons V1 _ o1 b308 b68 b5861 (List.nil : V2) (List.nil : V2) b6018 e6367 e6126 (by rfl)
theorem e6369 : o1.add b5861 (List.nil : V1)=b5861 := by rfl
theorem e6370 : o2.add (List.nil : V2) b6008=b6008 := by rfl
theorem e6371 : o2.add b6018 b6019=b6007 := @add_cons V1 _ o1 b5861 (List.nil : V1) b5861 (List.nil : V2) b6008 b6008 b6007 e6369 e6370 (by rfl)
theorem e6372 : o2.mul b5888 b69=b6007 := @mul_cons V1 _ o1 b308 b5890 b69 b6008 b6018 b6019 b6007 e6366 e6368 (by rfl) e6371
theorem e6373 : o1.mul b307 b68=b5860 := by decide
theorem e6374 : o1.scale b307 b69=b6020 := @scale_cons V1 _ o1 b307 b68 b5860 (List.nil : V2) (List.nil : V2) b6020 e6373 e6133 (by rfl)
theorem e6375 : o1.add b5860 (List.nil : V1)=b5860 := by rfl
theorem e6376 : o2.add (List.nil : V2) b6007=b6007 := by rfl
theorem e6377 : o2.add b6020 b6021=b6006 := @add_cons V1 _ o1 b5860 (List.nil : V1) b5860 (List.nil : V2) b6007 b6007 b6006 e6375 e6376 (by rfl)
theorem e6378 : o2.mul b5886 b69=b6006 := @mul_cons V1 _ o1 b307 b5888 b69 b6007 b6020 b6021 b6006 e6372 e6374 (by rfl) e6377
theorem e6379 : o1.mul b306 b68=b5859 := by decide
theorem e6380 : o1.scale b306 b69=b6022 := @scale_cons V1 _ o1 b306 b68 b5859 (List.nil : V2) (List.nil : V2) b6022 e6379 e6140 (by rfl)
theorem e6381 : o1.add b5859 (List.nil : V1)=b5859 := by rfl
theorem e6382 : o2.add (List.nil : V2) b6006=b6006 := by rfl
theorem e6383 : o2.add b6022 b6023=b6005 := @add_cons V1 _ o1 b5859 (List.nil : V1) b5859 (List.nil : V2) b6006 b6006 b6005 e6381 e6382 (by rfl)
theorem e6384 : o2.mul b5884 b69=b6005 := @mul_cons V1 _ o1 b306 b5886 b69 b6006 b6022 b6023 b6005 e6378 e6380 (by rfl) e6383
theorem e6385 : o1.mul b305 b68=b5858 := by decide
theorem e6386 : o1.scale b305 b69=b6024 := @scale_cons V1 _ o1 b305 b68 b5858 (List.nil : V2) (List.nil : V2) b6024 e6385 e6147 (by rfl)
theorem e6387 : o1.add b5858 (List.nil : V1)=b5858 := by rfl
theorem e6388 : o2.add (List.nil : V2) b6005=b6005 := by rfl
theorem e6389 : o2.add b6024 b6025=b6004 := @add_cons V1 _ o1 b5858 (List.nil : V1) b5858 (List.nil : V2) b6005 b6005 b6004 e6387 e6388 (by rfl)
theorem e6390 : o2.mul b5882 b69=b6004 := @mul_cons V1 _ o1 b305 b5884 b69 b6005 b6024 b6025 b6004 e6384 e6386 (by rfl) e6389
theorem e6391 : o1.mul b304 b68=b5857 := by decide
theorem e6392 : o1.scale b304 b69=b6026 := @scale_cons V1 _ o1 b304 b68 b5857 (List.nil : V2) (List.nil : V2) b6026 e6391 e6154 (by rfl)
theorem e6393 : o1.add b5857 (List.nil : V1)=b5857 := by rfl
theorem e6394 : o2.add (List.nil : V2) b6004=b6004 := by rfl
theorem e6395 : o2.add b6026 b6027=b6003 := @add_cons V1 _ o1 b5857 (List.nil : V1) b5857 (List.nil : V2) b6004 b6004 b6003 e6393 e6394 (by rfl)
theorem e6396 : o2.mul b5880 b69=b6003 := @mul_cons V1 _ o1 b304 b5882 b69 b6004 b6026 b6027 b6003 e6390 e6392 (by rfl) e6395
theorem e6397 : o1.mul b303 b68=b5856 := by decide
theorem e6398 : o1.scale b303 b69=b6028 := @scale_cons V1 _ o1 b303 b68 b5856 (List.nil : V2) (List.nil : V2) b6028 e6397 e6161 (by rfl)
theorem e6399 : o1.add b5856 (List.nil : V1)=b5856 := by rfl
theorem e6400 : o2.add (List.nil : V2) b6003=b6003 := by rfl
theorem e6401 : o2.add b6028 b6029=b6002 := @add_cons V1 _ o1 b5856 (List.nil : V1) b5856 (List.nil : V2) b6003 b6003 b6002 e6399 e6400 (by rfl)
theorem e6402 : o2.mul b5878 b69=b6002 := @mul_cons V1 _ o1 b303 b5880 b69 b6003 b6028 b6029 b6002 e6396 e6398 (by rfl) e6401
theorem e6403 : o1.mul b302 b68=b5855 := by decide
theorem e6404 : o1.scale b302 b69=b6030 := @scale_cons V1 _ o1 b302 b68 b5855 (List.nil : V2) (List.nil : V2) b6030 e6403 e6168 (by rfl)
theorem e6405 : o1.add b5855 (List.nil : V1)=b5855 := by rfl
theorem e6406 : o2.add (List.nil : V2) b6002=b6002 := by rfl
theorem e6407 : o2.add b6030 b6031=b6001 := @add_cons V1 _ o1 b5855 (List.nil : V1) b5855 (List.nil : V2) b6002 b6002 b6001 e6405 e6406 (by rfl)
theorem e6408 : o2.mul b5876 b69=b6001 := @mul_cons V1 _ o1 b302 b5878 b69 b6002 b6030 b6031 b6001 e6402 e6404 (by rfl) e6407
theorem e6409 : o1.mul b301 b68=b5195 := by decide
theorem e6410 : o1.scale b301 b69=b6032 := @scale_cons V1 _ o1 b301 b68 b5195 (List.nil : V2) (List.nil : V2) b6032 e6409 e6175 (by rfl)
theorem e6411 : o1.add b5195 (List.nil : V1)=b5195 := by rfl
theorem e6412 : o2.add (List.nil : V2) b6001=b6001 := by rfl
theorem e6413 : o2.add b6032 b6033=b6000 := @add_cons V1 _ o1 b5195 (List.nil : V1) b5195 (List.nil : V2) b6001 b6001 b6000 e6411 e6412 (by rfl)
theorem e6414 : o2.mul b5874 b69=b6000 := @mul_cons V1 _ o1 b301 b5876 b69 b6001 b6032 b6033 b6000 e6408 e6410 (by rfl) e6413
theorem e6415 : o2.add (List.nil : V2) b5999=b5999 := by rfl
theorem e6416 : o2.mul b5872 b69=b5999 := @mul_cons V1 _ o1 (List.nil : V1) b5874 b69 b6000 (List.nil : V2) b5999 b5999 e6414 e5682 (by rfl) e6415
theorem e6417 : o2.add (List.nil : V2) b5998=b5998 := by rfl
theorem e6418 : o2.mul b5870 b69=b5998 := @mul_cons V1 _ o1 (List.nil : V1) b5872 b69 b5999 (List.nil : V2) b5998 b5998 e6416 e5682 (by rfl) e6417
theorem e6419 : o2.add (List.nil : V2) b5997=b5997 := by rfl
theorem e6420 : o2.mul b5868 b69=b5997 := @mul_cons V1 _ o1 (List.nil : V1) b5870 b69 b5998 (List.nil : V2) b5997 b5997 e6418 e5682 (by rfl) e6419
theorem e6421 : o2.add (List.nil : V2) b5866=b5866 := by rfl
theorem e6422 : o2.mul b313 b69=b5866 := @mul_cons V1 _ o1 (List.nil : V1) b5868 b69 b5997 (List.nil : V2) b5866 b5866 e6420 e5682 (by rfl) e6421
theorem e6423 : o2.scale b313 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e6424 : o2.scale b313 b5555=b5996 := @scale_cons V2 _ o2 b313 b69 b5866 (List.nil : V3) (List.nil : V3) b5996 e6422 e6423 (by rfl)
theorem e6425 : o2.scale b313 b5520=b5958 := @scale_cons V2 _ o2 b313 b67 b5854 b5555 b5996 b5958 e6344 e6424 (by rfl)
theorem e6426 : o2.scale b313 b5485=b5920 := @scale_cons V2 _ o2 b313 b65 b5842 b5520 b5958 b5920 e6266 e6425 (by rfl)
theorem e6427 : o2.scale b313 b70=b5867 := @scale_cons V2 _ o2 b313 b63 b5336 b5485 b5920 b5867 e6188 e6426 (by rfl)
theorem e6428 : o2.add b5336 (List.nil : V2)=b5336 := by rfl
theorem e6429 : o1.add b5831 b5365=b5338 := by decide
theorem e6430 : o1.add b5832 b5366=b5339 := by decide
theorem e6431 : o1.add b5833 b5367=b5340 := by decide
theorem e6432 : o1.add b5834 b5368=b5341 := by decide
theorem e6433 : o1.add b5835 b5369=b5342 := by decide
theorem e6434 : o1.add b5836 b5370=b5343 := by decide
theorem e6435 : o1.add b5837 b5371=b5344 := by decide
theorem e6436 : o1.add b5838 b5372=b5345 := by decide
theorem e6437 : o1.add b5839 b5373=b5346 := by decide
theorem e6438 : o1.add b5840 b5374=b5347 := by decide
theorem e6439 : o1.add b5841 b5375=b5348 := by decide
theorem e6440 : o2.add b5935 b5653=b6050 := @add_cons V1 _ o1 b5841 b5375 b5348 (List.nil : V2) (List.nil : V2) (List.nil : V2) b6050 e6439 e2341 (by rfl)
theorem e6441 : o2.add b5934 b5651=b6049 := @add_cons V1 _ o1 b5840 b5374 b5347 b5935 b5653 b6050 b6049 e6438 e6440 (by rfl)
theorem e6442 : o2.add b5933 b5649=b6048 := @add_cons V1 _ o1 b5839 b5373 b5346 b5934 b5651 b6049 b6048 e6437 e6441 (by rfl)
theorem e6443 : o2.add b5932 b5647=b6047 := @add_cons V1 _ o1 b5838 b5372 b5345 b5933 b5649 b6048 b6047 e6436 e6442 (by rfl)
theorem e6444 : o2.add b5931 b5645=b6046 := @add_cons V1 _ o1 b5837 b5371 b5344 b5932 b5647 b6047 b6046 e6435 e6443 (by rfl)
theorem e6445 : o2.add b5930 b5643=b6045 := @add_cons V1 _ o1 b5836 b5370 b5343 b5931 b5645 b6046 b6045 e6434 e6444 (by rfl)
theorem e6446 : o2.add b5929 b5641=b6044 := @add_cons V1 _ o1 b5835 b5369 b5342 b5930 b5643 b6045 b6044 e6433 e6445 (by rfl)
theorem e6447 : o2.add b5928 b5639=b6043 := @add_cons V1 _ o1 b5834 b5368 b5341 b5929 b5641 b6044 b6043 e6432 e6446 (by rfl)
theorem e6448 : o2.add b5927 b5637=b6042 := @add_cons V1 _ o1 b5833 b5367 b5340 b5928 b5639 b6043 b6042 e6431 e6447 (by rfl)
theorem e6449 : o2.add b5926 b5635=b6041 := @add_cons V1 _ o1 b5832 b5366 b5339 b5927 b5637 b6042 b6041 e6430 e6448 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
