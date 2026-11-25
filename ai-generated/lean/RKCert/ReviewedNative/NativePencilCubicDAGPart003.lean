module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart002

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e300 : o1.mul b86 b29=b866 := by decide
theorem e301 : o1.mul b86 b30=b841 := by decide
theorem e302 : o1.mul b86 b31=b867 := by decide
theorem e303 : o1.mul b86 b32=b868 := by decide
theorem e304 : o1.mul b86 b33=b869 := by decide
theorem e305 : o1.scale b86 b864=b878 := @scale_cons V1 _ o1 b86 b33 b869 (List.nil : V2) (List.nil : V2) b878 e304 e26 (by rfl)
theorem e306 : o1.scale b86 b862=b877 := @scale_cons V1 _ o1 b86 b32 b868 b864 b878 b877 e303 e305 (by rfl)
theorem e307 : o1.scale b86 b860=b876 := @scale_cons V1 _ o1 b86 b31 b867 b862 b877 b876 e302 e306 (by rfl)
theorem e308 : o1.scale b86 b858=b875 := @scale_cons V1 _ o1 b86 b30 b841 b860 b876 b875 e301 e307 (by rfl)
theorem e309 : o1.scale b86 b856=b874 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b858 b875 b874 e19 e308 (by rfl)
theorem e310 : o1.scale b86 b854=b873 := @scale_cons V1 _ o1 b86 b29 b866 b856 b874 b873 e300 e309 (by rfl)
theorem e311 : o1.scale b86 b852=b872 := @scale_cons V1 _ o1 b86 b28 b839 b854 b873 b872 e299 e310 (by rfl)
theorem e312 : o1.scale b86 b850=b871 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b852 b872 b871 e19 e311 (by rfl)
theorem e313 : o1.scale b86 b34=b870 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b850 b871 b870 e19 e312 (by rfl)
theorem e314 : o1.add b839 (List.nil : V1)=b839 := by rfl
theorem e315 : o1.add b866 b845=b834 := by decide
theorem e316 : o1.add (List.nil : V1) b840=b840 := by rfl
theorem e317 : o1.add b841 (List.nil : V1)=b841 := by rfl
theorem e318 : o1.add b867 b846=b842 := by decide
theorem e319 : o1.add b868 b847=b843 := by decide
theorem e320 : o1.add b869 b848=b552 := by decide
theorem e321 : o2.add (List.nil : V2) b865=b865 := by rfl
theorem e322 : o2.add b878 b863=b887 := @add_cons V1 _ o1 b869 b848 b552 (List.nil : V2) b865 b865 b887 e320 e321 (by rfl)
theorem e323 : o2.add b877 b861=b886 := @add_cons V1 _ o1 b868 b847 b843 b878 b863 b887 b886 e319 e322 (by rfl)
theorem e324 : o2.add b876 b859=b885 := @add_cons V1 _ o1 b867 b846 b842 b877 b861 b886 b885 e318 e323 (by rfl)
theorem e325 : o2.add b875 b857=b884 := @add_cons V1 _ o1 b841 (List.nil : V1) b841 b876 b859 b885 b884 e317 e324 (by rfl)
theorem e326 : o2.add b874 b855=b883 := @add_cons V1 _ o1 (List.nil : V1) b840 b840 b875 b857 b884 b883 e316 e325 (by rfl)
theorem e327 : o2.add b873 b853=b882 := @add_cons V1 _ o1 b866 b845 b834 b874 b855 b883 b882 e315 e326 (by rfl)
theorem e328 : o2.add b872 b851=b881 := @add_cons V1 _ o1 b839 (List.nil : V1) b839 b873 b853 b882 b881 e314 e327 (by rfl)
theorem e329 : o2.add b871 b849=b880 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b872 b851 b881 b880 e34 e328 (by rfl)
theorem e330 : o2.add b870 b879=b844 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b871 b849 b880 b844 e34 e329 (by rfl)
theorem e331 : o2.mul b603 b34=b844 := @mul_cons V1 _ o1 b86 b610 b34 b849 b870 b879 b844 e298 e313 (by rfl) e330
theorem e332 : o1.mul b85 b28=b833 := by decide
theorem e333 : o1.mul b85 b29=b888 := by decide
theorem e334 : o1.mul b85 b30=b889 := by decide
theorem e335 : o1.mul b85 b31=b890 := by decide
theorem e336 : o1.mul b85 b32=b891 := by decide
theorem e337 : o1.mul b85 b33=b892 := by decide
theorem e338 : o1.scale b85 b864=b901 := @scale_cons V1 _ o1 b85 b33 b892 (List.nil : V2) (List.nil : V2) b901 e337 e57 (by rfl)
theorem e339 : o1.scale b85 b862=b900 := @scale_cons V1 _ o1 b85 b32 b891 b864 b901 b900 e336 e338 (by rfl)
theorem e340 : o1.scale b85 b860=b899 := @scale_cons V1 _ o1 b85 b31 b890 b862 b900 b899 e335 e339 (by rfl)
theorem e341 : o1.scale b85 b858=b898 := @scale_cons V1 _ o1 b85 b30 b889 b860 b899 b898 e334 e340 (by rfl)
theorem e342 : o1.scale b85 b856=b897 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b858 b898 b897 e50 e341 (by rfl)
theorem e343 : o1.scale b85 b854=b896 := @scale_cons V1 _ o1 b85 b29 b888 b856 b897 b896 e333 e342 (by rfl)
theorem e344 : o1.scale b85 b852=b895 := @scale_cons V1 _ o1 b85 b28 b833 b854 b896 b895 e332 e343 (by rfl)
theorem e345 : o1.scale b85 b850=b894 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b852 b895 b894 e50 e344 (by rfl)
theorem e346 : o1.scale b85 b34=b893 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b850 b894 b893 e50 e345 (by rfl)
theorem e347 : o1.add b833 (List.nil : V1)=b833 := by rfl
theorem e348 : o1.add b888 b839=b828 := by decide
theorem e349 : o1.add (List.nil : V1) b834=b834 := by rfl
theorem e350 : o1.add b889 b840=b835 := by decide
theorem e351 : o1.add b890 b841=b836 := by decide
theorem e352 : o1.add b891 b842=b837 := by decide
theorem e353 : o1.add b892 b843=b551 := by decide
theorem e354 : o2.add (List.nil : V2) b887=b887 := by rfl
theorem e355 : o2.add b901 b886=b910 := @add_cons V1 _ o1 b892 b843 b551 (List.nil : V2) b887 b887 b910 e353 e354 (by rfl)
theorem e356 : o2.add b900 b885=b909 := @add_cons V1 _ o1 b891 b842 b837 b901 b886 b910 b909 e352 e355 (by rfl)
theorem e357 : o2.add b899 b884=b908 := @add_cons V1 _ o1 b890 b841 b836 b900 b885 b909 b908 e351 e356 (by rfl)
theorem e358 : o2.add b898 b883=b907 := @add_cons V1 _ o1 b889 b840 b835 b899 b884 b908 b907 e350 e357 (by rfl)
theorem e359 : o2.add b897 b882=b906 := @add_cons V1 _ o1 (List.nil : V1) b834 b834 b898 b883 b907 b906 e349 e358 (by rfl)
theorem e360 : o2.add b896 b881=b905 := @add_cons V1 _ o1 b888 b839 b828 b897 b882 b906 b905 e348 e359 (by rfl)
theorem e361 : o2.add b895 b880=b904 := @add_cons V1 _ o1 b833 (List.nil : V1) b833 b896 b881 b905 b904 e347 e360 (by rfl)
theorem e362 : o2.add b894 b844=b903 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b895 b880 b904 b903 e34 e361 (by rfl)
theorem e363 : o2.add b893 b902=b838 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b894 b844 b903 b838 e34 e362 (by rfl)
theorem e364 : o2.mul b596 b34=b838 := @mul_cons V1 _ o1 b85 b603 b34 b844 b893 b902 b838 e331 e346 (by rfl) e363
theorem e365 : o1.mul b84 b28=b827 := by decide
theorem e366 : o1.mul b84 b29=b911 := by decide
theorem e367 : o1.mul b84 b30=b912 := by decide
theorem e368 : o1.mul b84 b31=b913 := by decide
theorem e369 : o1.mul b84 b32=b914 := by decide
theorem e370 : o1.mul b84 b33=b915 := by decide
theorem e371 : o1.scale b84 b864=b924 := @scale_cons V1 _ o1 b84 b33 b915 (List.nil : V2) (List.nil : V2) b924 e370 e87 (by rfl)
theorem e372 : o1.scale b84 b862=b923 := @scale_cons V1 _ o1 b84 b32 b914 b864 b924 b923 e369 e371 (by rfl)
theorem e373 : o1.scale b84 b860=b922 := @scale_cons V1 _ o1 b84 b31 b913 b862 b923 b922 e368 e372 (by rfl)
theorem e374 : o1.scale b84 b858=b921 := @scale_cons V1 _ o1 b84 b30 b912 b860 b922 b921 e367 e373 (by rfl)
theorem e375 : o1.scale b84 b856=b920 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b858 b921 b920 e80 e374 (by rfl)
theorem e376 : o1.scale b84 b854=b919 := @scale_cons V1 _ o1 b84 b29 b911 b856 b920 b919 e366 e375 (by rfl)
theorem e377 : o1.scale b84 b852=b918 := @scale_cons V1 _ o1 b84 b28 b827 b854 b919 b918 e365 e376 (by rfl)
theorem e378 : o1.scale b84 b850=b917 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b852 b918 b917 e80 e377 (by rfl)
theorem e379 : o1.scale b84 b34=b916 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b850 b917 b916 e80 e378 (by rfl)
theorem e380 : o1.add b827 (List.nil : V1)=b827 := by rfl
theorem e381 : o1.add b911 b833=b545 := by decide
theorem e382 : o1.add (List.nil : V1) b828=b828 := by rfl
theorem e383 : o1.add b912 b834=b829 := by decide
theorem e384 : o1.add b913 b835=b830 := by decide
theorem e385 : o1.add b914 b836=b831 := by decide
theorem e386 : o1.add b915 b837=b550 := by decide
theorem e387 : o2.add (List.nil : V2) b910=b910 := by rfl
theorem e388 : o2.add b924 b909=b933 := @add_cons V1 _ o1 b915 b837 b550 (List.nil : V2) b910 b910 b933 e386 e387 (by rfl)
theorem e389 : o2.add b923 b908=b932 := @add_cons V1 _ o1 b914 b836 b831 b924 b909 b933 b932 e385 e388 (by rfl)
theorem e390 : o2.add b922 b907=b931 := @add_cons V1 _ o1 b913 b835 b830 b923 b908 b932 b931 e384 e389 (by rfl)
theorem e391 : o2.add b921 b906=b930 := @add_cons V1 _ o1 b912 b834 b829 b922 b907 b931 b930 e383 e390 (by rfl)
theorem e392 : o2.add b920 b905=b929 := @add_cons V1 _ o1 (List.nil : V1) b828 b828 b921 b906 b930 b929 e382 e391 (by rfl)
theorem e393 : o2.add b919 b904=b928 := @add_cons V1 _ o1 b911 b833 b545 b920 b905 b929 b928 e381 e392 (by rfl)
theorem e394 : o2.add b918 b903=b927 := @add_cons V1 _ o1 b827 (List.nil : V1) b827 b919 b904 b928 b927 e380 e393 (by rfl)
theorem e395 : o2.add b917 b838=b926 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b918 b903 b927 b926 e34 e394 (by rfl)
theorem e396 : o2.add b916 b925=b832 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b917 b838 b926 b832 e34 e395 (by rfl)
theorem e397 : o2.mul b589 b34=b832 := @mul_cons V1 _ o1 b84 b596 b34 b838 b916 b925 b832 e364 e379 (by rfl) e396
theorem e398 : o1.mul b83 b28=b388 := by decide
theorem e399 : o1.mul b83 b29=b934 := by decide
theorem e400 : o1.mul b83 b30=b935 := by decide
theorem e401 : o1.mul b83 b31=b936 := by decide
theorem e402 : o1.mul b83 b32=b937 := by decide
theorem e403 : o1.mul b83 b33=b938 := by decide
theorem e404 : o1.scale b83 b864=b947 := @scale_cons V1 _ o1 b83 b33 b938 (List.nil : V2) (List.nil : V2) b947 e403 e117 (by rfl)
theorem e405 : o1.scale b83 b862=b946 := @scale_cons V1 _ o1 b83 b32 b937 b864 b947 b946 e402 e404 (by rfl)
theorem e406 : o1.scale b83 b860=b945 := @scale_cons V1 _ o1 b83 b31 b936 b862 b946 b945 e401 e405 (by rfl)
theorem e407 : o1.scale b83 b858=b944 := @scale_cons V1 _ o1 b83 b30 b935 b860 b945 b944 e400 e406 (by rfl)
theorem e408 : o1.scale b83 b856=b943 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b858 b944 b943 e110 e407 (by rfl)
theorem e409 : o1.scale b83 b854=b942 := @scale_cons V1 _ o1 b83 b29 b934 b856 b943 b942 e399 e408 (by rfl)
theorem e410 : o1.scale b83 b852=b941 := @scale_cons V1 _ o1 b83 b28 b388 b854 b942 b941 e398 e409 (by rfl)
theorem e411 : o1.scale b83 b850=b940 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b852 b941 b940 e110 e410 (by rfl)
theorem e412 : o1.scale b83 b34=b939 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b850 b940 b939 e110 e411 (by rfl)
theorem e413 : o1.add b388 (List.nil : V1)=b388 := by rfl
theorem e414 : o1.add b934 b827=b544 := by decide
theorem e415 : o1.add (List.nil : V1) b545=b545 := by rfl
theorem e416 : o1.add b935 b828=b546 := by decide
theorem e417 : o1.add b936 b829=b547 := by decide
theorem e418 : o1.add b937 b830=b548 := by decide
theorem e419 : o1.add b938 b831=b549 := by decide
theorem e420 : o2.add (List.nil : V2) b933=b933 := by rfl
theorem e421 : o2.add b947 b932=b956 := @add_cons V1 _ o1 b938 b831 b549 (List.nil : V2) b933 b933 b956 e419 e420 (by rfl)
theorem e422 : o2.add b946 b931=b955 := @add_cons V1 _ o1 b937 b830 b548 b947 b932 b956 b955 e418 e421 (by rfl)
theorem e423 : o2.add b945 b930=b954 := @add_cons V1 _ o1 b936 b829 b547 b946 b931 b955 b954 e417 e422 (by rfl)
theorem e424 : o2.add b944 b929=b953 := @add_cons V1 _ o1 b935 b828 b546 b945 b930 b954 b953 e416 e423 (by rfl)
theorem e425 : o2.add b943 b928=b952 := @add_cons V1 _ o1 (List.nil : V1) b545 b545 b944 b929 b953 b952 e415 e424 (by rfl)
theorem e426 : o2.add b942 b927=b951 := @add_cons V1 _ o1 b934 b827 b544 b943 b928 b952 b951 e414 e425 (by rfl)
theorem e427 : o2.add b941 b926=b950 := @add_cons V1 _ o1 b388 (List.nil : V1) b388 b942 b927 b951 b950 e413 e426 (by rfl)
theorem e428 : o2.add b940 b832=b949 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b941 b926 b950 b949 e34 e427 (by rfl)
theorem e429 : o2.add b939 b948=b554 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b940 b832 b949 b554 e34 e428 (by rfl)
theorem e430 : o2.mul b88 b34=b554 := @mul_cons V1 _ o1 b83 b589 b34 b832 b939 b948 b554 e397 e412 (by rfl) e429
theorem e431 : o2.mul (List.nil : V2) b41=(List.nil : V2) := by rfl
theorem e432 : o1.mul b87 b35=b977 := by decide
theorem e433 : o1.mul b87 b36=b978 := by decide
theorem e434 : o1.mul b87 b37=b973 := by decide
theorem e435 : o1.mul b87 b38=b979 := by decide
theorem e436 : o1.mul b87 b39=b980 := by decide
theorem e437 : o1.mul b87 b40=b564 := by decide
theorem e438 : o1.scale b87 b998=b999 := @scale_cons V1 _ o1 b87 b40 b564 (List.nil : V2) (List.nil : V2) b999 e437 e9 (by rfl)
theorem e439 : o1.scale b87 b996=b997 := @scale_cons V1 _ o1 b87 b39 b980 b998 b999 b997 e436 e438 (by rfl)
theorem e440 : o1.scale b87 b994=b995 := @scale_cons V1 _ o1 b87 b38 b979 b996 b997 b995 e435 e439 (by rfl)
theorem e441 : o1.scale b87 b992=b993 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b994 b995 b993 e2 e440 (by rfl)
theorem e442 : o1.scale b87 b990=b991 := @scale_cons V1 _ o1 b87 b37 b973 b992 b993 b991 e434 e441 (by rfl)
theorem e443 : o1.scale b87 b988=b989 := @scale_cons V1 _ o1 b87 b36 b978 b990 b991 b989 e433 e442 (by rfl)
theorem e444 : o1.scale b87 b986=b987 := @scale_cons V1 _ o1 b87 b35 b977 b988 b989 b987 e432 e443 (by rfl)
theorem e445 : o1.scale b87 b984=b985 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b986 b987 b985 e2 e444 (by rfl)
theorem e446 : o1.scale b87 b982=b983 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b984 b985 b983 e2 e445 (by rfl)
theorem e447 : o1.scale b87 b41=b981 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b982 b983 b981 e2 e446 (by rfl)
theorem e448 : o2.add b981 (List.nil : V2)=b981 := by rfl
theorem e449 : o2.mul b610 b41=b981 := @mul_cons V1 _ o1 b87 (List.nil : V2) b41 (List.nil : V2) b981 (List.nil : V2) b981 e431 e447 (by rfl) e448

end RKResearch.Certified.Graded.NativePencilCubicDAG
