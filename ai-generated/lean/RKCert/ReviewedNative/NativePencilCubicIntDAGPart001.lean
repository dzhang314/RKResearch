module

public import RKCert.ReviewedNative.NativePencilCubicIntDAGData

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicIntDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e0 : o2.mul (List.nil : V2) b6=(List.nil : V2) := by rfl
theorem e1 : o1.mul b18 b0=b63 := by decide
theorem e2 : o1.mul b18 b1=b64 := by decide
theorem e3 : o1.mul b18 b2=b65 := by decide
theorem e4 : o1.mul b18 b3=b66 := by decide
theorem e5 : o1.mul b18 b4=b67 := by decide
theorem e6 : o1.mul b18 b5=b39 := by decide
theorem e7 : o1.scale b18 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e8 : o1.scale b18 b77=b78 := @scale_cons V1 _ o1 b18 b5 b39 (List.nil : V2) (List.nil : V2) b78 e6 e7 (by rfl)
theorem e9 : o1.scale b18 b75=b76 := @scale_cons V1 _ o1 b18 b4 b67 b77 b78 b76 e5 e8 (by rfl)
theorem e10 : o1.scale b18 b73=b74 := @scale_cons V1 _ o1 b18 b3 b66 b75 b76 b74 e4 e9 (by rfl)
theorem e11 : o1.scale b18 b71=b72 := @scale_cons V1 _ o1 b18 b2 b65 b73 b74 b72 e3 e10 (by rfl)
theorem e12 : o1.scale b18 b69=b70 := @scale_cons V1 _ o1 b18 b1 b64 b71 b72 b70 e2 e11 (by rfl)
theorem e13 : o1.scale b18 b6=b68 := @scale_cons V1 _ o1 b18 b0 b63 b69 b70 b68 e1 e12 (by rfl)
theorem e14 : o2.add b68 (List.nil : V2)=b68 := by rfl
theorem e15 : o2.mul b62 b6=b68 := @mul_cons V1 _ o1 b18 (List.nil : V2) b6 (List.nil : V2) b68 (List.nil : V2) b68 e0 e13 (by rfl) e14
theorem e16 : o1.mul b17 b0=b56 := by decide
theorem e17 : o1.mul b17 b1=b79 := by decide
theorem e18 : o1.mul b17 b2=b80 := by decide
theorem e19 : o1.mul b17 b3=b81 := by decide
theorem e20 : o1.mul b17 b4=b82 := by decide
theorem e21 : o1.mul b17 b5=b83 := by decide
theorem e22 : o1.scale b17 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e23 : o1.scale b17 b77=b89 := @scale_cons V1 _ o1 b17 b5 b83 (List.nil : V2) (List.nil : V2) b89 e21 e22 (by rfl)
theorem e24 : o1.scale b17 b75=b88 := @scale_cons V1 _ o1 b17 b4 b82 b77 b89 b88 e20 e23 (by rfl)
theorem e25 : o1.scale b17 b73=b87 := @scale_cons V1 _ o1 b17 b3 b81 b75 b88 b87 e19 e24 (by rfl)
theorem e26 : o1.scale b17 b71=b86 := @scale_cons V1 _ o1 b17 b2 b80 b73 b87 b86 e18 e25 (by rfl)
theorem e27 : o1.scale b17 b69=b85 := @scale_cons V1 _ o1 b17 b1 b79 b71 b86 b85 e17 e26 (by rfl)
theorem e28 : o1.scale b17 b6=b84 := @scale_cons V1 _ o1 b17 b0 b56 b69 b85 b84 e16 e27 (by rfl)
theorem e29 : o1.add b56 (List.nil : V1)=b56 := by rfl
theorem e30 : o1.add b79 b63=b57 := by decide
theorem e31 : o1.add b80 b64=b58 := by decide
theorem e32 : o1.add b81 b65=b59 := by decide
theorem e33 : o1.add b82 b66=b60 := by decide
theorem e34 : o1.add b83 b67=b38 := by decide
theorem e35 : o2.add (List.nil : V2) b78=b78 := by rfl
theorem e36 : o2.add b89 b76=b95 := @add_cons V1 _ o1 b83 b67 b38 (List.nil : V2) b78 b78 b95 e34 e35 (by rfl)
theorem e37 : o2.add b88 b74=b94 := @add_cons V1 _ o1 b82 b66 b60 b89 b76 b95 b94 e33 e36 (by rfl)
theorem e38 : o2.add b87 b72=b93 := @add_cons V1 _ o1 b81 b65 b59 b88 b74 b94 b93 e32 e37 (by rfl)
theorem e39 : o2.add b86 b70=b92 := @add_cons V1 _ o1 b80 b64 b58 b87 b72 b93 b92 e31 e38 (by rfl)
theorem e40 : o2.add b85 b68=b91 := @add_cons V1 _ o1 b79 b63 b57 b86 b70 b92 b91 e30 e39 (by rfl)
theorem e41 : o2.add b84 b90=b61 := @add_cons V1 _ o1 b56 (List.nil : V1) b56 b85 b68 b91 b61 e29 e40 (by rfl)
theorem e42 : o2.mul b55 b6=b61 := @mul_cons V1 _ o1 b17 b62 b6 b68 b84 b90 b61 e15 e28 (by rfl) e41
theorem e43 : o1.mul b16 b0=b49 := by decide
theorem e44 : o1.mul b16 b1=b96 := by decide
theorem e45 : o1.mul b16 b2=b97 := by decide
theorem e46 : o1.mul b16 b3=b98 := by decide
theorem e47 : o1.mul b16 b4=b99 := by decide
theorem e48 : o1.mul b16 b5=b100 := by decide
theorem e49 : o1.scale b16 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e50 : o1.scale b16 b77=b106 := @scale_cons V1 _ o1 b16 b5 b100 (List.nil : V2) (List.nil : V2) b106 e48 e49 (by rfl)
theorem e51 : o1.scale b16 b75=b105 := @scale_cons V1 _ o1 b16 b4 b99 b77 b106 b105 e47 e50 (by rfl)
theorem e52 : o1.scale b16 b73=b104 := @scale_cons V1 _ o1 b16 b3 b98 b75 b105 b104 e46 e51 (by rfl)
theorem e53 : o1.scale b16 b71=b103 := @scale_cons V1 _ o1 b16 b2 b97 b73 b104 b103 e45 e52 (by rfl)
theorem e54 : o1.scale b16 b69=b102 := @scale_cons V1 _ o1 b16 b1 b96 b71 b103 b102 e44 e53 (by rfl)
theorem e55 : o1.scale b16 b6=b101 := @scale_cons V1 _ o1 b16 b0 b49 b69 b102 b101 e43 e54 (by rfl)
theorem e56 : o1.add b49 (List.nil : V1)=b49 := by rfl
theorem e57 : o1.add b96 b56=b50 := by decide
theorem e58 : o1.add b97 b57=b51 := by decide
theorem e59 : o1.add b98 b58=b52 := by decide
theorem e60 : o1.add b99 b59=b53 := by decide
theorem e61 : o1.add b100 b60=b37 := by decide
theorem e62 : o2.add (List.nil : V2) b95=b95 := by rfl
theorem e63 : o2.add b106 b94=b112 := @add_cons V1 _ o1 b100 b60 b37 (List.nil : V2) b95 b95 b112 e61 e62 (by rfl)
theorem e64 : o2.add b105 b93=b111 := @add_cons V1 _ o1 b99 b59 b53 b106 b94 b112 b111 e60 e63 (by rfl)
theorem e65 : o2.add b104 b92=b110 := @add_cons V1 _ o1 b98 b58 b52 b105 b93 b111 b110 e59 e64 (by rfl)
theorem e66 : o2.add b103 b91=b109 := @add_cons V1 _ o1 b97 b57 b51 b104 b92 b110 b109 e58 e65 (by rfl)
theorem e67 : o2.add b102 b61=b108 := @add_cons V1 _ o1 b96 b56 b50 b103 b91 b109 b108 e57 e66 (by rfl)
theorem e68 : o2.add b101 b107=b54 := @add_cons V1 _ o1 b49 (List.nil : V1) b49 b102 b61 b108 b54 e56 e67 (by rfl)
theorem e69 : o2.mul b48 b6=b54 := @mul_cons V1 _ o1 b16 b55 b6 b61 b101 b107 b54 e42 e55 (by rfl) e68
theorem e70 : o1.mul b15 b0=b42 := by decide
theorem e71 : o1.mul b15 b1=b113 := by decide
theorem e72 : o1.mul b15 b2=b114 := by decide
theorem e73 : o1.mul b15 b3=b115 := by decide
theorem e74 : o1.mul b15 b4=b116 := by decide
theorem e75 : o1.mul b15 b5=b117 := by decide
theorem e76 : o1.scale b15 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e77 : o1.scale b15 b77=b123 := @scale_cons V1 _ o1 b15 b5 b117 (List.nil : V2) (List.nil : V2) b123 e75 e76 (by rfl)
theorem e78 : o1.scale b15 b75=b122 := @scale_cons V1 _ o1 b15 b4 b116 b77 b123 b122 e74 e77 (by rfl)
theorem e79 : o1.scale b15 b73=b121 := @scale_cons V1 _ o1 b15 b3 b115 b75 b122 b121 e73 e78 (by rfl)
theorem e80 : o1.scale b15 b71=b120 := @scale_cons V1 _ o1 b15 b2 b114 b73 b121 b120 e72 e79 (by rfl)
theorem e81 : o1.scale b15 b69=b119 := @scale_cons V1 _ o1 b15 b1 b113 b71 b120 b119 e71 e80 (by rfl)
theorem e82 : o1.scale b15 b6=b118 := @scale_cons V1 _ o1 b15 b0 b42 b69 b119 b118 e70 e81 (by rfl)
theorem e83 : o1.add b42 (List.nil : V1)=b42 := by rfl
theorem e84 : o1.add b113 b49=b43 := by decide
theorem e85 : o1.add b114 b50=b44 := by decide
theorem e86 : o1.add b115 b51=b45 := by decide
theorem e87 : o1.add b116 b52=b46 := by decide
theorem e88 : o1.add b117 b53=b36 := by decide
theorem e89 : o2.add (List.nil : V2) b112=b112 := by rfl
theorem e90 : o2.add b123 b111=b129 := @add_cons V1 _ o1 b117 b53 b36 (List.nil : V2) b112 b112 b129 e88 e89 (by rfl)
theorem e91 : o2.add b122 b110=b128 := @add_cons V1 _ o1 b116 b52 b46 b123 b111 b129 b128 e87 e90 (by rfl)
theorem e92 : o2.add b121 b109=b127 := @add_cons V1 _ o1 b115 b51 b45 b122 b110 b128 b127 e86 e91 (by rfl)
theorem e93 : o2.add b120 b108=b126 := @add_cons V1 _ o1 b114 b50 b44 b121 b109 b127 b126 e85 e92 (by rfl)
theorem e94 : o2.add b119 b54=b125 := @add_cons V1 _ o1 b113 b49 b43 b120 b108 b126 b125 e84 e93 (by rfl)
theorem e95 : o2.add b118 b124=b47 := @add_cons V1 _ o1 b42 (List.nil : V1) b42 b119 b54 b125 b47 e83 e94 (by rfl)
theorem e96 : o2.mul b41 b6=b47 := @mul_cons V1 _ o1 b15 b48 b6 b54 b118 b124 b47 e69 e82 (by rfl) e95
theorem e97 : o1.mul b14 b0=b30 := by decide
theorem e98 : o1.mul b14 b1=b130 := by decide
theorem e99 : o1.mul b14 b2=b131 := by decide

end RKResearch.Certified.Graded.NativePencilCubicIntDAG
