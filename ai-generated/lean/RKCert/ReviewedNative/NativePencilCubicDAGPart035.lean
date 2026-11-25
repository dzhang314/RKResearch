module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart034

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5100 : o3.mul b4398 b13=b4399 := @mul_cons V2 _ o2 b243 b4400 b13 b4401 b4630 b4854 b4399 e4834 e5096 (by rfl) e5099
theorem e5101 : o1.mul b231 b6=b4920 := by decide
theorem e5102 : o1.mul b231 b7=b4921 := by decide
theorem e5103 : o1.mul b231 b8=b4922 := by decide
theorem e5104 : o1.mul b231 b9=b4923 := by decide
theorem e5105 : o1.mul b231 b10=b4924 := by decide
theorem e5106 : o1.mul b231 b11=b4363 := by decide
theorem e5107 : o1.scale b231 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5108 : o1.scale b231 b4475=b4930 := @scale_cons V1 _ o1 b231 b11 b4363 (List.nil : V2) (List.nil : V2) b4930 e5106 e5107 (by rfl)
theorem e5109 : o1.scale b231 b4473=b4929 := @scale_cons V1 _ o1 b231 b10 b4924 b4475 b4930 b4929 e5105 e5108 (by rfl)
theorem e5110 : o1.scale b231 b4471=b4928 := @scale_cons V1 _ o1 b231 b9 b4923 b4473 b4929 b4928 e5104 e5109 (by rfl)
theorem e5111 : o1.scale b231 b4469=b4927 := @scale_cons V1 _ o1 b231 b8 b4922 b4471 b4928 b4927 e5103 e5110 (by rfl)
theorem e5112 : o1.scale b231 b4467=b4926 := @scale_cons V1 _ o1 b231 b7 b4921 b4469 b4927 b4926 e5102 e5111 (by rfl)
theorem e5113 : o1.scale b231 b12=b4925 := @scale_cons V1 _ o1 b231 b6 b4920 b4467 b4926 b4925 e5101 e5112 (by rfl)
theorem e5114 : o2.add b4925 (List.nil : V2)=b4925 := by rfl
theorem e5115 : o2.mul b4919 b12=b4925 := @mul_cons V1 _ o1 b231 (List.nil : V2) b12 (List.nil : V2) b4925 (List.nil : V2) b4925 e4558 e5113 (by rfl) e5114
theorem e5116 : o1.mul b230 b6=b4913 := by decide
theorem e5117 : o1.mul b230 b7=b4931 := by decide
theorem e5118 : o1.mul b230 b8=b4932 := by decide
theorem e5119 : o1.mul b230 b9=b4933 := by decide
theorem e5120 : o1.mul b230 b10=b4934 := by decide
theorem e5121 : o1.mul b230 b11=b4935 := by decide
theorem e5122 : o1.scale b230 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5123 : o1.scale b230 b4475=b4941 := @scale_cons V1 _ o1 b230 b11 b4935 (List.nil : V2) (List.nil : V2) b4941 e5121 e5122 (by rfl)
theorem e5124 : o1.scale b230 b4473=b4940 := @scale_cons V1 _ o1 b230 b10 b4934 b4475 b4941 b4940 e5120 e5123 (by rfl)
theorem e5125 : o1.scale b230 b4471=b4939 := @scale_cons V1 _ o1 b230 b9 b4933 b4473 b4940 b4939 e5119 e5124 (by rfl)
theorem e5126 : o1.scale b230 b4469=b4938 := @scale_cons V1 _ o1 b230 b8 b4932 b4471 b4939 b4938 e5118 e5125 (by rfl)
theorem e5127 : o1.scale b230 b4467=b4937 := @scale_cons V1 _ o1 b230 b7 b4931 b4469 b4938 b4937 e5117 e5126 (by rfl)
theorem e5128 : o1.scale b230 b12=b4936 := @scale_cons V1 _ o1 b230 b6 b4913 b4467 b4937 b4936 e5116 e5127 (by rfl)
theorem e5129 : o1.add b4913 (List.nil : V1)=b4913 := by rfl
theorem e5130 : o1.add b4931 b4920=b4914 := by decide
theorem e5131 : o1.add b4932 b4921=b4915 := by decide
theorem e5132 : o1.add b4933 b4922=b4916 := by decide
theorem e5133 : o1.add b4934 b4923=b4917 := by decide
theorem e5134 : o1.add b4935 b4924=b4362 := by decide
theorem e5135 : o2.add (List.nil : V2) b4930=b4930 := by rfl
theorem e5136 : o2.add b4941 b4929=b4947 := @add_cons V1 _ o1 b4935 b4924 b4362 (List.nil : V2) b4930 b4930 b4947 e5134 e5135 (by rfl)
theorem e5137 : o2.add b4940 b4928=b4946 := @add_cons V1 _ o1 b4934 b4923 b4917 b4941 b4929 b4947 b4946 e5133 e5136 (by rfl)
theorem e5138 : o2.add b4939 b4927=b4945 := @add_cons V1 _ o1 b4933 b4922 b4916 b4940 b4928 b4946 b4945 e5132 e5137 (by rfl)
theorem e5139 : o2.add b4938 b4926=b4944 := @add_cons V1 _ o1 b4932 b4921 b4915 b4939 b4927 b4945 b4944 e5131 e5138 (by rfl)
theorem e5140 : o2.add b4937 b4925=b4943 := @add_cons V1 _ o1 b4931 b4920 b4914 b4938 b4926 b4944 b4943 e5130 e5139 (by rfl)
theorem e5141 : o2.add b4936 b4942=b4918 := @add_cons V1 _ o1 b4913 (List.nil : V1) b4913 b4937 b4925 b4943 b4918 e5129 e5140 (by rfl)
theorem e5142 : o2.mul b4912 b12=b4918 := @mul_cons V1 _ o1 b230 b4919 b12 b4925 b4936 b4942 b4918 e5115 e5128 (by rfl) e5141
theorem e5143 : o1.mul b229 b6=b4906 := by decide
theorem e5144 : o1.mul b229 b7=b4948 := by decide
theorem e5145 : o1.mul b229 b8=b4949 := by decide
theorem e5146 : o1.mul b229 b9=b4950 := by decide
theorem e5147 : o1.mul b229 b10=b4951 := by decide
theorem e5148 : o1.mul b229 b11=b4952 := by decide
theorem e5149 : o1.scale b229 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5150 : o1.scale b229 b4475=b4958 := @scale_cons V1 _ o1 b229 b11 b4952 (List.nil : V2) (List.nil : V2) b4958 e5148 e5149 (by rfl)
theorem e5151 : o1.scale b229 b4473=b4957 := @scale_cons V1 _ o1 b229 b10 b4951 b4475 b4958 b4957 e5147 e5150 (by rfl)
theorem e5152 : o1.scale b229 b4471=b4956 := @scale_cons V1 _ o1 b229 b9 b4950 b4473 b4957 b4956 e5146 e5151 (by rfl)
theorem e5153 : o1.scale b229 b4469=b4955 := @scale_cons V1 _ o1 b229 b8 b4949 b4471 b4956 b4955 e5145 e5152 (by rfl)
theorem e5154 : o1.scale b229 b4467=b4954 := @scale_cons V1 _ o1 b229 b7 b4948 b4469 b4955 b4954 e5144 e5153 (by rfl)
theorem e5155 : o1.scale b229 b12=b4953 := @scale_cons V1 _ o1 b229 b6 b4906 b4467 b4954 b4953 e5143 e5154 (by rfl)
theorem e5156 : o1.add b4906 (List.nil : V1)=b4906 := by rfl
theorem e5157 : o1.add b4948 b4913=b4907 := by decide
theorem e5158 : o1.add b4949 b4914=b4908 := by decide
theorem e5159 : o1.add b4950 b4915=b4909 := by decide
theorem e5160 : o1.add b4951 b4916=b4910 := by decide
theorem e5161 : o1.add b4952 b4917=b4361 := by decide
theorem e5162 : o2.add (List.nil : V2) b4947=b4947 := by rfl
theorem e5163 : o2.add b4958 b4946=b4964 := @add_cons V1 _ o1 b4952 b4917 b4361 (List.nil : V2) b4947 b4947 b4964 e5161 e5162 (by rfl)
theorem e5164 : o2.add b4957 b4945=b4963 := @add_cons V1 _ o1 b4951 b4916 b4910 b4958 b4946 b4964 b4963 e5160 e5163 (by rfl)
theorem e5165 : o2.add b4956 b4944=b4962 := @add_cons V1 _ o1 b4950 b4915 b4909 b4957 b4945 b4963 b4962 e5159 e5164 (by rfl)
theorem e5166 : o2.add b4955 b4943=b4961 := @add_cons V1 _ o1 b4949 b4914 b4908 b4956 b4944 b4962 b4961 e5158 e5165 (by rfl)
theorem e5167 : o2.add b4954 b4918=b4960 := @add_cons V1 _ o1 b4948 b4913 b4907 b4955 b4943 b4961 b4960 e5157 e5166 (by rfl)
theorem e5168 : o2.add b4953 b4959=b4911 := @add_cons V1 _ o1 b4906 (List.nil : V1) b4906 b4954 b4918 b4960 b4911 e5156 e5167 (by rfl)
theorem e5169 : o2.mul b4905 b12=b4911 := @mul_cons V1 _ o1 b229 b4912 b12 b4918 b4953 b4959 b4911 e5142 e5155 (by rfl) e5168
theorem e5170 : o1.mul b228 b6=b4899 := by decide
theorem e5171 : o1.mul b228 b7=b4965 := by decide
theorem e5172 : o1.mul b228 b8=b4966 := by decide
theorem e5173 : o1.mul b228 b9=b4967 := by decide
theorem e5174 : o1.mul b228 b10=b4968 := by decide
theorem e5175 : o1.mul b228 b11=b4969 := by decide
theorem e5176 : o1.scale b228 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5177 : o1.scale b228 b4475=b4975 := @scale_cons V1 _ o1 b228 b11 b4969 (List.nil : V2) (List.nil : V2) b4975 e5175 e5176 (by rfl)
theorem e5178 : o1.scale b228 b4473=b4974 := @scale_cons V1 _ o1 b228 b10 b4968 b4475 b4975 b4974 e5174 e5177 (by rfl)
theorem e5179 : o1.scale b228 b4471=b4973 := @scale_cons V1 _ o1 b228 b9 b4967 b4473 b4974 b4973 e5173 e5178 (by rfl)
theorem e5180 : o1.scale b228 b4469=b4972 := @scale_cons V1 _ o1 b228 b8 b4966 b4471 b4973 b4972 e5172 e5179 (by rfl)
theorem e5181 : o1.scale b228 b4467=b4971 := @scale_cons V1 _ o1 b228 b7 b4965 b4469 b4972 b4971 e5171 e5180 (by rfl)
theorem e5182 : o1.scale b228 b12=b4970 := @scale_cons V1 _ o1 b228 b6 b4899 b4467 b4971 b4970 e5170 e5181 (by rfl)
theorem e5183 : o1.add b4899 (List.nil : V1)=b4899 := by rfl
theorem e5184 : o1.add b4965 b4906=b4900 := by decide
theorem e5185 : o1.add b4966 b4907=b4901 := by decide
theorem e5186 : o1.add b4967 b4908=b4902 := by decide
theorem e5187 : o1.add b4968 b4909=b4903 := by decide
theorem e5188 : o1.add b4969 b4910=b4360 := by decide
theorem e5189 : o2.add (List.nil : V2) b4964=b4964 := by rfl
theorem e5190 : o2.add b4975 b4963=b4981 := @add_cons V1 _ o1 b4969 b4910 b4360 (List.nil : V2) b4964 b4964 b4981 e5188 e5189 (by rfl)
theorem e5191 : o2.add b4974 b4962=b4980 := @add_cons V1 _ o1 b4968 b4909 b4903 b4975 b4963 b4981 b4980 e5187 e5190 (by rfl)
theorem e5192 : o2.add b4973 b4961=b4979 := @add_cons V1 _ o1 b4967 b4908 b4902 b4974 b4962 b4980 b4979 e5186 e5191 (by rfl)
theorem e5193 : o2.add b4972 b4960=b4978 := @add_cons V1 _ o1 b4966 b4907 b4901 b4973 b4961 b4979 b4978 e5185 e5192 (by rfl)
theorem e5194 : o2.add b4971 b4911=b4977 := @add_cons V1 _ o1 b4965 b4906 b4900 b4972 b4960 b4978 b4977 e5184 e5193 (by rfl)
theorem e5195 : o2.add b4970 b4976=b4904 := @add_cons V1 _ o1 b4899 (List.nil : V1) b4899 b4971 b4911 b4977 b4904 e5183 e5194 (by rfl)
theorem e5196 : o2.mul b4898 b12=b4904 := @mul_cons V1 _ o1 b228 b4905 b12 b4911 b4970 b4976 b4904 e5169 e5182 (by rfl) e5195
theorem e5197 : o1.mul b227 b6=b4892 := by decide
theorem e5198 : o1.mul b227 b7=b4982 := by decide
theorem e5199 : o1.mul b227 b8=b4983 := by decide
theorem e5200 : o1.mul b227 b9=b4984 := by decide
theorem e5201 : o1.mul b227 b10=b4985 := by decide
theorem e5202 : o1.mul b227 b11=b4986 := by decide
theorem e5203 : o1.scale b227 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5204 : o1.scale b227 b4475=b4992 := @scale_cons V1 _ o1 b227 b11 b4986 (List.nil : V2) (List.nil : V2) b4992 e5202 e5203 (by rfl)
theorem e5205 : o1.scale b227 b4473=b4991 := @scale_cons V1 _ o1 b227 b10 b4985 b4475 b4992 b4991 e5201 e5204 (by rfl)
theorem e5206 : o1.scale b227 b4471=b4990 := @scale_cons V1 _ o1 b227 b9 b4984 b4473 b4991 b4990 e5200 e5205 (by rfl)
theorem e5207 : o1.scale b227 b4469=b4989 := @scale_cons V1 _ o1 b227 b8 b4983 b4471 b4990 b4989 e5199 e5206 (by rfl)
theorem e5208 : o1.scale b227 b4467=b4988 := @scale_cons V1 _ o1 b227 b7 b4982 b4469 b4989 b4988 e5198 e5207 (by rfl)
theorem e5209 : o1.scale b227 b12=b4987 := @scale_cons V1 _ o1 b227 b6 b4892 b4467 b4988 b4987 e5197 e5208 (by rfl)
theorem e5210 : o1.add b4892 (List.nil : V1)=b4892 := by rfl
theorem e5211 : o1.add b4982 b4899=b4893 := by decide
theorem e5212 : o1.add b4983 b4900=b4894 := by decide
theorem e5213 : o1.add b4984 b4901=b4895 := by decide
theorem e5214 : o1.add b4985 b4902=b4896 := by decide
theorem e5215 : o1.add b4986 b4903=b4359 := by decide
theorem e5216 : o2.add (List.nil : V2) b4981=b4981 := by rfl
theorem e5217 : o2.add b4992 b4980=b4998 := @add_cons V1 _ o1 b4986 b4903 b4359 (List.nil : V2) b4981 b4981 b4998 e5215 e5216 (by rfl)
theorem e5218 : o2.add b4991 b4979=b4997 := @add_cons V1 _ o1 b4985 b4902 b4896 b4992 b4980 b4998 b4997 e5214 e5217 (by rfl)
theorem e5219 : o2.add b4990 b4978=b4996 := @add_cons V1 _ o1 b4984 b4901 b4895 b4991 b4979 b4997 b4996 e5213 e5218 (by rfl)
theorem e5220 : o2.add b4989 b4977=b4995 := @add_cons V1 _ o1 b4983 b4900 b4894 b4990 b4978 b4996 b4995 e5212 e5219 (by rfl)
theorem e5221 : o2.add b4988 b4904=b4994 := @add_cons V1 _ o1 b4982 b4899 b4893 b4989 b4977 b4995 b4994 e5211 e5220 (by rfl)
theorem e5222 : o2.add b4987 b4993=b4897 := @add_cons V1 _ o1 b4892 (List.nil : V1) b4892 b4988 b4904 b4994 b4897 e5210 e5221 (by rfl)
theorem e5223 : o2.mul b4891 b12=b4897 := @mul_cons V1 _ o1 b227 b4898 b12 b4904 b4987 b4993 b4897 e5196 e5209 (by rfl) e5222
theorem e5224 : o1.mul b226 b6=b4885 := by decide
theorem e5225 : o1.mul b226 b7=b4999 := by decide
theorem e5226 : o1.mul b226 b8=b5000 := by decide
theorem e5227 : o1.mul b226 b9=b5001 := by decide
theorem e5228 : o1.mul b226 b10=b5002 := by decide
theorem e5229 : o1.mul b226 b11=b5003 := by decide
theorem e5230 : o1.scale b226 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5231 : o1.scale b226 b4475=b5009 := @scale_cons V1 _ o1 b226 b11 b5003 (List.nil : V2) (List.nil : V2) b5009 e5229 e5230 (by rfl)
theorem e5232 : o1.scale b226 b4473=b5008 := @scale_cons V1 _ o1 b226 b10 b5002 b4475 b5009 b5008 e5228 e5231 (by rfl)
theorem e5233 : o1.scale b226 b4471=b5007 := @scale_cons V1 _ o1 b226 b9 b5001 b4473 b5008 b5007 e5227 e5232 (by rfl)
theorem e5234 : o1.scale b226 b4469=b5006 := @scale_cons V1 _ o1 b226 b8 b5000 b4471 b5007 b5006 e5226 e5233 (by rfl)
theorem e5235 : o1.scale b226 b4467=b5005 := @scale_cons V1 _ o1 b226 b7 b4999 b4469 b5006 b5005 e5225 e5234 (by rfl)
theorem e5236 : o1.scale b226 b12=b5004 := @scale_cons V1 _ o1 b226 b6 b4885 b4467 b5005 b5004 e5224 e5235 (by rfl)
theorem e5237 : o1.add b4885 (List.nil : V1)=b4885 := by rfl
theorem e5238 : o1.add b4999 b4892=b4886 := by decide
theorem e5239 : o1.add b5000 b4893=b4887 := by decide
theorem e5240 : o1.add b5001 b4894=b4888 := by decide
theorem e5241 : o1.add b5002 b4895=b4889 := by decide
theorem e5242 : o1.add b5003 b4896=b4358 := by decide
theorem e5243 : o2.add (List.nil : V2) b4998=b4998 := by rfl
theorem e5244 : o2.add b5009 b4997=b5015 := @add_cons V1 _ o1 b5003 b4896 b4358 (List.nil : V2) b4998 b4998 b5015 e5242 e5243 (by rfl)
theorem e5245 : o2.add b5008 b4996=b5014 := @add_cons V1 _ o1 b5002 b4895 b4889 b5009 b4997 b5015 b5014 e5241 e5244 (by rfl)
theorem e5246 : o2.add b5007 b4995=b5013 := @add_cons V1 _ o1 b5001 b4894 b4888 b5008 b4996 b5014 b5013 e5240 e5245 (by rfl)
theorem e5247 : o2.add b5006 b4994=b5012 := @add_cons V1 _ o1 b5000 b4893 b4887 b5007 b4995 b5013 b5012 e5239 e5246 (by rfl)
theorem e5248 : o2.add b5005 b4897=b5011 := @add_cons V1 _ o1 b4999 b4892 b4886 b5006 b4994 b5012 b5011 e5238 e5247 (by rfl)
theorem e5249 : o2.add b5004 b5010=b4890 := @add_cons V1 _ o1 b4885 (List.nil : V1) b4885 b5005 b4897 b5011 b4890 e5237 e5248 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
