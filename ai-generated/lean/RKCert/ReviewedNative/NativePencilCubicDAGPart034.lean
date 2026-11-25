module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart033

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4950 : o2.add (List.nil : V2) b4751=b4751 := by rfl
theorem e4951 : o2.add b4762 b4750=b4768 := @add_cons V1 _ o1 b4756 b4673 b4375 (List.nil : V2) b4751 b4751 b4768 e4949 e4950 (by rfl)
theorem e4952 : o2.add b4761 b4749=b4767 := @add_cons V1 _ o1 b4755 b4672 b4666 b4762 b4750 b4768 b4767 e4948 e4951 (by rfl)
theorem e4953 : o2.add b4760 b4748=b4766 := @add_cons V1 _ o1 b4754 b4671 b4665 b4761 b4749 b4767 b4766 e4947 e4952 (by rfl)
theorem e4954 : o2.add b4759 b4747=b4765 := @add_cons V1 _ o1 b4753 b4670 b4664 b4760 b4748 b4766 b4765 e4946 e4953 (by rfl)
theorem e4955 : o2.add b4758 b4674=b4764 := @add_cons V1 _ o1 b4752 b4669 b4663 b4759 b4747 b4765 b4764 e4945 e4954 (by rfl)
theorem e4956 : o2.add b4757 b4763=b4667 := @add_cons V1 _ o1 b4662 (List.nil : V1) b4662 b4758 b4674 b4764 b4667 e4944 e4955 (by rfl)
theorem e4957 : o2.mul b4661 b12=b4667 := @mul_cons V1 _ o1 b238 b4668 b12 b4674 b4757 b4763 b4667 e4930 e4943 (by rfl) e4956
theorem e4958 : o1.mul b237 b6=b4655 := by decide
theorem e4959 : o1.mul b237 b7=b4769 := by decide
theorem e4960 : o1.mul b237 b8=b4770 := by decide
theorem e4961 : o1.mul b237 b9=b4771 := by decide
theorem e4962 : o1.mul b237 b10=b4772 := by decide
theorem e4963 : o1.mul b237 b11=b4773 := by decide
theorem e4964 : o1.scale b237 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4965 : o1.scale b237 b4475=b4779 := @scale_cons V1 _ o1 b237 b11 b4773 (List.nil : V2) (List.nil : V2) b4779 e4963 e4964 (by rfl)
theorem e4966 : o1.scale b237 b4473=b4778 := @scale_cons V1 _ o1 b237 b10 b4772 b4475 b4779 b4778 e4962 e4965 (by rfl)
theorem e4967 : o1.scale b237 b4471=b4777 := @scale_cons V1 _ o1 b237 b9 b4771 b4473 b4778 b4777 e4961 e4966 (by rfl)
theorem e4968 : o1.scale b237 b4469=b4776 := @scale_cons V1 _ o1 b237 b8 b4770 b4471 b4777 b4776 e4960 e4967 (by rfl)
theorem e4969 : o1.scale b237 b4467=b4775 := @scale_cons V1 _ o1 b237 b7 b4769 b4469 b4776 b4775 e4959 e4968 (by rfl)
theorem e4970 : o1.scale b237 b12=b4774 := @scale_cons V1 _ o1 b237 b6 b4655 b4467 b4775 b4774 e4958 e4969 (by rfl)
theorem e4971 : o1.add b4655 (List.nil : V1)=b4655 := by rfl
theorem e4972 : o1.add b4769 b4662=b4656 := by decide
theorem e4973 : o1.add b4770 b4663=b4657 := by decide
theorem e4974 : o1.add b4771 b4664=b4658 := by decide
theorem e4975 : o1.add b4772 b4665=b4659 := by decide
theorem e4976 : o1.add b4773 b4666=b4374 := by decide
theorem e4977 : o2.add (List.nil : V2) b4768=b4768 := by rfl
theorem e4978 : o2.add b4779 b4767=b4785 := @add_cons V1 _ o1 b4773 b4666 b4374 (List.nil : V2) b4768 b4768 b4785 e4976 e4977 (by rfl)
theorem e4979 : o2.add b4778 b4766=b4784 := @add_cons V1 _ o1 b4772 b4665 b4659 b4779 b4767 b4785 b4784 e4975 e4978 (by rfl)
theorem e4980 : o2.add b4777 b4765=b4783 := @add_cons V1 _ o1 b4771 b4664 b4658 b4778 b4766 b4784 b4783 e4974 e4979 (by rfl)
theorem e4981 : o2.add b4776 b4764=b4782 := @add_cons V1 _ o1 b4770 b4663 b4657 b4777 b4765 b4783 b4782 e4973 e4980 (by rfl)
theorem e4982 : o2.add b4775 b4667=b4781 := @add_cons V1 _ o1 b4769 b4662 b4656 b4776 b4764 b4782 b4781 e4972 e4981 (by rfl)
theorem e4983 : o2.add b4774 b4780=b4660 := @add_cons V1 _ o1 b4655 (List.nil : V1) b4655 b4775 b4667 b4781 b4660 e4971 e4982 (by rfl)
theorem e4984 : o2.mul b4654 b12=b4660 := @mul_cons V1 _ o1 b237 b4661 b12 b4667 b4774 b4780 b4660 e4957 e4970 (by rfl) e4983
theorem e4985 : o1.mul b236 b6=b4648 := by decide
theorem e4986 : o1.mul b236 b7=b4786 := by decide
theorem e4987 : o1.mul b236 b8=b4787 := by decide
theorem e4988 : o1.mul b236 b9=b4788 := by decide
theorem e4989 : o1.mul b236 b10=b4789 := by decide
theorem e4990 : o1.mul b236 b11=b4790 := by decide
theorem e4991 : o1.scale b236 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4992 : o1.scale b236 b4475=b4796 := @scale_cons V1 _ o1 b236 b11 b4790 (List.nil : V2) (List.nil : V2) b4796 e4990 e4991 (by rfl)
theorem e4993 : o1.scale b236 b4473=b4795 := @scale_cons V1 _ o1 b236 b10 b4789 b4475 b4796 b4795 e4989 e4992 (by rfl)
theorem e4994 : o1.scale b236 b4471=b4794 := @scale_cons V1 _ o1 b236 b9 b4788 b4473 b4795 b4794 e4988 e4993 (by rfl)
theorem e4995 : o1.scale b236 b4469=b4793 := @scale_cons V1 _ o1 b236 b8 b4787 b4471 b4794 b4793 e4987 e4994 (by rfl)
theorem e4996 : o1.scale b236 b4467=b4792 := @scale_cons V1 _ o1 b236 b7 b4786 b4469 b4793 b4792 e4986 e4995 (by rfl)
theorem e4997 : o1.scale b236 b12=b4791 := @scale_cons V1 _ o1 b236 b6 b4648 b4467 b4792 b4791 e4985 e4996 (by rfl)
theorem e4998 : o1.add b4648 (List.nil : V1)=b4648 := by rfl
theorem e4999 : o1.add b4786 b4655=b4649 := by decide
theorem e5000 : o1.add b4787 b4656=b4650 := by decide
theorem e5001 : o1.add b4788 b4657=b4651 := by decide
theorem e5002 : o1.add b4789 b4658=b4652 := by decide
theorem e5003 : o1.add b4790 b4659=b4373 := by decide
theorem e5004 : o2.add (List.nil : V2) b4785=b4785 := by rfl
theorem e5005 : o2.add b4796 b4784=b4802 := @add_cons V1 _ o1 b4790 b4659 b4373 (List.nil : V2) b4785 b4785 b4802 e5003 e5004 (by rfl)
theorem e5006 : o2.add b4795 b4783=b4801 := @add_cons V1 _ o1 b4789 b4658 b4652 b4796 b4784 b4802 b4801 e5002 e5005 (by rfl)
theorem e5007 : o2.add b4794 b4782=b4800 := @add_cons V1 _ o1 b4788 b4657 b4651 b4795 b4783 b4801 b4800 e5001 e5006 (by rfl)
theorem e5008 : o2.add b4793 b4781=b4799 := @add_cons V1 _ o1 b4787 b4656 b4650 b4794 b4782 b4800 b4799 e5000 e5007 (by rfl)
theorem e5009 : o2.add b4792 b4660=b4798 := @add_cons V1 _ o1 b4786 b4655 b4649 b4793 b4781 b4799 b4798 e4999 e5008 (by rfl)
theorem e5010 : o2.add b4791 b4797=b4653 := @add_cons V1 _ o1 b4648 (List.nil : V1) b4648 b4792 b4660 b4798 b4653 e4998 e5009 (by rfl)
theorem e5011 : o2.mul b4647 b12=b4653 := @mul_cons V1 _ o1 b236 b4654 b12 b4660 b4791 b4797 b4653 e4984 e4997 (by rfl) e5010
theorem e5012 : o1.mul b235 b6=b4641 := by decide
theorem e5013 : o1.mul b235 b7=b4803 := by decide
theorem e5014 : o1.mul b235 b8=b4804 := by decide
theorem e5015 : o1.mul b235 b9=b4805 := by decide
theorem e5016 : o1.mul b235 b10=b4806 := by decide
theorem e5017 : o1.mul b235 b11=b4807 := by decide
theorem e5018 : o1.scale b235 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5019 : o1.scale b235 b4475=b4813 := @scale_cons V1 _ o1 b235 b11 b4807 (List.nil : V2) (List.nil : V2) b4813 e5017 e5018 (by rfl)
theorem e5020 : o1.scale b235 b4473=b4812 := @scale_cons V1 _ o1 b235 b10 b4806 b4475 b4813 b4812 e5016 e5019 (by rfl)
theorem e5021 : o1.scale b235 b4471=b4811 := @scale_cons V1 _ o1 b235 b9 b4805 b4473 b4812 b4811 e5015 e5020 (by rfl)
theorem e5022 : o1.scale b235 b4469=b4810 := @scale_cons V1 _ o1 b235 b8 b4804 b4471 b4811 b4810 e5014 e5021 (by rfl)
theorem e5023 : o1.scale b235 b4467=b4809 := @scale_cons V1 _ o1 b235 b7 b4803 b4469 b4810 b4809 e5013 e5022 (by rfl)
theorem e5024 : o1.scale b235 b12=b4808 := @scale_cons V1 _ o1 b235 b6 b4641 b4467 b4809 b4808 e5012 e5023 (by rfl)
theorem e5025 : o1.add b4641 (List.nil : V1)=b4641 := by rfl
theorem e5026 : o1.add b4803 b4648=b4642 := by decide
theorem e5027 : o1.add b4804 b4649=b4643 := by decide
theorem e5028 : o1.add b4805 b4650=b4644 := by decide
theorem e5029 : o1.add b4806 b4651=b4645 := by decide
theorem e5030 : o1.add b4807 b4652=b4372 := by decide
theorem e5031 : o2.add (List.nil : V2) b4802=b4802 := by rfl
theorem e5032 : o2.add b4813 b4801=b4819 := @add_cons V1 _ o1 b4807 b4652 b4372 (List.nil : V2) b4802 b4802 b4819 e5030 e5031 (by rfl)
theorem e5033 : o2.add b4812 b4800=b4818 := @add_cons V1 _ o1 b4806 b4651 b4645 b4813 b4801 b4819 b4818 e5029 e5032 (by rfl)
theorem e5034 : o2.add b4811 b4799=b4817 := @add_cons V1 _ o1 b4805 b4650 b4644 b4812 b4800 b4818 b4817 e5028 e5033 (by rfl)
theorem e5035 : o2.add b4810 b4798=b4816 := @add_cons V1 _ o1 b4804 b4649 b4643 b4811 b4799 b4817 b4816 e5027 e5034 (by rfl)
theorem e5036 : o2.add b4809 b4653=b4815 := @add_cons V1 _ o1 b4803 b4648 b4642 b4810 b4798 b4816 b4815 e5026 e5035 (by rfl)
theorem e5037 : o2.add b4808 b4814=b4646 := @add_cons V1 _ o1 b4641 (List.nil : V1) b4641 b4809 b4653 b4815 b4646 e5025 e5036 (by rfl)
theorem e5038 : o2.mul b4640 b12=b4646 := @mul_cons V1 _ o1 b235 b4647 b12 b4653 b4808 b4814 b4646 e5011 e5024 (by rfl) e5037
theorem e5039 : o1.mul b234 b6=b4634 := by decide
theorem e5040 : o1.mul b234 b7=b4820 := by decide
theorem e5041 : o1.mul b234 b8=b4821 := by decide
theorem e5042 : o1.mul b234 b9=b4822 := by decide
theorem e5043 : o1.mul b234 b10=b4823 := by decide
theorem e5044 : o1.mul b234 b11=b4824 := by decide
theorem e5045 : o1.scale b234 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5046 : o1.scale b234 b4475=b4830 := @scale_cons V1 _ o1 b234 b11 b4824 (List.nil : V2) (List.nil : V2) b4830 e5044 e5045 (by rfl)
theorem e5047 : o1.scale b234 b4473=b4829 := @scale_cons V1 _ o1 b234 b10 b4823 b4475 b4830 b4829 e5043 e5046 (by rfl)
theorem e5048 : o1.scale b234 b4471=b4828 := @scale_cons V1 _ o1 b234 b9 b4822 b4473 b4829 b4828 e5042 e5047 (by rfl)
theorem e5049 : o1.scale b234 b4469=b4827 := @scale_cons V1 _ o1 b234 b8 b4821 b4471 b4828 b4827 e5041 e5048 (by rfl)
theorem e5050 : o1.scale b234 b4467=b4826 := @scale_cons V1 _ o1 b234 b7 b4820 b4469 b4827 b4826 e5040 e5049 (by rfl)
theorem e5051 : o1.scale b234 b12=b4825 := @scale_cons V1 _ o1 b234 b6 b4634 b4467 b4826 b4825 e5039 e5050 (by rfl)
theorem e5052 : o1.add b4634 (List.nil : V1)=b4634 := by rfl
theorem e5053 : o1.add b4820 b4641=b4635 := by decide
theorem e5054 : o1.add b4821 b4642=b4636 := by decide
theorem e5055 : o1.add b4822 b4643=b4637 := by decide
theorem e5056 : o1.add b4823 b4644=b4638 := by decide
theorem e5057 : o1.add b4824 b4645=b4371 := by decide
theorem e5058 : o2.add (List.nil : V2) b4819=b4819 := by rfl
theorem e5059 : o2.add b4830 b4818=b4836 := @add_cons V1 _ o1 b4824 b4645 b4371 (List.nil : V2) b4819 b4819 b4836 e5057 e5058 (by rfl)
theorem e5060 : o2.add b4829 b4817=b4835 := @add_cons V1 _ o1 b4823 b4644 b4638 b4830 b4818 b4836 b4835 e5056 e5059 (by rfl)
theorem e5061 : o2.add b4828 b4816=b4834 := @add_cons V1 _ o1 b4822 b4643 b4637 b4829 b4817 b4835 b4834 e5055 e5060 (by rfl)
theorem e5062 : o2.add b4827 b4815=b4833 := @add_cons V1 _ o1 b4821 b4642 b4636 b4828 b4816 b4834 b4833 e5054 e5061 (by rfl)
theorem e5063 : o2.add b4826 b4646=b4832 := @add_cons V1 _ o1 b4820 b4641 b4635 b4827 b4815 b4833 b4832 e5053 e5062 (by rfl)
theorem e5064 : o2.add b4825 b4831=b4639 := @add_cons V1 _ o1 b4634 (List.nil : V1) b4634 b4826 b4646 b4832 b4639 e5052 e5063 (by rfl)
theorem e5065 : o2.mul b4633 b12=b4639 := @mul_cons V1 _ o1 b234 b4640 b12 b4646 b4825 b4831 b4639 e5038 e5051 (by rfl) e5064
theorem e5066 : o1.mul b233 b6=b4365 := by decide
theorem e5067 : o1.mul b233 b7=b4837 := by decide
theorem e5068 : o1.mul b233 b8=b4838 := by decide
theorem e5069 : o1.mul b233 b9=b4839 := by decide
theorem e5070 : o1.mul b233 b10=b4840 := by decide
theorem e5071 : o1.mul b233 b11=b4841 := by decide
theorem e5072 : o1.scale b233 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5073 : o1.scale b233 b4475=b4847 := @scale_cons V1 _ o1 b233 b11 b4841 (List.nil : V2) (List.nil : V2) b4847 e5071 e5072 (by rfl)
theorem e5074 : o1.scale b233 b4473=b4846 := @scale_cons V1 _ o1 b233 b10 b4840 b4475 b4847 b4846 e5070 e5073 (by rfl)
theorem e5075 : o1.scale b233 b4471=b4845 := @scale_cons V1 _ o1 b233 b9 b4839 b4473 b4846 b4845 e5069 e5074 (by rfl)
theorem e5076 : o1.scale b233 b4469=b4844 := @scale_cons V1 _ o1 b233 b8 b4838 b4471 b4845 b4844 e5068 e5075 (by rfl)
theorem e5077 : o1.scale b233 b4467=b4843 := @scale_cons V1 _ o1 b233 b7 b4837 b4469 b4844 b4843 e5067 e5076 (by rfl)
theorem e5078 : o1.scale b233 b12=b4842 := @scale_cons V1 _ o1 b233 b6 b4365 b4467 b4843 b4842 e5066 e5077 (by rfl)
theorem e5079 : o1.add b4365 (List.nil : V1)=b4365 := by rfl
theorem e5080 : o1.add b4837 b4634=b4366 := by decide
theorem e5081 : o1.add b4838 b4635=b4367 := by decide
theorem e5082 : o1.add b4839 b4636=b4368 := by decide
theorem e5083 : o1.add b4840 b4637=b4369 := by decide
theorem e5084 : o1.add b4841 b4638=b4370 := by decide
theorem e5085 : o2.add (List.nil : V2) b4836=b4836 := by rfl
theorem e5086 : o2.add b4847 b4835=b4853 := @add_cons V1 _ o1 b4841 b4638 b4370 (List.nil : V2) b4836 b4836 b4853 e5084 e5085 (by rfl)
theorem e5087 : o2.add b4846 b4834=b4852 := @add_cons V1 _ o1 b4840 b4637 b4369 b4847 b4835 b4853 b4852 e5083 e5086 (by rfl)
theorem e5088 : o2.add b4845 b4833=b4851 := @add_cons V1 _ o1 b4839 b4636 b4368 b4846 b4834 b4852 b4851 e5082 e5087 (by rfl)
theorem e5089 : o2.add b4844 b4832=b4850 := @add_cons V1 _ o1 b4838 b4635 b4367 b4845 b4833 b4851 b4850 e5081 e5088 (by rfl)
theorem e5090 : o2.add b4843 b4639=b4849 := @add_cons V1 _ o1 b4837 b4634 b4366 b4844 b4832 b4850 b4849 e5080 e5089 (by rfl)
theorem e5091 : o2.add b4842 b4848=b4632 := @add_cons V1 _ o1 b4365 (List.nil : V1) b4365 b4843 b4639 b4849 b4632 e5079 e5090 (by rfl)
theorem e5092 : o2.mul b4631 b12=b4632 := @mul_cons V1 _ o1 b233 b4633 b12 b4639 b4842 b4848 b4632 e5065 e5078 (by rfl) e5091
theorem e5093 : o2.add (List.nil : V2) b4380=b4380 := by rfl
theorem e5094 : o2.mul b243 b12=b4380 := @mul_cons V1 _ o1 (List.nil : V1) b4631 b12 b4632 (List.nil : V2) b4380 b4380 e5092 e4828 (by rfl) e5093
theorem e5095 : o2.scale b243 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e5096 : o2.scale b243 b13=b4630 := @scale_cons V2 _ o2 b243 b12 b4380 (List.nil : V3) (List.nil : V3) b4630 e5094 e5095 (by rfl)
theorem e5097 : o2.add b4380 (List.nil : V2)=b4380 := by rfl
theorem e5098 : o3.add (List.nil : V3) b4401=b4401 := by rfl
theorem e5099 : o3.add b4630 b4854=b4399 := @add_cons V2 _ o2 b4380 (List.nil : V2) b4380 (List.nil : V3) b4401 b4401 b4399 e5097 e5098 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
