module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart032

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4800 : o1.scale b244 b4469=b4620 := @scale_cons V1 _ o1 b244 b8 b4614 b4471 b4621 b4620 e4792 e4799 (by rfl)
theorem e4801 : o1.scale b244 b4467=b4619 := @scale_cons V1 _ o1 b244 b7 b4613 b4469 b4620 b4619 e4791 e4800 (by rfl)
theorem e4802 : o1.scale b244 b12=b4618 := @scale_cons V1 _ o1 b244 b6 b4381 b4467 b4619 b4618 e4790 e4801 (by rfl)
theorem e4803 : o1.add b4381 (List.nil : V1)=b4381 := by rfl
theorem e4804 : o1.add b4613 b4405=b4382 := by decide
theorem e4805 : o1.add b4614 b4406=b4383 := by decide
theorem e4806 : o1.add b4615 b4407=b4384 := by decide
theorem e4807 : o1.add b4616 b4408=b4385 := by decide
theorem e4808 : o1.add b4617 b4409=b4386 := by decide
theorem e4809 : o2.add (List.nil : V2) b4612=b4612 := by rfl
theorem e4810 : o2.add b4623 b4611=b4629 := @add_cons V1 _ o1 b4617 b4409 b4386 (List.nil : V2) b4612 b4612 b4629 e4808 e4809 (by rfl)
theorem e4811 : o2.add b4622 b4610=b4628 := @add_cons V1 _ o1 b4616 b4408 b4385 b4623 b4611 b4629 b4628 e4807 e4810 (by rfl)
theorem e4812 : o2.add b4621 b4609=b4627 := @add_cons V1 _ o1 b4615 b4407 b4384 b4622 b4610 b4628 b4627 e4806 e4811 (by rfl)
theorem e4813 : o2.add b4620 b4608=b4626 := @add_cons V1 _ o1 b4614 b4406 b4383 b4621 b4609 b4627 b4626 e4805 e4812 (by rfl)
theorem e4814 : o2.add b4619 b4410=b4625 := @add_cons V1 _ o1 b4613 b4405 b4382 b4620 b4608 b4626 b4625 e4804 e4813 (by rfl)
theorem e4815 : o2.add b4618 b4624=b4403 := @add_cons V1 _ o1 b4381 (List.nil : V1) b4381 b4619 b4410 b4625 b4403 e4803 e4814 (by rfl)
theorem e4816 : o2.mul b4402 b12=b4403 := @mul_cons V1 _ o1 b244 b4404 b12 b4410 b4618 b4624 b4403 e4789 e4802 (by rfl) e4815
theorem e4817 : o1.mul (List.nil : V1) b6=(List.nil : V1) := by rfl
theorem e4818 : o1.mul (List.nil : V1) b7=(List.nil : V1) := by rfl
theorem e4819 : o1.mul (List.nil : V1) b8=(List.nil : V1) := by rfl
theorem e4820 : o1.mul (List.nil : V1) b9=(List.nil : V1) := by rfl
theorem e4821 : o1.mul (List.nil : V1) b10=(List.nil : V1) := by rfl
theorem e4822 : o1.mul (List.nil : V1) b11=(List.nil : V1) := by rfl
theorem e4823 : o1.scale (List.nil : V1) b4475=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b11 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e4822 e3696 (by rfl)
theorem e4824 : o1.scale (List.nil : V1) b4473=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b10 (List.nil : V1) b4475 (List.nil : V2) (List.nil : V2) e4821 e4823 (by rfl)
theorem e4825 : o1.scale (List.nil : V1) b4471=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b9 (List.nil : V1) b4473 (List.nil : V2) (List.nil : V2) e4820 e4824 (by rfl)
theorem e4826 : o1.scale (List.nil : V1) b4469=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b8 (List.nil : V1) b4471 (List.nil : V2) (List.nil : V2) e4819 e4825 (by rfl)
theorem e4827 : o1.scale (List.nil : V1) b4467=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b7 (List.nil : V1) b4469 (List.nil : V2) (List.nil : V2) e4818 e4826 (by rfl)
theorem e4828 : o1.scale (List.nil : V1) b12=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b6 (List.nil : V1) b4467 (List.nil : V2) (List.nil : V2) e4817 e4827 (by rfl)
theorem e4829 : o2.add (List.nil : V2) b4396=b4396 := by rfl
theorem e4830 : o2.mul b254 b12=b4396 := @mul_cons V1 _ o1 (List.nil : V1) b4402 b12 b4403 (List.nil : V2) b4396 b4396 e4816 e4828 (by rfl) e4829
theorem e4831 : o2.scale b254 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e4832 : o2.scale b254 b13=b4401 := @scale_cons V2 _ o2 b254 b12 b4396 (List.nil : V3) (List.nil : V3) b4401 e4830 e4831 (by rfl)
theorem e4833 : o3.add b4401 (List.nil : V3)=b4401 := by rfl
theorem e4834 : o3.mul b4400 b13=b4401 := @mul_cons V2 _ o2 b254 (List.nil : V3) b13 (List.nil : V3) b4401 (List.nil : V3) b4401 e4557 e4832 (by rfl) e4833
theorem e4835 : o1.mul b242 b6=b4690 := by decide
theorem e4836 : o1.mul b242 b7=b4691 := by decide
theorem e4837 : o1.mul b242 b8=b4692 := by decide
theorem e4838 : o1.mul b242 b9=b4693 := by decide
theorem e4839 : o1.mul b242 b10=b4694 := by decide
theorem e4840 : o1.mul b242 b11=b4379 := by decide
theorem e4841 : o1.scale b242 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4842 : o1.scale b242 b4475=b4700 := @scale_cons V1 _ o1 b242 b11 b4379 (List.nil : V2) (List.nil : V2) b4700 e4840 e4841 (by rfl)
theorem e4843 : o1.scale b242 b4473=b4699 := @scale_cons V1 _ o1 b242 b10 b4694 b4475 b4700 b4699 e4839 e4842 (by rfl)
theorem e4844 : o1.scale b242 b4471=b4698 := @scale_cons V1 _ o1 b242 b9 b4693 b4473 b4699 b4698 e4838 e4843 (by rfl)
theorem e4845 : o1.scale b242 b4469=b4697 := @scale_cons V1 _ o1 b242 b8 b4692 b4471 b4698 b4697 e4837 e4844 (by rfl)
theorem e4846 : o1.scale b242 b4467=b4696 := @scale_cons V1 _ o1 b242 b7 b4691 b4469 b4697 b4696 e4836 e4845 (by rfl)
theorem e4847 : o1.scale b242 b12=b4695 := @scale_cons V1 _ o1 b242 b6 b4690 b4467 b4696 b4695 e4835 e4846 (by rfl)
theorem e4848 : o2.add b4695 (List.nil : V2)=b4695 := by rfl
theorem e4849 : o2.mul b4689 b12=b4695 := @mul_cons V1 _ o1 b242 (List.nil : V2) b12 (List.nil : V2) b4695 (List.nil : V2) b4695 e4558 e4847 (by rfl) e4848
theorem e4850 : o1.mul b241 b6=b4683 := by decide
theorem e4851 : o1.mul b241 b7=b4701 := by decide
theorem e4852 : o1.mul b241 b8=b4702 := by decide
theorem e4853 : o1.mul b241 b9=b4703 := by decide
theorem e4854 : o1.mul b241 b10=b4704 := by decide
theorem e4855 : o1.mul b241 b11=b4705 := by decide
theorem e4856 : o1.scale b241 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4857 : o1.scale b241 b4475=b4711 := @scale_cons V1 _ o1 b241 b11 b4705 (List.nil : V2) (List.nil : V2) b4711 e4855 e4856 (by rfl)
theorem e4858 : o1.scale b241 b4473=b4710 := @scale_cons V1 _ o1 b241 b10 b4704 b4475 b4711 b4710 e4854 e4857 (by rfl)
theorem e4859 : o1.scale b241 b4471=b4709 := @scale_cons V1 _ o1 b241 b9 b4703 b4473 b4710 b4709 e4853 e4858 (by rfl)
theorem e4860 : o1.scale b241 b4469=b4708 := @scale_cons V1 _ o1 b241 b8 b4702 b4471 b4709 b4708 e4852 e4859 (by rfl)
theorem e4861 : o1.scale b241 b4467=b4707 := @scale_cons V1 _ o1 b241 b7 b4701 b4469 b4708 b4707 e4851 e4860 (by rfl)
theorem e4862 : o1.scale b241 b12=b4706 := @scale_cons V1 _ o1 b241 b6 b4683 b4467 b4707 b4706 e4850 e4861 (by rfl)
theorem e4863 : o1.add b4683 (List.nil : V1)=b4683 := by rfl
theorem e4864 : o1.add b4701 b4690=b4684 := by decide
theorem e4865 : o1.add b4702 b4691=b4685 := by decide
theorem e4866 : o1.add b4703 b4692=b4686 := by decide
theorem e4867 : o1.add b4704 b4693=b4687 := by decide
theorem e4868 : o1.add b4705 b4694=b4378 := by decide
theorem e4869 : o2.add (List.nil : V2) b4700=b4700 := by rfl
theorem e4870 : o2.add b4711 b4699=b4717 := @add_cons V1 _ o1 b4705 b4694 b4378 (List.nil : V2) b4700 b4700 b4717 e4868 e4869 (by rfl)
theorem e4871 : o2.add b4710 b4698=b4716 := @add_cons V1 _ o1 b4704 b4693 b4687 b4711 b4699 b4717 b4716 e4867 e4870 (by rfl)
theorem e4872 : o2.add b4709 b4697=b4715 := @add_cons V1 _ o1 b4703 b4692 b4686 b4710 b4698 b4716 b4715 e4866 e4871 (by rfl)
theorem e4873 : o2.add b4708 b4696=b4714 := @add_cons V1 _ o1 b4702 b4691 b4685 b4709 b4697 b4715 b4714 e4865 e4872 (by rfl)
theorem e4874 : o2.add b4707 b4695=b4713 := @add_cons V1 _ o1 b4701 b4690 b4684 b4708 b4696 b4714 b4713 e4864 e4873 (by rfl)
theorem e4875 : o2.add b4706 b4712=b4688 := @add_cons V1 _ o1 b4683 (List.nil : V1) b4683 b4707 b4695 b4713 b4688 e4863 e4874 (by rfl)
theorem e4876 : o2.mul b4682 b12=b4688 := @mul_cons V1 _ o1 b241 b4689 b12 b4695 b4706 b4712 b4688 e4849 e4862 (by rfl) e4875
theorem e4877 : o1.mul b240 b6=b4676 := by decide
theorem e4878 : o1.mul b240 b7=b4718 := by decide
theorem e4879 : o1.mul b240 b8=b4719 := by decide
theorem e4880 : o1.mul b240 b9=b4720 := by decide
theorem e4881 : o1.mul b240 b10=b4721 := by decide
theorem e4882 : o1.mul b240 b11=b4722 := by decide
theorem e4883 : o1.scale b240 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4884 : o1.scale b240 b4475=b4728 := @scale_cons V1 _ o1 b240 b11 b4722 (List.nil : V2) (List.nil : V2) b4728 e4882 e4883 (by rfl)
theorem e4885 : o1.scale b240 b4473=b4727 := @scale_cons V1 _ o1 b240 b10 b4721 b4475 b4728 b4727 e4881 e4884 (by rfl)
theorem e4886 : o1.scale b240 b4471=b4726 := @scale_cons V1 _ o1 b240 b9 b4720 b4473 b4727 b4726 e4880 e4885 (by rfl)
theorem e4887 : o1.scale b240 b4469=b4725 := @scale_cons V1 _ o1 b240 b8 b4719 b4471 b4726 b4725 e4879 e4886 (by rfl)
theorem e4888 : o1.scale b240 b4467=b4724 := @scale_cons V1 _ o1 b240 b7 b4718 b4469 b4725 b4724 e4878 e4887 (by rfl)
theorem e4889 : o1.scale b240 b12=b4723 := @scale_cons V1 _ o1 b240 b6 b4676 b4467 b4724 b4723 e4877 e4888 (by rfl)
theorem e4890 : o1.add b4676 (List.nil : V1)=b4676 := by rfl
theorem e4891 : o1.add b4718 b4683=b4677 := by decide
theorem e4892 : o1.add b4719 b4684=b4678 := by decide
theorem e4893 : o1.add b4720 b4685=b4679 := by decide
theorem e4894 : o1.add b4721 b4686=b4680 := by decide
theorem e4895 : o1.add b4722 b4687=b4377 := by decide
theorem e4896 : o2.add (List.nil : V2) b4717=b4717 := by rfl
theorem e4897 : o2.add b4728 b4716=b4734 := @add_cons V1 _ o1 b4722 b4687 b4377 (List.nil : V2) b4717 b4717 b4734 e4895 e4896 (by rfl)
theorem e4898 : o2.add b4727 b4715=b4733 := @add_cons V1 _ o1 b4721 b4686 b4680 b4728 b4716 b4734 b4733 e4894 e4897 (by rfl)
theorem e4899 : o2.add b4726 b4714=b4732 := @add_cons V1 _ o1 b4720 b4685 b4679 b4727 b4715 b4733 b4732 e4893 e4898 (by rfl)
theorem e4900 : o2.add b4725 b4713=b4731 := @add_cons V1 _ o1 b4719 b4684 b4678 b4726 b4714 b4732 b4731 e4892 e4899 (by rfl)
theorem e4901 : o2.add b4724 b4688=b4730 := @add_cons V1 _ o1 b4718 b4683 b4677 b4725 b4713 b4731 b4730 e4891 e4900 (by rfl)
theorem e4902 : o2.add b4723 b4729=b4681 := @add_cons V1 _ o1 b4676 (List.nil : V1) b4676 b4724 b4688 b4730 b4681 e4890 e4901 (by rfl)
theorem e4903 : o2.mul b4675 b12=b4681 := @mul_cons V1 _ o1 b240 b4682 b12 b4688 b4723 b4729 b4681 e4876 e4889 (by rfl) e4902
theorem e4904 : o1.mul b239 b6=b4669 := by decide
theorem e4905 : o1.mul b239 b7=b4735 := by decide
theorem e4906 : o1.mul b239 b8=b4736 := by decide
theorem e4907 : o1.mul b239 b9=b4737 := by decide
theorem e4908 : o1.mul b239 b10=b4738 := by decide
theorem e4909 : o1.mul b239 b11=b4739 := by decide
theorem e4910 : o1.scale b239 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4911 : o1.scale b239 b4475=b4745 := @scale_cons V1 _ o1 b239 b11 b4739 (List.nil : V2) (List.nil : V2) b4745 e4909 e4910 (by rfl)
theorem e4912 : o1.scale b239 b4473=b4744 := @scale_cons V1 _ o1 b239 b10 b4738 b4475 b4745 b4744 e4908 e4911 (by rfl)
theorem e4913 : o1.scale b239 b4471=b4743 := @scale_cons V1 _ o1 b239 b9 b4737 b4473 b4744 b4743 e4907 e4912 (by rfl)
theorem e4914 : o1.scale b239 b4469=b4742 := @scale_cons V1 _ o1 b239 b8 b4736 b4471 b4743 b4742 e4906 e4913 (by rfl)
theorem e4915 : o1.scale b239 b4467=b4741 := @scale_cons V1 _ o1 b239 b7 b4735 b4469 b4742 b4741 e4905 e4914 (by rfl)
theorem e4916 : o1.scale b239 b12=b4740 := @scale_cons V1 _ o1 b239 b6 b4669 b4467 b4741 b4740 e4904 e4915 (by rfl)
theorem e4917 : o1.add b4669 (List.nil : V1)=b4669 := by rfl
theorem e4918 : o1.add b4735 b4676=b4670 := by decide
theorem e4919 : o1.add b4736 b4677=b4671 := by decide
theorem e4920 : o1.add b4737 b4678=b4672 := by decide
theorem e4921 : o1.add b4738 b4679=b4673 := by decide
theorem e4922 : o1.add b4739 b4680=b4376 := by decide
theorem e4923 : o2.add (List.nil : V2) b4734=b4734 := by rfl
theorem e4924 : o2.add b4745 b4733=b4751 := @add_cons V1 _ o1 b4739 b4680 b4376 (List.nil : V2) b4734 b4734 b4751 e4922 e4923 (by rfl)
theorem e4925 : o2.add b4744 b4732=b4750 := @add_cons V1 _ o1 b4738 b4679 b4673 b4745 b4733 b4751 b4750 e4921 e4924 (by rfl)
theorem e4926 : o2.add b4743 b4731=b4749 := @add_cons V1 _ o1 b4737 b4678 b4672 b4744 b4732 b4750 b4749 e4920 e4925 (by rfl)
theorem e4927 : o2.add b4742 b4730=b4748 := @add_cons V1 _ o1 b4736 b4677 b4671 b4743 b4731 b4749 b4748 e4919 e4926 (by rfl)
theorem e4928 : o2.add b4741 b4681=b4747 := @add_cons V1 _ o1 b4735 b4676 b4670 b4742 b4730 b4748 b4747 e4918 e4927 (by rfl)
theorem e4929 : o2.add b4740 b4746=b4674 := @add_cons V1 _ o1 b4669 (List.nil : V1) b4669 b4741 b4681 b4747 b4674 e4917 e4928 (by rfl)
theorem e4930 : o2.mul b4668 b12=b4674 := @mul_cons V1 _ o1 b239 b4675 b12 b4681 b4740 b4746 b4674 e4903 e4916 (by rfl) e4929
theorem e4931 : o1.mul b238 b6=b4662 := by decide
theorem e4932 : o1.mul b238 b7=b4752 := by decide
theorem e4933 : o1.mul b238 b8=b4753 := by decide
theorem e4934 : o1.mul b238 b9=b4754 := by decide
theorem e4935 : o1.mul b238 b10=b4755 := by decide
theorem e4936 : o1.mul b238 b11=b4756 := by decide
theorem e4937 : o1.scale b238 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4938 : o1.scale b238 b4475=b4762 := @scale_cons V1 _ o1 b238 b11 b4756 (List.nil : V2) (List.nil : V2) b4762 e4936 e4937 (by rfl)
theorem e4939 : o1.scale b238 b4473=b4761 := @scale_cons V1 _ o1 b238 b10 b4755 b4475 b4762 b4761 e4935 e4938 (by rfl)
theorem e4940 : o1.scale b238 b4471=b4760 := @scale_cons V1 _ o1 b238 b9 b4754 b4473 b4761 b4760 e4934 e4939 (by rfl)
theorem e4941 : o1.scale b238 b4469=b4759 := @scale_cons V1 _ o1 b238 b8 b4753 b4471 b4760 b4759 e4933 e4940 (by rfl)
theorem e4942 : o1.scale b238 b4467=b4758 := @scale_cons V1 _ o1 b238 b7 b4752 b4469 b4759 b4758 e4932 e4941 (by rfl)
theorem e4943 : o1.scale b238 b12=b4757 := @scale_cons V1 _ o1 b238 b6 b4662 b4467 b4758 b4757 e4931 e4942 (by rfl)
theorem e4944 : o1.add b4662 (List.nil : V1)=b4662 := by rfl
theorem e4945 : o1.add b4752 b4669=b4663 := by decide
theorem e4946 : o1.add b4753 b4670=b4664 := by decide
theorem e4947 : o1.add b4754 b4671=b4665 := by decide
theorem e4948 : o1.add b4755 b4672=b4666 := by decide
theorem e4949 : o1.add b4756 b4673=b4375 := by decide

end RKResearch.Certified.Graded.NativePencilCubicDAG
