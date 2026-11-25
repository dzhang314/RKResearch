module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart031

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4650 : o2.add b4519 b4507=b4525 := @add_cons V1 _ o1 b4513 b4449 b4443 b4520 b4508 b4526 b4525 e4644 e4649 (by rfl)
theorem e4651 : o2.add b4518 b4506=b4524 := @add_cons V1 _ o1 b4512 b4448 b4442 b4519 b4507 b4525 b4524 e4643 e4650 (by rfl)
theorem e4652 : o2.add b4517 b4452=b4523 := @add_cons V1 _ o1 b4511 b4447 b4441 b4518 b4506 b4524 b4523 e4642 e4651 (by rfl)
theorem e4653 : o2.add b4516 b4522=b4445 := @add_cons V1 _ o1 b4440 (List.nil : V1) b4440 b4517 b4452 b4523 b4445 e4641 e4652 (by rfl)
theorem e4654 : o2.mul b4439 b12=b4445 := @mul_cons V1 _ o1 b250 b4446 b12 b4452 b4516 b4522 b4445 e4627 e4640 (by rfl) e4653
theorem e4655 : o1.mul b249 b6=b4433 := by decide
theorem e4656 : o1.mul b249 b7=b4528 := by decide
theorem e4657 : o1.mul b249 b8=b4529 := by decide
theorem e4658 : o1.mul b249 b9=b4530 := by decide
theorem e4659 : o1.mul b249 b10=b4531 := by decide
theorem e4660 : o1.mul b249 b11=b4532 := by decide
theorem e4661 : o1.scale b249 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4662 : o1.scale b249 b4475=b4538 := @scale_cons V1 _ o1 b249 b11 b4532 (List.nil : V2) (List.nil : V2) b4538 e4660 e4661 (by rfl)
theorem e4663 : o1.scale b249 b4473=b4537 := @scale_cons V1 _ o1 b249 b10 b4531 b4475 b4538 b4537 e4659 e4662 (by rfl)
theorem e4664 : o1.scale b249 b4471=b4536 := @scale_cons V1 _ o1 b249 b9 b4530 b4473 b4537 b4536 e4658 e4663 (by rfl)
theorem e4665 : o1.scale b249 b4469=b4535 := @scale_cons V1 _ o1 b249 b8 b4529 b4471 b4536 b4535 e4657 e4664 (by rfl)
theorem e4666 : o1.scale b249 b4467=b4534 := @scale_cons V1 _ o1 b249 b7 b4528 b4469 b4535 b4534 e4656 e4665 (by rfl)
theorem e4667 : o1.scale b249 b12=b4533 := @scale_cons V1 _ o1 b249 b6 b4433 b4467 b4534 b4533 e4655 e4666 (by rfl)
theorem e4668 : o1.add b4433 (List.nil : V1)=b4433 := by rfl
theorem e4669 : o1.add b4528 b4440=b4434 := by decide
theorem e4670 : o1.add b4529 b4441=b4435 := by decide
theorem e4671 : o1.add b4530 b4442=b4436 := by decide
theorem e4672 : o1.add b4531 b4443=b4437 := by decide
theorem e4673 : o1.add b4532 b4444=b4391 := by decide
theorem e4674 : o2.add (List.nil : V2) b4527=b4527 := by rfl
theorem e4675 : o2.add b4538 b4526=b4544 := @add_cons V1 _ o1 b4532 b4444 b4391 (List.nil : V2) b4527 b4527 b4544 e4673 e4674 (by rfl)
theorem e4676 : o2.add b4537 b4525=b4543 := @add_cons V1 _ o1 b4531 b4443 b4437 b4538 b4526 b4544 b4543 e4672 e4675 (by rfl)
theorem e4677 : o2.add b4536 b4524=b4542 := @add_cons V1 _ o1 b4530 b4442 b4436 b4537 b4525 b4543 b4542 e4671 e4676 (by rfl)
theorem e4678 : o2.add b4535 b4523=b4541 := @add_cons V1 _ o1 b4529 b4441 b4435 b4536 b4524 b4542 b4541 e4670 e4677 (by rfl)
theorem e4679 : o2.add b4534 b4445=b4540 := @add_cons V1 _ o1 b4528 b4440 b4434 b4535 b4523 b4541 b4540 e4669 e4678 (by rfl)
theorem e4680 : o2.add b4533 b4539=b4438 := @add_cons V1 _ o1 b4433 (List.nil : V1) b4433 b4534 b4445 b4540 b4438 e4668 e4679 (by rfl)
theorem e4681 : o2.mul b4432 b12=b4438 := @mul_cons V1 _ o1 b249 b4439 b12 b4445 b4533 b4539 b4438 e4654 e4667 (by rfl) e4680
theorem e4682 : o1.mul b248 b6=b4426 := by decide
theorem e4683 : o1.mul b248 b7=b4545 := by decide
theorem e4684 : o1.mul b248 b8=b4546 := by decide
theorem e4685 : o1.mul b248 b9=b4547 := by decide
theorem e4686 : o1.mul b248 b10=b4548 := by decide
theorem e4687 : o1.mul b248 b11=b4549 := by decide
theorem e4688 : o1.scale b248 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4689 : o1.scale b248 b4475=b4555 := @scale_cons V1 _ o1 b248 b11 b4549 (List.nil : V2) (List.nil : V2) b4555 e4687 e4688 (by rfl)
theorem e4690 : o1.scale b248 b4473=b4554 := @scale_cons V1 _ o1 b248 b10 b4548 b4475 b4555 b4554 e4686 e4689 (by rfl)
theorem e4691 : o1.scale b248 b4471=b4553 := @scale_cons V1 _ o1 b248 b9 b4547 b4473 b4554 b4553 e4685 e4690 (by rfl)
theorem e4692 : o1.scale b248 b4469=b4552 := @scale_cons V1 _ o1 b248 b8 b4546 b4471 b4553 b4552 e4684 e4691 (by rfl)
theorem e4693 : o1.scale b248 b4467=b4551 := @scale_cons V1 _ o1 b248 b7 b4545 b4469 b4552 b4551 e4683 e4692 (by rfl)
theorem e4694 : o1.scale b248 b12=b4550 := @scale_cons V1 _ o1 b248 b6 b4426 b4467 b4551 b4550 e4682 e4693 (by rfl)
theorem e4695 : o1.add b4426 (List.nil : V1)=b4426 := by rfl
theorem e4696 : o1.add b4545 b4433=b4427 := by decide
theorem e4697 : o1.add b4546 b4434=b4428 := by decide
theorem e4698 : o1.add b4547 b4435=b4429 := by decide
theorem e4699 : o1.add b4548 b4436=b4430 := by decide
theorem e4700 : o1.add b4549 b4437=b4390 := by decide
theorem e4701 : o2.add (List.nil : V2) b4544=b4544 := by rfl
theorem e4702 : o2.add b4555 b4543=b4561 := @add_cons V1 _ o1 b4549 b4437 b4390 (List.nil : V2) b4544 b4544 b4561 e4700 e4701 (by rfl)
theorem e4703 : o2.add b4554 b4542=b4560 := @add_cons V1 _ o1 b4548 b4436 b4430 b4555 b4543 b4561 b4560 e4699 e4702 (by rfl)
theorem e4704 : o2.add b4553 b4541=b4559 := @add_cons V1 _ o1 b4547 b4435 b4429 b4554 b4542 b4560 b4559 e4698 e4703 (by rfl)
theorem e4705 : o2.add b4552 b4540=b4558 := @add_cons V1 _ o1 b4546 b4434 b4428 b4553 b4541 b4559 b4558 e4697 e4704 (by rfl)
theorem e4706 : o2.add b4551 b4438=b4557 := @add_cons V1 _ o1 b4545 b4433 b4427 b4552 b4540 b4558 b4557 e4696 e4705 (by rfl)
theorem e4707 : o2.add b4550 b4556=b4431 := @add_cons V1 _ o1 b4426 (List.nil : V1) b4426 b4551 b4438 b4557 b4431 e4695 e4706 (by rfl)
theorem e4708 : o2.mul b4425 b12=b4431 := @mul_cons V1 _ o1 b248 b4432 b12 b4438 b4550 b4556 b4431 e4681 e4694 (by rfl) e4707
theorem e4709 : o1.mul b247 b6=b4419 := by decide
theorem e4710 : o1.mul b247 b7=b4562 := by decide
theorem e4711 : o1.mul b247 b8=b4563 := by decide
theorem e4712 : o1.mul b247 b9=b4564 := by decide
theorem e4713 : o1.mul b247 b10=b4565 := by decide
theorem e4714 : o1.mul b247 b11=b4566 := by decide
theorem e4715 : o1.scale b247 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4716 : o1.scale b247 b4475=b4572 := @scale_cons V1 _ o1 b247 b11 b4566 (List.nil : V2) (List.nil : V2) b4572 e4714 e4715 (by rfl)
theorem e4717 : o1.scale b247 b4473=b4571 := @scale_cons V1 _ o1 b247 b10 b4565 b4475 b4572 b4571 e4713 e4716 (by rfl)
theorem e4718 : o1.scale b247 b4471=b4570 := @scale_cons V1 _ o1 b247 b9 b4564 b4473 b4571 b4570 e4712 e4717 (by rfl)
theorem e4719 : o1.scale b247 b4469=b4569 := @scale_cons V1 _ o1 b247 b8 b4563 b4471 b4570 b4569 e4711 e4718 (by rfl)
theorem e4720 : o1.scale b247 b4467=b4568 := @scale_cons V1 _ o1 b247 b7 b4562 b4469 b4569 b4568 e4710 e4719 (by rfl)
theorem e4721 : o1.scale b247 b12=b4567 := @scale_cons V1 _ o1 b247 b6 b4419 b4467 b4568 b4567 e4709 e4720 (by rfl)
theorem e4722 : o1.add b4419 (List.nil : V1)=b4419 := by rfl
theorem e4723 : o1.add b4562 b4426=b4420 := by decide
theorem e4724 : o1.add b4563 b4427=b4421 := by decide
theorem e4725 : o1.add b4564 b4428=b4422 := by decide
theorem e4726 : o1.add b4565 b4429=b4423 := by decide
theorem e4727 : o1.add b4566 b4430=b4389 := by decide
theorem e4728 : o2.add (List.nil : V2) b4561=b4561 := by rfl
theorem e4729 : o2.add b4572 b4560=b4578 := @add_cons V1 _ o1 b4566 b4430 b4389 (List.nil : V2) b4561 b4561 b4578 e4727 e4728 (by rfl)
theorem e4730 : o2.add b4571 b4559=b4577 := @add_cons V1 _ o1 b4565 b4429 b4423 b4572 b4560 b4578 b4577 e4726 e4729 (by rfl)
theorem e4731 : o2.add b4570 b4558=b4576 := @add_cons V1 _ o1 b4564 b4428 b4422 b4571 b4559 b4577 b4576 e4725 e4730 (by rfl)
theorem e4732 : o2.add b4569 b4557=b4575 := @add_cons V1 _ o1 b4563 b4427 b4421 b4570 b4558 b4576 b4575 e4724 e4731 (by rfl)
theorem e4733 : o2.add b4568 b4431=b4574 := @add_cons V1 _ o1 b4562 b4426 b4420 b4569 b4557 b4575 b4574 e4723 e4732 (by rfl)
theorem e4734 : o2.add b4567 b4573=b4424 := @add_cons V1 _ o1 b4419 (List.nil : V1) b4419 b4568 b4431 b4574 b4424 e4722 e4733 (by rfl)
theorem e4735 : o2.mul b4418 b12=b4424 := @mul_cons V1 _ o1 b247 b4425 b12 b4431 b4567 b4573 b4424 e4708 e4721 (by rfl) e4734
theorem e4736 : o1.mul b246 b6=b4412 := by decide
theorem e4737 : o1.mul b246 b7=b4579 := by decide
theorem e4738 : o1.mul b246 b8=b4580 := by decide
theorem e4739 : o1.mul b246 b9=b4581 := by decide
theorem e4740 : o1.mul b246 b10=b4582 := by decide
theorem e4741 : o1.mul b246 b11=b4583 := by decide
theorem e4742 : o1.scale b246 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4743 : o1.scale b246 b4475=b4589 := @scale_cons V1 _ o1 b246 b11 b4583 (List.nil : V2) (List.nil : V2) b4589 e4741 e4742 (by rfl)
theorem e4744 : o1.scale b246 b4473=b4588 := @scale_cons V1 _ o1 b246 b10 b4582 b4475 b4589 b4588 e4740 e4743 (by rfl)
theorem e4745 : o1.scale b246 b4471=b4587 := @scale_cons V1 _ o1 b246 b9 b4581 b4473 b4588 b4587 e4739 e4744 (by rfl)
theorem e4746 : o1.scale b246 b4469=b4586 := @scale_cons V1 _ o1 b246 b8 b4580 b4471 b4587 b4586 e4738 e4745 (by rfl)
theorem e4747 : o1.scale b246 b4467=b4585 := @scale_cons V1 _ o1 b246 b7 b4579 b4469 b4586 b4585 e4737 e4746 (by rfl)
theorem e4748 : o1.scale b246 b12=b4584 := @scale_cons V1 _ o1 b246 b6 b4412 b4467 b4585 b4584 e4736 e4747 (by rfl)
theorem e4749 : o1.add b4412 (List.nil : V1)=b4412 := by rfl
theorem e4750 : o1.add b4579 b4419=b4413 := by decide
theorem e4751 : o1.add b4580 b4420=b4414 := by decide
theorem e4752 : o1.add b4581 b4421=b4415 := by decide
theorem e4753 : o1.add b4582 b4422=b4416 := by decide
theorem e4754 : o1.add b4583 b4423=b4388 := by decide
theorem e4755 : o2.add (List.nil : V2) b4578=b4578 := by rfl
theorem e4756 : o2.add b4589 b4577=b4595 := @add_cons V1 _ o1 b4583 b4423 b4388 (List.nil : V2) b4578 b4578 b4595 e4754 e4755 (by rfl)
theorem e4757 : o2.add b4588 b4576=b4594 := @add_cons V1 _ o1 b4582 b4422 b4416 b4589 b4577 b4595 b4594 e4753 e4756 (by rfl)
theorem e4758 : o2.add b4587 b4575=b4593 := @add_cons V1 _ o1 b4581 b4421 b4415 b4588 b4576 b4594 b4593 e4752 e4757 (by rfl)
theorem e4759 : o2.add b4586 b4574=b4592 := @add_cons V1 _ o1 b4580 b4420 b4414 b4587 b4575 b4593 b4592 e4751 e4758 (by rfl)
theorem e4760 : o2.add b4585 b4424=b4591 := @add_cons V1 _ o1 b4579 b4419 b4413 b4586 b4574 b4592 b4591 e4750 e4759 (by rfl)
theorem e4761 : o2.add b4584 b4590=b4417 := @add_cons V1 _ o1 b4412 (List.nil : V1) b4412 b4585 b4424 b4591 b4417 e4749 e4760 (by rfl)
theorem e4762 : o2.mul b4411 b12=b4417 := @mul_cons V1 _ o1 b246 b4418 b12 b4424 b4584 b4590 b4417 e4735 e4748 (by rfl) e4761
theorem e4763 : o1.mul b245 b6=b4405 := by decide
theorem e4764 : o1.mul b245 b7=b4596 := by decide
theorem e4765 : o1.mul b245 b8=b4597 := by decide
theorem e4766 : o1.mul b245 b9=b4598 := by decide
theorem e4767 : o1.mul b245 b10=b4599 := by decide
theorem e4768 : o1.mul b245 b11=b4600 := by decide
theorem e4769 : o1.scale b245 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4770 : o1.scale b245 b4475=b4606 := @scale_cons V1 _ o1 b245 b11 b4600 (List.nil : V2) (List.nil : V2) b4606 e4768 e4769 (by rfl)
theorem e4771 : o1.scale b245 b4473=b4605 := @scale_cons V1 _ o1 b245 b10 b4599 b4475 b4606 b4605 e4767 e4770 (by rfl)
theorem e4772 : o1.scale b245 b4471=b4604 := @scale_cons V1 _ o1 b245 b9 b4598 b4473 b4605 b4604 e4766 e4771 (by rfl)
theorem e4773 : o1.scale b245 b4469=b4603 := @scale_cons V1 _ o1 b245 b8 b4597 b4471 b4604 b4603 e4765 e4772 (by rfl)
theorem e4774 : o1.scale b245 b4467=b4602 := @scale_cons V1 _ o1 b245 b7 b4596 b4469 b4603 b4602 e4764 e4773 (by rfl)
theorem e4775 : o1.scale b245 b12=b4601 := @scale_cons V1 _ o1 b245 b6 b4405 b4467 b4602 b4601 e4763 e4774 (by rfl)
theorem e4776 : o1.add b4405 (List.nil : V1)=b4405 := by rfl
theorem e4777 : o1.add b4596 b4412=b4406 := by decide
theorem e4778 : o1.add b4597 b4413=b4407 := by decide
theorem e4779 : o1.add b4598 b4414=b4408 := by decide
theorem e4780 : o1.add b4599 b4415=b4409 := by decide
theorem e4781 : o1.add b4600 b4416=b4387 := by decide
theorem e4782 : o2.add (List.nil : V2) b4595=b4595 := by rfl
theorem e4783 : o2.add b4606 b4594=b4612 := @add_cons V1 _ o1 b4600 b4416 b4387 (List.nil : V2) b4595 b4595 b4612 e4781 e4782 (by rfl)
theorem e4784 : o2.add b4605 b4593=b4611 := @add_cons V1 _ o1 b4599 b4415 b4409 b4606 b4594 b4612 b4611 e4780 e4783 (by rfl)
theorem e4785 : o2.add b4604 b4592=b4610 := @add_cons V1 _ o1 b4598 b4414 b4408 b4605 b4593 b4611 b4610 e4779 e4784 (by rfl)
theorem e4786 : o2.add b4603 b4591=b4609 := @add_cons V1 _ o1 b4597 b4413 b4407 b4604 b4592 b4610 b4609 e4778 e4785 (by rfl)
theorem e4787 : o2.add b4602 b4417=b4608 := @add_cons V1 _ o1 b4596 b4412 b4406 b4603 b4591 b4609 b4608 e4777 e4786 (by rfl)
theorem e4788 : o2.add b4601 b4607=b4410 := @add_cons V1 _ o1 b4405 (List.nil : V1) b4405 b4602 b4417 b4608 b4410 e4776 e4787 (by rfl)
theorem e4789 : o2.mul b4404 b12=b4410 := @mul_cons V1 _ o1 b245 b4411 b12 b4417 b4601 b4607 b4410 e4762 e4775 (by rfl) e4788
theorem e4790 : o1.mul b244 b6=b4381 := by decide
theorem e4791 : o1.mul b244 b7=b4613 := by decide
theorem e4792 : o1.mul b244 b8=b4614 := by decide
theorem e4793 : o1.mul b244 b9=b4615 := by decide
theorem e4794 : o1.mul b244 b10=b4616 := by decide
theorem e4795 : o1.mul b244 b11=b4617 := by decide
theorem e4796 : o1.scale b244 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4797 : o1.scale b244 b4475=b4623 := @scale_cons V1 _ o1 b244 b11 b4617 (List.nil : V2) (List.nil : V2) b4623 e4795 e4796 (by rfl)
theorem e4798 : o1.scale b244 b4473=b4622 := @scale_cons V1 _ o1 b244 b10 b4616 b4475 b4623 b4622 e4794 e4797 (by rfl)
theorem e4799 : o1.scale b244 b4471=b4621 := @scale_cons V1 _ o1 b244 b9 b4615 b4473 b4622 b4621 e4793 e4798 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
