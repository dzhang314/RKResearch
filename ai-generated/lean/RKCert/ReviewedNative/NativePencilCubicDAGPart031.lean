module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart030

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e4500 : o2.add b4331 b4332=b4300 := @add_cons V1 _ o1 b3698 (List.nil : V1) b3698 (List.nil : V2) b4302 b4302 b4300 e4498 e4499 (by rfl)
theorem e4501 : o2.mul b4299 b4=b4300 := @mul_cons V1 _ o1 b97 b4301 b4 b4302 b4331 b4332 b4300 e4494 e4497 (by rfl) e4500
theorem e4502 : o1.mul b96 b3=b3697 := by decide
theorem e4503 : o1.scale b96 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4504 : o1.scale b96 b4=b4333 := @scale_cons V1 _ o1 b96 b3 b3697 (List.nil : V2) (List.nil : V2) b4333 e4502 e4503 (by rfl)
theorem e4505 : o1.add b3697 (List.nil : V1)=b3697 := by rfl
theorem e4506 : o2.add (List.nil : V2) b4300=b4300 := by rfl
theorem e4507 : o2.add b4333 b4334=b4298 := @add_cons V1 _ o1 b3697 (List.nil : V1) b3697 (List.nil : V2) b4300 b4300 b4298 e4505 e4506 (by rfl)
theorem e4508 : o2.mul b4297 b4=b4298 := @mul_cons V1 _ o1 b96 b4299 b4 b4300 b4333 b4334 b4298 e4501 e4504 (by rfl) e4507
theorem e4509 : o1.mul b95 b3=b3696 := by decide
theorem e4510 : o1.scale b95 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4511 : o1.scale b95 b4=b4335 := @scale_cons V1 _ o1 b95 b3 b3696 (List.nil : V2) (List.nil : V2) b4335 e4509 e4510 (by rfl)
theorem e4512 : o1.add b3696 (List.nil : V1)=b3696 := by rfl
theorem e4513 : o2.add (List.nil : V2) b4298=b4298 := by rfl
theorem e4514 : o2.add b4335 b4336=b4296 := @add_cons V1 _ o1 b3696 (List.nil : V1) b3696 (List.nil : V2) b4298 b4298 b4296 e4512 e4513 (by rfl)
theorem e4515 : o2.mul b4295 b4=b4296 := @mul_cons V1 _ o1 b95 b4297 b4 b4298 b4335 b4336 b4296 e4508 e4511 (by rfl) e4514
theorem e4516 : o1.mul b94 b3=b3695 := by decide
theorem e4517 : o1.scale b94 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4518 : o1.scale b94 b4=b4337 := @scale_cons V1 _ o1 b94 b3 b3695 (List.nil : V2) (List.nil : V2) b4337 e4516 e4517 (by rfl)
theorem e4519 : o1.add b3695 (List.nil : V1)=b3695 := by rfl
theorem e4520 : o2.add (List.nil : V2) b4296=b4296 := by rfl
theorem e4521 : o2.add b4337 b4338=b4294 := @add_cons V1 _ o1 b3695 (List.nil : V1) b3695 (List.nil : V2) b4296 b4296 b4294 e4519 e4520 (by rfl)
theorem e4522 : o2.mul b4293 b4=b4294 := @mul_cons V1 _ o1 b94 b4295 b4 b4296 b4337 b4338 b4294 e4515 e4518 (by rfl) e4521
theorem e4523 : o1.mul b93 b3=b3694 := by decide
theorem e4524 : o1.scale b93 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4525 : o1.scale b93 b4=b4339 := @scale_cons V1 _ o1 b93 b3 b3694 (List.nil : V2) (List.nil : V2) b4339 e4523 e4524 (by rfl)
theorem e4526 : o1.add b3694 (List.nil : V1)=b3694 := by rfl
theorem e4527 : o2.add (List.nil : V2) b4294=b4294 := by rfl
theorem e4528 : o2.add b4339 b4340=b4292 := @add_cons V1 _ o1 b3694 (List.nil : V1) b3694 (List.nil : V2) b4294 b4294 b4292 e4526 e4527 (by rfl)
theorem e4529 : o2.mul b4291 b4=b4292 := @mul_cons V1 _ o1 b93 b4293 b4 b4294 b4339 b4340 b4292 e4522 e4525 (by rfl) e4528
theorem e4530 : o1.mul b92 b3=b3693 := by decide
theorem e4531 : o1.scale b92 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4532 : o1.scale b92 b4=b4341 := @scale_cons V1 _ o1 b92 b3 b3693 (List.nil : V2) (List.nil : V2) b4341 e4530 e4531 (by rfl)
theorem e4533 : o1.add b3693 (List.nil : V1)=b3693 := by rfl
theorem e4534 : o2.add (List.nil : V2) b4292=b4292 := by rfl
theorem e4535 : o2.add b4341 b4342=b4290 := @add_cons V1 _ o1 b3693 (List.nil : V1) b3693 (List.nil : V2) b4292 b4292 b4290 e4533 e4534 (by rfl)
theorem e4536 : o2.mul b4289 b4=b4290 := @mul_cons V1 _ o1 b92 b4291 b4 b4292 b4341 b4342 b4290 e4529 e4532 (by rfl) e4535
theorem e4537 : o1.mul b91 b3=b3692 := by decide
theorem e4538 : o1.scale b91 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4539 : o1.scale b91 b4=b4343 := @scale_cons V1 _ o1 b91 b3 b3692 (List.nil : V2) (List.nil : V2) b4343 e4537 e4538 (by rfl)
theorem e4540 : o1.add b3692 (List.nil : V1)=b3692 := by rfl
theorem e4541 : o2.add (List.nil : V2) b4290=b4290 := by rfl
theorem e4542 : o2.add b4343 b4344=b4288 := @add_cons V1 _ o1 b3692 (List.nil : V1) b3692 (List.nil : V2) b4290 b4290 b4288 e4540 e4541 (by rfl)
theorem e4543 : o2.mul b4287 b4=b4288 := @mul_cons V1 _ o1 b91 b4289 b4 b4290 b4343 b4344 b4288 e4536 e4539 (by rfl) e4542
theorem e4544 : o1.mul b90 b3=b3691 := by decide
theorem e4545 : o1.scale b90 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4546 : o1.scale b90 b4=b4345 := @scale_cons V1 _ o1 b90 b3 b3691 (List.nil : V2) (List.nil : V2) b4345 e4544 e4545 (by rfl)
theorem e4547 : o1.add b3691 (List.nil : V1)=b3691 := by rfl
theorem e4548 : o2.add (List.nil : V2) b4288=b4288 := by rfl
theorem e4549 : o2.add b4345 b4346=b3707 := @add_cons V1 _ o1 b3691 (List.nil : V1) b3691 (List.nil : V2) b4288 b4288 b3707 e4547 e4548 (by rfl)
theorem e4550 : o2.mul b106 b4=b3707 := @mul_cons V1 _ o1 b90 b4287 b4 b4288 b4345 b4346 b3707 e4543 e4546 (by rfl) e4549
theorem e4551 : o2.scale b106 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e4552 : o2.scale b106 b5=b4286 := @scale_cons V2 _ o2 b106 b4 b3707 (List.nil : V3) (List.nil : V3) b4286 e4550 e4551 (by rfl)
theorem e4553 : o2.add b3707 (List.nil : V2)=b3707 := by rfl
theorem e4554 : o3.add (List.nil : V3) b3823=b3823 := by rfl
theorem e4555 : o3.add b4286 b4347=b3821 := @add_cons V2 _ o2 b3707 (List.nil : V2) b3707 (List.nil : V3) b3823 b3823 b3821 e4553 e4554 (by rfl)
theorem e4556 : o3.mul b220 b5=b3821 := @mul_cons V2 _ o2 b106 b3822 b5 b3823 b4286 b4347 b3821 e4440 e4552 (by rfl) e4555
theorem e4557 : o3.mul (List.nil : V3) b13=(List.nil : V3) := by rfl
theorem e4558 : o2.mul (List.nil : V2) b12=(List.nil : V2) := by rfl
theorem e4559 : o1.mul b253 b6=b4461 := by decide
theorem e4560 : o1.mul b253 b7=b4462 := by decide
theorem e4561 : o1.mul b253 b8=b4463 := by decide
theorem e4562 : o1.mul b253 b9=b4464 := by decide
theorem e4563 : o1.mul b253 b10=b4465 := by decide
theorem e4564 : o1.mul b253 b11=b4395 := by decide
theorem e4565 : o1.scale b253 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4566 : o1.scale b253 b4475=b4476 := @scale_cons V1 _ o1 b253 b11 b4395 (List.nil : V2) (List.nil : V2) b4476 e4564 e4565 (by rfl)
theorem e4567 : o1.scale b253 b4473=b4474 := @scale_cons V1 _ o1 b253 b10 b4465 b4475 b4476 b4474 e4563 e4566 (by rfl)
theorem e4568 : o1.scale b253 b4471=b4472 := @scale_cons V1 _ o1 b253 b9 b4464 b4473 b4474 b4472 e4562 e4567 (by rfl)
theorem e4569 : o1.scale b253 b4469=b4470 := @scale_cons V1 _ o1 b253 b8 b4463 b4471 b4472 b4470 e4561 e4568 (by rfl)
theorem e4570 : o1.scale b253 b4467=b4468 := @scale_cons V1 _ o1 b253 b7 b4462 b4469 b4470 b4468 e4560 e4569 (by rfl)
theorem e4571 : o1.scale b253 b12=b4466 := @scale_cons V1 _ o1 b253 b6 b4461 b4467 b4468 b4466 e4559 e4570 (by rfl)
theorem e4572 : o2.add b4466 (List.nil : V2)=b4466 := by rfl
theorem e4573 : o2.mul b4460 b12=b4466 := @mul_cons V1 _ o1 b253 (List.nil : V2) b12 (List.nil : V2) b4466 (List.nil : V2) b4466 e4558 e4571 (by rfl) e4572
theorem e4574 : o1.mul b252 b6=b4454 := by decide
theorem e4575 : o1.mul b252 b7=b4477 := by decide
theorem e4576 : o1.mul b252 b8=b4478 := by decide
theorem e4577 : o1.mul b252 b9=b4479 := by decide
theorem e4578 : o1.mul b252 b10=b4480 := by decide
theorem e4579 : o1.mul b252 b11=b4481 := by decide
theorem e4580 : o1.scale b252 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4581 : o1.scale b252 b4475=b4487 := @scale_cons V1 _ o1 b252 b11 b4481 (List.nil : V2) (List.nil : V2) b4487 e4579 e4580 (by rfl)
theorem e4582 : o1.scale b252 b4473=b4486 := @scale_cons V1 _ o1 b252 b10 b4480 b4475 b4487 b4486 e4578 e4581 (by rfl)
theorem e4583 : o1.scale b252 b4471=b4485 := @scale_cons V1 _ o1 b252 b9 b4479 b4473 b4486 b4485 e4577 e4582 (by rfl)
theorem e4584 : o1.scale b252 b4469=b4484 := @scale_cons V1 _ o1 b252 b8 b4478 b4471 b4485 b4484 e4576 e4583 (by rfl)
theorem e4585 : o1.scale b252 b4467=b4483 := @scale_cons V1 _ o1 b252 b7 b4477 b4469 b4484 b4483 e4575 e4584 (by rfl)
theorem e4586 : o1.scale b252 b12=b4482 := @scale_cons V1 _ o1 b252 b6 b4454 b4467 b4483 b4482 e4574 e4585 (by rfl)
theorem e4587 : o1.add b4454 (List.nil : V1)=b4454 := by rfl
theorem e4588 : o1.add b4477 b4461=b4455 := by decide
theorem e4589 : o1.add b4478 b4462=b4456 := by decide
theorem e4590 : o1.add b4479 b4463=b4457 := by decide
theorem e4591 : o1.add b4480 b4464=b4458 := by decide
theorem e4592 : o1.add b4481 b4465=b4394 := by decide
theorem e4593 : o2.add (List.nil : V2) b4476=b4476 := by rfl
theorem e4594 : o2.add b4487 b4474=b4493 := @add_cons V1 _ o1 b4481 b4465 b4394 (List.nil : V2) b4476 b4476 b4493 e4592 e4593 (by rfl)
theorem e4595 : o2.add b4486 b4472=b4492 := @add_cons V1 _ o1 b4480 b4464 b4458 b4487 b4474 b4493 b4492 e4591 e4594 (by rfl)
theorem e4596 : o2.add b4485 b4470=b4491 := @add_cons V1 _ o1 b4479 b4463 b4457 b4486 b4472 b4492 b4491 e4590 e4595 (by rfl)
theorem e4597 : o2.add b4484 b4468=b4490 := @add_cons V1 _ o1 b4478 b4462 b4456 b4485 b4470 b4491 b4490 e4589 e4596 (by rfl)
theorem e4598 : o2.add b4483 b4466=b4489 := @add_cons V1 _ o1 b4477 b4461 b4455 b4484 b4468 b4490 b4489 e4588 e4597 (by rfl)
theorem e4599 : o2.add b4482 b4488=b4459 := @add_cons V1 _ o1 b4454 (List.nil : V1) b4454 b4483 b4466 b4489 b4459 e4587 e4598 (by rfl)
theorem e4600 : o2.mul b4453 b12=b4459 := @mul_cons V1 _ o1 b252 b4460 b12 b4466 b4482 b4488 b4459 e4573 e4586 (by rfl) e4599
theorem e4601 : o1.mul b251 b6=b4447 := by decide
theorem e4602 : o1.mul b251 b7=b4494 := by decide
theorem e4603 : o1.mul b251 b8=b4495 := by decide
theorem e4604 : o1.mul b251 b9=b4496 := by decide
theorem e4605 : o1.mul b251 b10=b4497 := by decide
theorem e4606 : o1.mul b251 b11=b4498 := by decide
theorem e4607 : o1.scale b251 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4608 : o1.scale b251 b4475=b4504 := @scale_cons V1 _ o1 b251 b11 b4498 (List.nil : V2) (List.nil : V2) b4504 e4606 e4607 (by rfl)
theorem e4609 : o1.scale b251 b4473=b4503 := @scale_cons V1 _ o1 b251 b10 b4497 b4475 b4504 b4503 e4605 e4608 (by rfl)
theorem e4610 : o1.scale b251 b4471=b4502 := @scale_cons V1 _ o1 b251 b9 b4496 b4473 b4503 b4502 e4604 e4609 (by rfl)
theorem e4611 : o1.scale b251 b4469=b4501 := @scale_cons V1 _ o1 b251 b8 b4495 b4471 b4502 b4501 e4603 e4610 (by rfl)
theorem e4612 : o1.scale b251 b4467=b4500 := @scale_cons V1 _ o1 b251 b7 b4494 b4469 b4501 b4500 e4602 e4611 (by rfl)
theorem e4613 : o1.scale b251 b12=b4499 := @scale_cons V1 _ o1 b251 b6 b4447 b4467 b4500 b4499 e4601 e4612 (by rfl)
theorem e4614 : o1.add b4447 (List.nil : V1)=b4447 := by rfl
theorem e4615 : o1.add b4494 b4454=b4448 := by decide
theorem e4616 : o1.add b4495 b4455=b4449 := by decide
theorem e4617 : o1.add b4496 b4456=b4450 := by decide
theorem e4618 : o1.add b4497 b4457=b4451 := by decide
theorem e4619 : o1.add b4498 b4458=b4393 := by decide
theorem e4620 : o2.add (List.nil : V2) b4493=b4493 := by rfl
theorem e4621 : o2.add b4504 b4492=b4510 := @add_cons V1 _ o1 b4498 b4458 b4393 (List.nil : V2) b4493 b4493 b4510 e4619 e4620 (by rfl)
theorem e4622 : o2.add b4503 b4491=b4509 := @add_cons V1 _ o1 b4497 b4457 b4451 b4504 b4492 b4510 b4509 e4618 e4621 (by rfl)
theorem e4623 : o2.add b4502 b4490=b4508 := @add_cons V1 _ o1 b4496 b4456 b4450 b4503 b4491 b4509 b4508 e4617 e4622 (by rfl)
theorem e4624 : o2.add b4501 b4489=b4507 := @add_cons V1 _ o1 b4495 b4455 b4449 b4502 b4490 b4508 b4507 e4616 e4623 (by rfl)
theorem e4625 : o2.add b4500 b4459=b4506 := @add_cons V1 _ o1 b4494 b4454 b4448 b4501 b4489 b4507 b4506 e4615 e4624 (by rfl)
theorem e4626 : o2.add b4499 b4505=b4452 := @add_cons V1 _ o1 b4447 (List.nil : V1) b4447 b4500 b4459 b4506 b4452 e4614 e4625 (by rfl)
theorem e4627 : o2.mul b4446 b12=b4452 := @mul_cons V1 _ o1 b251 b4453 b12 b4459 b4499 b4505 b4452 e4600 e4613 (by rfl) e4626
theorem e4628 : o1.mul b250 b6=b4440 := by decide
theorem e4629 : o1.mul b250 b7=b4511 := by decide
theorem e4630 : o1.mul b250 b8=b4512 := by decide
theorem e4631 : o1.mul b250 b9=b4513 := by decide
theorem e4632 : o1.mul b250 b10=b4514 := by decide
theorem e4633 : o1.mul b250 b11=b4515 := by decide
theorem e4634 : o1.scale b250 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e4635 : o1.scale b250 b4475=b4521 := @scale_cons V1 _ o1 b250 b11 b4515 (List.nil : V2) (List.nil : V2) b4521 e4633 e4634 (by rfl)
theorem e4636 : o1.scale b250 b4473=b4520 := @scale_cons V1 _ o1 b250 b10 b4514 b4475 b4521 b4520 e4632 e4635 (by rfl)
theorem e4637 : o1.scale b250 b4471=b4519 := @scale_cons V1 _ o1 b250 b9 b4513 b4473 b4520 b4519 e4631 e4636 (by rfl)
theorem e4638 : o1.scale b250 b4469=b4518 := @scale_cons V1 _ o1 b250 b8 b4512 b4471 b4519 b4518 e4630 e4637 (by rfl)
theorem e4639 : o1.scale b250 b4467=b4517 := @scale_cons V1 _ o1 b250 b7 b4511 b4469 b4518 b4517 e4629 e4638 (by rfl)
theorem e4640 : o1.scale b250 b12=b4516 := @scale_cons V1 _ o1 b250 b6 b4440 b4467 b4517 b4516 e4628 e4639 (by rfl)
theorem e4641 : o1.add b4440 (List.nil : V1)=b4440 := by rfl
theorem e4642 : o1.add b4511 b4447=b4441 := by decide
theorem e4643 : o1.add b4512 b4448=b4442 := by decide
theorem e4644 : o1.add b4513 b4449=b4443 := by decide
theorem e4645 : o1.add b4514 b4450=b4444 := by decide
theorem e4646 : o1.add b4515 b4451=b4392 := by decide
theorem e4647 : o2.add (List.nil : V2) b4510=b4510 := by rfl
theorem e4648 : o2.add b4521 b4509=b4527 := @add_cons V1 _ o1 b4515 b4451 b4392 (List.nil : V2) b4510 b4510 b4527 e4646 e4647 (by rfl)
theorem e4649 : o2.add b4520 b4508=b4526 := @add_cons V1 _ o1 b4514 b4450 b4444 b4521 b4509 b4527 b4526 e4645 e4648 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
