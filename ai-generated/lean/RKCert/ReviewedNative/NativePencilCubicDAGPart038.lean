module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart037

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5550 : o1.mul b335 b66=b5434 := by decide
theorem e5551 : o1.scale b335 b67=b5536 := @scale_cons V1 _ o1 b335 b66 b5434 (List.nil : V2) (List.nil : V2) b5536 e5550 e5395 (by rfl)
theorem e5552 : o2.add b5536 (List.nil : V2)=b5536 := by rfl
theorem e5553 : o2.mul b5465 b67=b5536 := @mul_cons V1 _ o1 b335 (List.nil : V2) b67 (List.nil : V2) b5536 (List.nil : V2) b5536 e5549 e5551 (by rfl) e5552
theorem e5554 : o1.mul b334 b66=b5433 := by decide
theorem e5555 : o1.scale b334 b67=b5537 := @scale_cons V1 _ o1 b334 b66 b5433 (List.nil : V2) (List.nil : V2) b5537 e5554 e5400 (by rfl)
theorem e5556 : o1.add b5433 (List.nil : V1)=b5433 := by rfl
theorem e5557 : o2.add (List.nil : V2) b5536=b5536 := by rfl
theorem e5558 : o2.add b5537 b5538=b5535 := @add_cons V1 _ o1 b5433 (List.nil : V1) b5433 (List.nil : V2) b5536 b5536 b5535 e5556 e5557 (by rfl)
theorem e5559 : o2.mul b5463 b67=b5535 := @mul_cons V1 _ o1 b334 b5465 b67 b5536 b5537 b5538 b5535 e5553 e5555 (by rfl) e5558
theorem e5560 : o1.mul b333 b66=b5432 := by decide
theorem e5561 : o1.scale b333 b67=b5539 := @scale_cons V1 _ o1 b333 b66 b5432 (List.nil : V2) (List.nil : V2) b5539 e5560 e5407 (by rfl)
theorem e5562 : o1.add b5432 (List.nil : V1)=b5432 := by rfl
theorem e5563 : o2.add (List.nil : V2) b5535=b5535 := by rfl
theorem e5564 : o2.add b5539 b5540=b5534 := @add_cons V1 _ o1 b5432 (List.nil : V1) b5432 (List.nil : V2) b5535 b5535 b5534 e5562 e5563 (by rfl)
theorem e5565 : o2.mul b5461 b67=b5534 := @mul_cons V1 _ o1 b333 b5463 b67 b5535 b5539 b5540 b5534 e5559 e5561 (by rfl) e5564
theorem e5566 : o1.mul b332 b66=b5431 := by decide
theorem e5567 : o1.scale b332 b67=b5541 := @scale_cons V1 _ o1 b332 b66 b5431 (List.nil : V2) (List.nil : V2) b5541 e5566 e5414 (by rfl)
theorem e5568 : o1.add b5431 (List.nil : V1)=b5431 := by rfl
theorem e5569 : o2.add (List.nil : V2) b5534=b5534 := by rfl
theorem e5570 : o2.add b5541 b5542=b5533 := @add_cons V1 _ o1 b5431 (List.nil : V1) b5431 (List.nil : V2) b5534 b5534 b5533 e5568 e5569 (by rfl)
theorem e5571 : o2.mul b5459 b67=b5533 := @mul_cons V1 _ o1 b332 b5461 b67 b5534 b5541 b5542 b5533 e5565 e5567 (by rfl) e5570
theorem e5572 : o1.mul b331 b66=b5430 := by decide
theorem e5573 : o1.scale b331 b67=b5543 := @scale_cons V1 _ o1 b331 b66 b5430 (List.nil : V2) (List.nil : V2) b5543 e5572 e5421 (by rfl)
theorem e5574 : o1.add b5430 (List.nil : V1)=b5430 := by rfl
theorem e5575 : o2.add (List.nil : V2) b5533=b5533 := by rfl
theorem e5576 : o2.add b5543 b5544=b5532 := @add_cons V1 _ o1 b5430 (List.nil : V1) b5430 (List.nil : V2) b5533 b5533 b5532 e5574 e5575 (by rfl)
theorem e5577 : o2.mul b5457 b67=b5532 := @mul_cons V1 _ o1 b331 b5459 b67 b5533 b5543 b5544 b5532 e5571 e5573 (by rfl) e5576
theorem e5578 : o1.mul b330 b66=b5429 := by decide
theorem e5579 : o1.scale b330 b67=b5545 := @scale_cons V1 _ o1 b330 b66 b5429 (List.nil : V2) (List.nil : V2) b5545 e5578 e5428 (by rfl)
theorem e5580 : o1.add b5429 (List.nil : V1)=b5429 := by rfl
theorem e5581 : o2.add (List.nil : V2) b5532=b5532 := by rfl
theorem e5582 : o2.add b5545 b5546=b5531 := @add_cons V1 _ o1 b5429 (List.nil : V1) b5429 (List.nil : V2) b5532 b5532 b5531 e5580 e5581 (by rfl)
theorem e5583 : o2.mul b5455 b67=b5531 := @mul_cons V1 _ o1 b330 b5457 b67 b5532 b5545 b5546 b5531 e5577 e5579 (by rfl) e5582
theorem e5584 : o1.mul b329 b66=b5428 := by decide
theorem e5585 : o1.scale b329 b67=b5547 := @scale_cons V1 _ o1 b329 b66 b5428 (List.nil : V2) (List.nil : V2) b5547 e5584 e5435 (by rfl)
theorem e5586 : o1.add b5428 (List.nil : V1)=b5428 := by rfl
theorem e5587 : o2.add (List.nil : V2) b5531=b5531 := by rfl
theorem e5588 : o2.add b5547 b5548=b5530 := @add_cons V1 _ o1 b5428 (List.nil : V1) b5428 (List.nil : V2) b5531 b5531 b5530 e5586 e5587 (by rfl)
theorem e5589 : o2.mul b5453 b67=b5530 := @mul_cons V1 _ o1 b329 b5455 b67 b5531 b5547 b5548 b5530 e5583 e5585 (by rfl) e5588
theorem e5590 : o1.mul b328 b66=b5427 := by decide
theorem e5591 : o1.scale b328 b67=b5549 := @scale_cons V1 _ o1 b328 b66 b5427 (List.nil : V2) (List.nil : V2) b5549 e5590 e5442 (by rfl)
theorem e5592 : o1.add b5427 (List.nil : V1)=b5427 := by rfl
theorem e5593 : o2.add (List.nil : V2) b5530=b5530 := by rfl
theorem e5594 : o2.add b5549 b5550=b5529 := @add_cons V1 _ o1 b5427 (List.nil : V1) b5427 (List.nil : V2) b5530 b5530 b5529 e5592 e5593 (by rfl)
theorem e5595 : o2.mul b5451 b67=b5529 := @mul_cons V1 _ o1 b328 b5453 b67 b5530 b5549 b5550 b5529 e5589 e5591 (by rfl) e5594
theorem e5596 : o1.mul b327 b66=b5426 := by decide
theorem e5597 : o1.scale b327 b67=b5551 := @scale_cons V1 _ o1 b327 b66 b5426 (List.nil : V2) (List.nil : V2) b5551 e5596 e5449 (by rfl)
theorem e5598 : o1.add b5426 (List.nil : V1)=b5426 := by rfl
theorem e5599 : o2.add (List.nil : V2) b5529=b5529 := by rfl
theorem e5600 : o2.add b5551 b5552=b5528 := @add_cons V1 _ o1 b5426 (List.nil : V1) b5426 (List.nil : V2) b5529 b5529 b5528 e5598 e5599 (by rfl)
theorem e5601 : o2.mul b5449 b67=b5528 := @mul_cons V1 _ o1 b327 b5451 b67 b5529 b5551 b5552 b5528 e5595 e5597 (by rfl) e5600
theorem e5602 : o1.mul b326 b66=b5425 := by decide
theorem e5603 : o1.scale b326 b67=b5553 := @scale_cons V1 _ o1 b326 b66 b5425 (List.nil : V2) (List.nil : V2) b5553 e5602 e5456 (by rfl)
theorem e5604 : o1.add b5425 (List.nil : V1)=b5425 := by rfl
theorem e5605 : o2.add (List.nil : V2) b5528=b5528 := by rfl
theorem e5606 : o2.add b5553 b5554=b5527 := @add_cons V1 _ o1 b5425 (List.nil : V1) b5425 (List.nil : V2) b5528 b5528 b5527 e5604 e5605 (by rfl)
theorem e5607 : o2.mul b5447 b67=b5527 := @mul_cons V1 _ o1 b326 b5449 b67 b5528 b5553 b5554 b5527 e5601 e5603 (by rfl) e5606
theorem e5608 : o1.mul (List.nil : V1) b66=(List.nil : V1) := by rfl
theorem e5609 : o1.scale (List.nil : V1) b67=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b66 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e5608 e3696 (by rfl)
theorem e5610 : o2.add (List.nil : V2) b5526=b5526 := by rfl
theorem e5611 : o2.mul b5445 b67=b5526 := @mul_cons V1 _ o1 (List.nil : V1) b5447 b67 b5527 (List.nil : V2) b5526 b5526 e5607 e5609 (by rfl) e5610
theorem e5612 : o2.add (List.nil : V2) b5525=b5525 := by rfl
theorem e5613 : o2.mul b5443 b67=b5525 := @mul_cons V1 _ o1 (List.nil : V1) b5445 b67 b5526 (List.nil : V2) b5525 b5525 e5611 e5609 (by rfl) e5612
theorem e5614 : o2.add (List.nil : V2) b5524=b5524 := by rfl
theorem e5615 : o2.mul b5441 b67=b5524 := @mul_cons V1 _ o1 (List.nil : V1) b5443 b67 b5525 (List.nil : V2) b5524 b5524 e5613 e5609 (by rfl) e5614
theorem e5616 : o2.add (List.nil : V2) b5523=b5523 := by rfl
theorem e5617 : o2.mul b5439 b67=b5523 := @mul_cons V1 _ o1 (List.nil : V1) b5441 b67 b5524 (List.nil : V2) b5523 b5523 e5615 e5609 (by rfl) e5616
theorem e5618 : o2.add (List.nil : V2) b5522=b5522 := by rfl
theorem e5619 : o2.mul b5437 b67=b5522 := @mul_cons V1 _ o1 (List.nil : V1) b5439 b67 b5523 (List.nil : V2) b5522 b5522 e5617 e5609 (by rfl) e5618
theorem e5620 : o2.add (List.nil : V2) b5435=b5435 := by rfl
theorem e5621 : o2.mul b336 b67=b5435 := @mul_cons V1 _ o1 (List.nil : V1) b5437 b67 b5522 (List.nil : V2) b5435 b5435 e5619 e5609 (by rfl) e5620
theorem e5622 : o2.mul (List.nil : V2) b69=(List.nil : V2) := by rfl
theorem e5623 : o1.mul b335 b68=b5229 := by decide
theorem e5624 : o1.scale b335 b69=b5571 := @scale_cons V1 _ o1 b335 b68 b5229 (List.nil : V2) (List.nil : V2) b5571 e5623 e5395 (by rfl)
theorem e5625 : o2.add b5571 (List.nil : V2)=b5571 := by rfl
theorem e5626 : o2.mul b5465 b69=b5571 := @mul_cons V1 _ o1 b335 (List.nil : V2) b69 (List.nil : V2) b5571 (List.nil : V2) b5571 e5622 e5624 (by rfl) e5625
theorem e5627 : o1.mul b334 b68=b5228 := by decide
theorem e5628 : o1.scale b334 b69=b5572 := @scale_cons V1 _ o1 b334 b68 b5228 (List.nil : V2) (List.nil : V2) b5572 e5627 e5400 (by rfl)
theorem e5629 : o1.add b5228 (List.nil : V1)=b5228 := by rfl
theorem e5630 : o2.add (List.nil : V2) b5571=b5571 := by rfl
theorem e5631 : o2.add b5572 b5573=b5570 := @add_cons V1 _ o1 b5228 (List.nil : V1) b5228 (List.nil : V2) b5571 b5571 b5570 e5629 e5630 (by rfl)
theorem e5632 : o2.mul b5463 b69=b5570 := @mul_cons V1 _ o1 b334 b5465 b69 b5571 b5572 b5573 b5570 e5626 e5628 (by rfl) e5631
theorem e5633 : o1.mul b333 b68=b5227 := by decide
theorem e5634 : o1.scale b333 b69=b5574 := @scale_cons V1 _ o1 b333 b68 b5227 (List.nil : V2) (List.nil : V2) b5574 e5633 e5407 (by rfl)
theorem e5635 : o1.add b5227 (List.nil : V1)=b5227 := by rfl
theorem e5636 : o2.add (List.nil : V2) b5570=b5570 := by rfl
theorem e5637 : o2.add b5574 b5575=b5569 := @add_cons V1 _ o1 b5227 (List.nil : V1) b5227 (List.nil : V2) b5570 b5570 b5569 e5635 e5636 (by rfl)
theorem e5638 : o2.mul b5461 b69=b5569 := @mul_cons V1 _ o1 b333 b5463 b69 b5570 b5574 b5575 b5569 e5632 e5634 (by rfl) e5637
theorem e5639 : o1.mul b332 b68=b5226 := by decide
theorem e5640 : o1.scale b332 b69=b5576 := @scale_cons V1 _ o1 b332 b68 b5226 (List.nil : V2) (List.nil : V2) b5576 e5639 e5414 (by rfl)
theorem e5641 : o1.add b5226 (List.nil : V1)=b5226 := by rfl
theorem e5642 : o2.add (List.nil : V2) b5569=b5569 := by rfl
theorem e5643 : o2.add b5576 b5577=b5568 := @add_cons V1 _ o1 b5226 (List.nil : V1) b5226 (List.nil : V2) b5569 b5569 b5568 e5641 e5642 (by rfl)
theorem e5644 : o2.mul b5459 b69=b5568 := @mul_cons V1 _ o1 b332 b5461 b69 b5569 b5576 b5577 b5568 e5638 e5640 (by rfl) e5643
theorem e5645 : o1.mul b331 b68=b5225 := by decide
theorem e5646 : o1.scale b331 b69=b5578 := @scale_cons V1 _ o1 b331 b68 b5225 (List.nil : V2) (List.nil : V2) b5578 e5645 e5421 (by rfl)
theorem e5647 : o1.add b5225 (List.nil : V1)=b5225 := by rfl
theorem e5648 : o2.add (List.nil : V2) b5568=b5568 := by rfl
theorem e5649 : o2.add b5578 b5579=b5567 := @add_cons V1 _ o1 b5225 (List.nil : V1) b5225 (List.nil : V2) b5568 b5568 b5567 e5647 e5648 (by rfl)
theorem e5650 : o2.mul b5457 b69=b5567 := @mul_cons V1 _ o1 b331 b5459 b69 b5568 b5578 b5579 b5567 e5644 e5646 (by rfl) e5649
theorem e5651 : o1.mul b330 b68=b5224 := by decide
theorem e5652 : o1.scale b330 b69=b5580 := @scale_cons V1 _ o1 b330 b68 b5224 (List.nil : V2) (List.nil : V2) b5580 e5651 e5428 (by rfl)
theorem e5653 : o1.add b5224 (List.nil : V1)=b5224 := by rfl
theorem e5654 : o2.add (List.nil : V2) b5567=b5567 := by rfl
theorem e5655 : o2.add b5580 b5581=b5566 := @add_cons V1 _ o1 b5224 (List.nil : V1) b5224 (List.nil : V2) b5567 b5567 b5566 e5653 e5654 (by rfl)
theorem e5656 : o2.mul b5455 b69=b5566 := @mul_cons V1 _ o1 b330 b5457 b69 b5567 b5580 b5581 b5566 e5650 e5652 (by rfl) e5655
theorem e5657 : o1.mul b329 b68=b5223 := by decide
theorem e5658 : o1.scale b329 b69=b5582 := @scale_cons V1 _ o1 b329 b68 b5223 (List.nil : V2) (List.nil : V2) b5582 e5657 e5435 (by rfl)
theorem e5659 : o1.add b5223 (List.nil : V1)=b5223 := by rfl
theorem e5660 : o2.add (List.nil : V2) b5566=b5566 := by rfl
theorem e5661 : o2.add b5582 b5583=b5565 := @add_cons V1 _ o1 b5223 (List.nil : V1) b5223 (List.nil : V2) b5566 b5566 b5565 e5659 e5660 (by rfl)
theorem e5662 : o2.mul b5453 b69=b5565 := @mul_cons V1 _ o1 b329 b5455 b69 b5566 b5582 b5583 b5565 e5656 e5658 (by rfl) e5661
theorem e5663 : o1.mul b328 b68=b5222 := by decide
theorem e5664 : o1.scale b328 b69=b5584 := @scale_cons V1 _ o1 b328 b68 b5222 (List.nil : V2) (List.nil : V2) b5584 e5663 e5442 (by rfl)
theorem e5665 : o1.add b5222 (List.nil : V1)=b5222 := by rfl
theorem e5666 : o2.add (List.nil : V2) b5565=b5565 := by rfl
theorem e5667 : o2.add b5584 b5585=b5564 := @add_cons V1 _ o1 b5222 (List.nil : V1) b5222 (List.nil : V2) b5565 b5565 b5564 e5665 e5666 (by rfl)
theorem e5668 : o2.mul b5451 b69=b5564 := @mul_cons V1 _ o1 b328 b5453 b69 b5565 b5584 b5585 b5564 e5662 e5664 (by rfl) e5667
theorem e5669 : o1.mul b327 b68=b5221 := by decide
theorem e5670 : o1.scale b327 b69=b5586 := @scale_cons V1 _ o1 b327 b68 b5221 (List.nil : V2) (List.nil : V2) b5586 e5669 e5449 (by rfl)
theorem e5671 : o1.add b5221 (List.nil : V1)=b5221 := by rfl
theorem e5672 : o2.add (List.nil : V2) b5564=b5564 := by rfl
theorem e5673 : o2.add b5586 b5587=b5563 := @add_cons V1 _ o1 b5221 (List.nil : V1) b5221 (List.nil : V2) b5564 b5564 b5563 e5671 e5672 (by rfl)
theorem e5674 : o2.mul b5449 b69=b5563 := @mul_cons V1 _ o1 b327 b5451 b69 b5564 b5586 b5587 b5563 e5668 e5670 (by rfl) e5673
theorem e5675 : o1.mul b326 b68=b5220 := by decide
theorem e5676 : o1.scale b326 b69=b5588 := @scale_cons V1 _ o1 b326 b68 b5220 (List.nil : V2) (List.nil : V2) b5588 e5675 e5456 (by rfl)
theorem e5677 : o1.add b5220 (List.nil : V1)=b5220 := by rfl
theorem e5678 : o2.add (List.nil : V2) b5563=b5563 := by rfl
theorem e5679 : o2.add b5588 b5589=b5562 := @add_cons V1 _ o1 b5220 (List.nil : V1) b5220 (List.nil : V2) b5563 b5563 b5562 e5677 e5678 (by rfl)
theorem e5680 : o2.mul b5447 b69=b5562 := @mul_cons V1 _ o1 b326 b5449 b69 b5563 b5588 b5589 b5562 e5674 e5676 (by rfl) e5679
theorem e5681 : o1.mul (List.nil : V1) b68=(List.nil : V1) := by rfl
theorem e5682 : o1.scale (List.nil : V1) b69=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b68 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e5681 e3696 (by rfl)
theorem e5683 : o2.add (List.nil : V2) b5561=b5561 := by rfl
theorem e5684 : o2.mul b5445 b69=b5561 := @mul_cons V1 _ o1 (List.nil : V1) b5447 b69 b5562 (List.nil : V2) b5561 b5561 e5680 e5682 (by rfl) e5683
theorem e5685 : o2.add (List.nil : V2) b5560=b5560 := by rfl
theorem e5686 : o2.mul b5443 b69=b5560 := @mul_cons V1 _ o1 (List.nil : V1) b5445 b69 b5561 (List.nil : V2) b5560 b5560 e5684 e5682 (by rfl) e5685
theorem e5687 : o2.add (List.nil : V2) b5559=b5559 := by rfl
theorem e5688 : o2.mul b5441 b69=b5559 := @mul_cons V1 _ o1 (List.nil : V1) b5443 b69 b5560 (List.nil : V2) b5559 b5559 e5686 e5682 (by rfl) e5687
theorem e5689 : o2.add (List.nil : V2) b5558=b5558 := by rfl
theorem e5690 : o2.mul b5439 b69=b5558 := @mul_cons V1 _ o1 (List.nil : V1) b5441 b69 b5559 (List.nil : V2) b5558 b5558 e5688 e5682 (by rfl) e5689
theorem e5691 : o2.add (List.nil : V2) b5557=b5557 := by rfl
theorem e5692 : o2.mul b5437 b69=b5557 := @mul_cons V1 _ o1 (List.nil : V1) b5439 b69 b5558 (List.nil : V2) b5557 b5557 e5690 e5682 (by rfl) e5691
theorem e5693 : o2.add (List.nil : V2) b5230=b5230 := by rfl
theorem e5694 : o2.mul b336 b69=b5230 := @mul_cons V1 _ o1 (List.nil : V1) b5437 b69 b5557 (List.nil : V2) b5230 b5230 e5692 e5682 (by rfl) e5693
theorem e5695 : o2.scale b336 (List.nil : V3)=(List.nil : V3) := by rfl
theorem e5696 : o2.scale b336 b5555=b5556 := @scale_cons V2 _ o2 b336 b69 b5230 (List.nil : V3) (List.nil : V3) b5556 e5694 e5695 (by rfl)
theorem e5697 : o2.scale b336 b5520=b5521 := @scale_cons V2 _ o2 b336 b67 b5435 b5555 b5556 b5521 e5621 e5696 (by rfl)
theorem e5698 : o2.scale b336 b5485=b5486 := @scale_cons V2 _ o2 b336 b65 b5424 b5520 b5521 b5486 e5548 e5697 (by rfl)
theorem e5699 : o2.scale b336 b70=b5436 := @scale_cons V2 _ o2 b336 b63 b5413 b5485 b5486 b5436 e5475 e5698 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
