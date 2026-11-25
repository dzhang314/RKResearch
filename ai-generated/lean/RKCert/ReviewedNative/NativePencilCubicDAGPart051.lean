module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart050

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e7500 : o1.scale b257 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7501 : o1.scale b257 b63=b6720 := @scale_cons V1 _ o1 b257 b62 b5103 (List.nil : V2) (List.nil : V2) b6720 e7499 e7500 (by rfl)
theorem e7502 : o1.add b5103 (List.nil : V1)=b5103 := by rfl
theorem e7503 : o2.add (List.nil : V2) b6671=b6671 := by rfl
theorem e7504 : o2.add b6720 b6721=b6669 := @add_cons V1 _ o1 b5103 (List.nil : V1) b5103 (List.nil : V2) b6671 b6671 b6669 e7502 e7503 (by rfl)
theorem e7505 : o2.mul b6668 b63=b6669 := @mul_cons V1 _ o1 b257 b6670 b63 b6671 b6720 b6721 b6669 e7498 e7501 (by rfl) e7504
theorem e7506 : o1.mul b256 b62=b5102 := by decide
theorem e7507 : o1.scale b256 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e7508 : o1.scale b256 b63=b6722 := @scale_cons V1 _ o1 b256 b62 b5102 (List.nil : V2) (List.nil : V2) b6722 e7506 e7507 (by rfl)
theorem e7509 : o1.add b5102 (List.nil : V1)=b5102 := by rfl
theorem e7510 : o2.add (List.nil : V2) b6669=b6669 := by rfl
theorem e7511 : o2.add b6722 b6723=b6667 := @add_cons V1 _ o1 b5102 (List.nil : V1) b5102 (List.nil : V2) b6669 b6669 b6667 e7509 e7510 (by rfl)
theorem e7512 : o2.mul b6666 b63=b6667 := @mul_cons V1 _ o1 b256 b6668 b63 b6669 b6722 b6723 b6667 e7505 e7508 (by rfl) e7511
theorem e7513 : o2.add (List.nil : V2) b5117=b5117 := by rfl
theorem e7514 : o2.mul b271 b63=b5117 := @mul_cons V1 _ o1 (List.nil : V1) b6666 b63 b6667 (List.nil : V2) b5117 b5117 e7512 e5463 (by rfl) e7513
theorem e7515 : o1.mul b270 b64=b6633 := by decide
theorem e7516 : o1.scale b270 b65=b6739 := @scale_cons V1 _ o1 b270 b64 b6633 (List.nil : V2) (List.nil : V2) b6739 e7515 e7411 (by rfl)
theorem e7517 : o2.add b6739 (List.nil : V2)=b6739 := by rfl
theorem e7518 : o2.mul b6694 b65=b6739 := @mul_cons V1 _ o1 b270 (List.nil : V2) b65 (List.nil : V2) b6739 (List.nil : V2) b6739 e5476 e7516 (by rfl) e7517
theorem e7519 : o1.mul b269 b64=b6632 := by decide
theorem e7520 : o1.scale b269 b65=b6740 := @scale_cons V1 _ o1 b269 b64 b6632 (List.nil : V2) (List.nil : V2) b6740 e7519 e7416 (by rfl)
theorem e7521 : o1.add b6632 (List.nil : V1)=b6632 := by rfl
theorem e7522 : o2.add (List.nil : V2) b6739=b6739 := by rfl
theorem e7523 : o2.add b6740 b6741=b6738 := @add_cons V1 _ o1 b6632 (List.nil : V1) b6632 (List.nil : V2) b6739 b6739 b6738 e7521 e7522 (by rfl)
theorem e7524 : o2.mul b6692 b65=b6738 := @mul_cons V1 _ o1 b269 b6694 b65 b6739 b6740 b6741 b6738 e7518 e7520 (by rfl) e7523
theorem e7525 : o1.mul b268 b64=b6631 := by decide
theorem e7526 : o1.scale b268 b65=b6742 := @scale_cons V1 _ o1 b268 b64 b6631 (List.nil : V2) (List.nil : V2) b6742 e7525 e7423 (by rfl)
theorem e7527 : o1.add b6631 (List.nil : V1)=b6631 := by rfl
theorem e7528 : o2.add (List.nil : V2) b6738=b6738 := by rfl
theorem e7529 : o2.add b6742 b6743=b6737 := @add_cons V1 _ o1 b6631 (List.nil : V1) b6631 (List.nil : V2) b6738 b6738 b6737 e7527 e7528 (by rfl)
theorem e7530 : o2.mul b6690 b65=b6737 := @mul_cons V1 _ o1 b268 b6692 b65 b6738 b6742 b6743 b6737 e7524 e7526 (by rfl) e7529
theorem e7531 : o1.mul b267 b64=b6630 := by decide
theorem e7532 : o1.scale b267 b65=b6744 := @scale_cons V1 _ o1 b267 b64 b6630 (List.nil : V2) (List.nil : V2) b6744 e7531 e7430 (by rfl)
theorem e7533 : o1.add b6630 (List.nil : V1)=b6630 := by rfl
theorem e7534 : o2.add (List.nil : V2) b6737=b6737 := by rfl
theorem e7535 : o2.add b6744 b6745=b6736 := @add_cons V1 _ o1 b6630 (List.nil : V1) b6630 (List.nil : V2) b6737 b6737 b6736 e7533 e7534 (by rfl)
theorem e7536 : o2.mul b6688 b65=b6736 := @mul_cons V1 _ o1 b267 b6690 b65 b6737 b6744 b6745 b6736 e7530 e7532 (by rfl) e7535
theorem e7537 : o1.mul b266 b64=b6629 := by decide
theorem e7538 : o1.scale b266 b65=b6746 := @scale_cons V1 _ o1 b266 b64 b6629 (List.nil : V2) (List.nil : V2) b6746 e7537 e7437 (by rfl)
theorem e7539 : o1.add b6629 (List.nil : V1)=b6629 := by rfl
theorem e7540 : o2.add (List.nil : V2) b6736=b6736 := by rfl
theorem e7541 : o2.add b6746 b6747=b6735 := @add_cons V1 _ o1 b6629 (List.nil : V1) b6629 (List.nil : V2) b6736 b6736 b6735 e7539 e7540 (by rfl)
theorem e7542 : o2.mul b6686 b65=b6735 := @mul_cons V1 _ o1 b266 b6688 b65 b6736 b6746 b6747 b6735 e7536 e7538 (by rfl) e7541
theorem e7543 : o1.mul b265 b64=b6628 := by decide
theorem e7544 : o1.scale b265 b65=b6748 := @scale_cons V1 _ o1 b265 b64 b6628 (List.nil : V2) (List.nil : V2) b6748 e7543 e7444 (by rfl)
theorem e7545 : o1.add b6628 (List.nil : V1)=b6628 := by rfl
theorem e7546 : o2.add (List.nil : V2) b6735=b6735 := by rfl
theorem e7547 : o2.add b6748 b6749=b6734 := @add_cons V1 _ o1 b6628 (List.nil : V1) b6628 (List.nil : V2) b6735 b6735 b6734 e7545 e7546 (by rfl)
theorem e7548 : o2.mul b6684 b65=b6734 := @mul_cons V1 _ o1 b265 b6686 b65 b6735 b6748 b6749 b6734 e7542 e7544 (by rfl) e7547
theorem e7549 : o1.mul b264 b64=b6627 := by decide
theorem e7550 : o1.scale b264 b65=b6750 := @scale_cons V1 _ o1 b264 b64 b6627 (List.nil : V2) (List.nil : V2) b6750 e7549 e7451 (by rfl)
theorem e7551 : o1.add b6627 (List.nil : V1)=b6627 := by rfl
theorem e7552 : o2.add (List.nil : V2) b6734=b6734 := by rfl
theorem e7553 : o2.add b6750 b6751=b6733 := @add_cons V1 _ o1 b6627 (List.nil : V1) b6627 (List.nil : V2) b6734 b6734 b6733 e7551 e7552 (by rfl)
theorem e7554 : o2.mul b6682 b65=b6733 := @mul_cons V1 _ o1 b264 b6684 b65 b6734 b6750 b6751 b6733 e7548 e7550 (by rfl) e7553
theorem e7555 : o1.mul b263 b64=b6626 := by decide
theorem e7556 : o1.scale b263 b65=b6752 := @scale_cons V1 _ o1 b263 b64 b6626 (List.nil : V2) (List.nil : V2) b6752 e7555 e7458 (by rfl)
theorem e7557 : o1.add b6626 (List.nil : V1)=b6626 := by rfl
theorem e7558 : o2.add (List.nil : V2) b6733=b6733 := by rfl
theorem e7559 : o2.add b6752 b6753=b6732 := @add_cons V1 _ o1 b6626 (List.nil : V1) b6626 (List.nil : V2) b6733 b6733 b6732 e7557 e7558 (by rfl)
theorem e7560 : o2.mul b6680 b65=b6732 := @mul_cons V1 _ o1 b263 b6682 b65 b6733 b6752 b6753 b6732 e7554 e7556 (by rfl) e7559
theorem e7561 : o1.mul b262 b64=b6625 := by decide
theorem e7562 : o1.scale b262 b65=b6754 := @scale_cons V1 _ o1 b262 b64 b6625 (List.nil : V2) (List.nil : V2) b6754 e7561 e7465 (by rfl)
theorem e7563 : o1.add b6625 (List.nil : V1)=b6625 := by rfl
theorem e7564 : o2.add (List.nil : V2) b6732=b6732 := by rfl
theorem e7565 : o2.add b6754 b6755=b6731 := @add_cons V1 _ o1 b6625 (List.nil : V1) b6625 (List.nil : V2) b6732 b6732 b6731 e7563 e7564 (by rfl)
theorem e7566 : o2.mul b6678 b65=b6731 := @mul_cons V1 _ o1 b262 b6680 b65 b6732 b6754 b6755 b6731 e7560 e7562 (by rfl) e7565
theorem e7567 : o1.mul b261 b64=b6624 := by decide
theorem e7568 : o1.scale b261 b65=b6756 := @scale_cons V1 _ o1 b261 b64 b6624 (List.nil : V2) (List.nil : V2) b6756 e7567 e7472 (by rfl)
theorem e7569 : o1.add b6624 (List.nil : V1)=b6624 := by rfl
theorem e7570 : o2.add (List.nil : V2) b6731=b6731 := by rfl
theorem e7571 : o2.add b6756 b6757=b6730 := @add_cons V1 _ o1 b6624 (List.nil : V1) b6624 (List.nil : V2) b6731 b6731 b6730 e7569 e7570 (by rfl)
theorem e7572 : o2.mul b6676 b65=b6730 := @mul_cons V1 _ o1 b261 b6678 b65 b6731 b6756 b6757 b6730 e7566 e7568 (by rfl) e7571
theorem e7573 : o1.mul b260 b64=b6623 := by decide
theorem e7574 : o1.scale b260 b65=b6758 := @scale_cons V1 _ o1 b260 b64 b6623 (List.nil : V2) (List.nil : V2) b6758 e7573 e7479 (by rfl)
theorem e7575 : o1.add b6623 (List.nil : V1)=b6623 := by rfl
theorem e7576 : o2.add (List.nil : V2) b6730=b6730 := by rfl
theorem e7577 : o2.add b6758 b6759=b6729 := @add_cons V1 _ o1 b6623 (List.nil : V1) b6623 (List.nil : V2) b6730 b6730 b6729 e7575 e7576 (by rfl)
theorem e7578 : o2.mul b6674 b65=b6729 := @mul_cons V1 _ o1 b260 b6676 b65 b6730 b6758 b6759 b6729 e7572 e7574 (by rfl) e7577
theorem e7579 : o1.mul b259 b64=b6622 := by decide
theorem e7580 : o1.scale b259 b65=b6760 := @scale_cons V1 _ o1 b259 b64 b6622 (List.nil : V2) (List.nil : V2) b6760 e7579 e7486 (by rfl)
theorem e7581 : o1.add b6622 (List.nil : V1)=b6622 := by rfl
theorem e7582 : o2.add (List.nil : V2) b6729=b6729 := by rfl
theorem e7583 : o2.add b6760 b6761=b6728 := @add_cons V1 _ o1 b6622 (List.nil : V1) b6622 (List.nil : V2) b6729 b6729 b6728 e7581 e7582 (by rfl)
theorem e7584 : o2.mul b6672 b65=b6728 := @mul_cons V1 _ o1 b259 b6674 b65 b6729 b6760 b6761 b6728 e7578 e7580 (by rfl) e7583
theorem e7585 : o1.mul b258 b64=b6621 := by decide
theorem e7586 : o1.scale b258 b65=b6762 := @scale_cons V1 _ o1 b258 b64 b6621 (List.nil : V2) (List.nil : V2) b6762 e7585 e7493 (by rfl)
theorem e7587 : o1.add b6621 (List.nil : V1)=b6621 := by rfl
theorem e7588 : o2.add (List.nil : V2) b6728=b6728 := by rfl
theorem e7589 : o2.add b6762 b6763=b6727 := @add_cons V1 _ o1 b6621 (List.nil : V1) b6621 (List.nil : V2) b6728 b6728 b6727 e7587 e7588 (by rfl)
theorem e7590 : o2.mul b6670 b65=b6727 := @mul_cons V1 _ o1 b258 b6672 b65 b6728 b6762 b6763 b6727 e7584 e7586 (by rfl) e7589
theorem e7591 : o1.mul b257 b64=b6620 := by decide
theorem e7592 : o1.scale b257 b65=b6764 := @scale_cons V1 _ o1 b257 b64 b6620 (List.nil : V2) (List.nil : V2) b6764 e7591 e7500 (by rfl)
theorem e7593 : o1.add b6620 (List.nil : V1)=b6620 := by rfl
theorem e7594 : o2.add (List.nil : V2) b6727=b6727 := by rfl
theorem e7595 : o2.add b6764 b6765=b6726 := @add_cons V1 _ o1 b6620 (List.nil : V1) b6620 (List.nil : V2) b6727 b6727 b6726 e7593 e7594 (by rfl)
theorem e7596 : o2.mul b6668 b65=b6726 := @mul_cons V1 _ o1 b257 b6670 b65 b6727 b6764 b6765 b6726 e7590 e7592 (by rfl) e7595
theorem e7597 : o1.mul b256 b64=b5118 := by decide
theorem e7598 : o1.scale b256 b65=b6766 := @scale_cons V1 _ o1 b256 b64 b5118 (List.nil : V2) (List.nil : V2) b6766 e7597 e7507 (by rfl)
theorem e7599 : o1.add b5118 (List.nil : V1)=b5118 := by rfl
theorem e7600 : o2.add (List.nil : V2) b6726=b6726 := by rfl
theorem e7601 : o2.add b6766 b6767=b6725 := @add_cons V1 _ o1 b5118 (List.nil : V1) b5118 (List.nil : V2) b6726 b6726 b6725 e7599 e7600 (by rfl)
theorem e7602 : o2.mul b6666 b65=b6725 := @mul_cons V1 _ o1 b256 b6668 b65 b6726 b6766 b6767 b6725 e7596 e7598 (by rfl) e7601
theorem e7603 : o2.add (List.nil : V2) b6634=b6634 := by rfl
theorem e7604 : o2.mul b271 b65=b6634 := @mul_cons V1 _ o1 (List.nil : V1) b6666 b65 b6725 (List.nil : V2) b6634 b6634 e7602 e5536 (by rfl) e7603
theorem e7605 : o1.mul b270 b66=b6648 := by decide
theorem e7606 : o1.scale b270 b67=b6783 := @scale_cons V1 _ o1 b270 b66 b6648 (List.nil : V2) (List.nil : V2) b6783 e7605 e7411 (by rfl)
theorem e7607 : o2.add b6783 (List.nil : V2)=b6783 := by rfl
theorem e7608 : o2.mul b6694 b67=b6783 := @mul_cons V1 _ o1 b270 (List.nil : V2) b67 (List.nil : V2) b6783 (List.nil : V2) b6783 e5549 e7606 (by rfl) e7607
theorem e7609 : o1.mul b269 b66=b6647 := by decide
theorem e7610 : o1.scale b269 b67=b6784 := @scale_cons V1 _ o1 b269 b66 b6647 (List.nil : V2) (List.nil : V2) b6784 e7609 e7416 (by rfl)
theorem e7611 : o1.add b6647 (List.nil : V1)=b6647 := by rfl
theorem e7612 : o2.add (List.nil : V2) b6783=b6783 := by rfl
theorem e7613 : o2.add b6784 b6785=b6782 := @add_cons V1 _ o1 b6647 (List.nil : V1) b6647 (List.nil : V2) b6783 b6783 b6782 e7611 e7612 (by rfl)
theorem e7614 : o2.mul b6692 b67=b6782 := @mul_cons V1 _ o1 b269 b6694 b67 b6783 b6784 b6785 b6782 e7608 e7610 (by rfl) e7613
theorem e7615 : o1.mul b268 b66=b6646 := by decide
theorem e7616 : o1.scale b268 b67=b6786 := @scale_cons V1 _ o1 b268 b66 b6646 (List.nil : V2) (List.nil : V2) b6786 e7615 e7423 (by rfl)
theorem e7617 : o1.add b6646 (List.nil : V1)=b6646 := by rfl
theorem e7618 : o2.add (List.nil : V2) b6782=b6782 := by rfl
theorem e7619 : o2.add b6786 b6787=b6781 := @add_cons V1 _ o1 b6646 (List.nil : V1) b6646 (List.nil : V2) b6782 b6782 b6781 e7617 e7618 (by rfl)
theorem e7620 : o2.mul b6690 b67=b6781 := @mul_cons V1 _ o1 b268 b6692 b67 b6782 b6786 b6787 b6781 e7614 e7616 (by rfl) e7619
theorem e7621 : o1.mul b267 b66=b6645 := by decide
theorem e7622 : o1.scale b267 b67=b6788 := @scale_cons V1 _ o1 b267 b66 b6645 (List.nil : V2) (List.nil : V2) b6788 e7621 e7430 (by rfl)
theorem e7623 : o1.add b6645 (List.nil : V1)=b6645 := by rfl
theorem e7624 : o2.add (List.nil : V2) b6781=b6781 := by rfl
theorem e7625 : o2.add b6788 b6789=b6780 := @add_cons V1 _ o1 b6645 (List.nil : V1) b6645 (List.nil : V2) b6781 b6781 b6780 e7623 e7624 (by rfl)
theorem e7626 : o2.mul b6688 b67=b6780 := @mul_cons V1 _ o1 b267 b6690 b67 b6781 b6788 b6789 b6780 e7620 e7622 (by rfl) e7625
theorem e7627 : o1.mul b266 b66=b6644 := by decide
theorem e7628 : o1.scale b266 b67=b6790 := @scale_cons V1 _ o1 b266 b66 b6644 (List.nil : V2) (List.nil : V2) b6790 e7627 e7437 (by rfl)
theorem e7629 : o1.add b6644 (List.nil : V1)=b6644 := by rfl
theorem e7630 : o2.add (List.nil : V2) b6780=b6780 := by rfl
theorem e7631 : o2.add b6790 b6791=b6779 := @add_cons V1 _ o1 b6644 (List.nil : V1) b6644 (List.nil : V2) b6780 b6780 b6779 e7629 e7630 (by rfl)
theorem e7632 : o2.mul b6686 b67=b6779 := @mul_cons V1 _ o1 b266 b6688 b67 b6780 b6790 b6791 b6779 e7626 e7628 (by rfl) e7631
theorem e7633 : o1.mul b265 b66=b6643 := by decide
theorem e7634 : o1.scale b265 b67=b6792 := @scale_cons V1 _ o1 b265 b66 b6643 (List.nil : V2) (List.nil : V2) b6792 e7633 e7444 (by rfl)
theorem e7635 : o1.add b6643 (List.nil : V1)=b6643 := by rfl
theorem e7636 : o2.add (List.nil : V2) b6779=b6779 := by rfl
theorem e7637 : o2.add b6792 b6793=b6778 := @add_cons V1 _ o1 b6643 (List.nil : V1) b6643 (List.nil : V2) b6779 b6779 b6778 e7635 e7636 (by rfl)
theorem e7638 : o2.mul b6684 b67=b6778 := @mul_cons V1 _ o1 b265 b6686 b67 b6779 b6792 b6793 b6778 e7632 e7634 (by rfl) e7637
theorem e7639 : o1.mul b264 b66=b6642 := by decide
theorem e7640 : o1.scale b264 b67=b6794 := @scale_cons V1 _ o1 b264 b66 b6642 (List.nil : V2) (List.nil : V2) b6794 e7639 e7451 (by rfl)
theorem e7641 : o1.add b6642 (List.nil : V1)=b6642 := by rfl
theorem e7642 : o2.add (List.nil : V2) b6778=b6778 := by rfl
theorem e7643 : o2.add b6794 b6795=b6777 := @add_cons V1 _ o1 b6642 (List.nil : V1) b6642 (List.nil : V2) b6778 b6778 b6777 e7641 e7642 (by rfl)
theorem e7644 : o2.mul b6682 b67=b6777 := @mul_cons V1 _ o1 b264 b6684 b67 b6778 b6794 b6795 b6777 e7638 e7640 (by rfl) e7643
theorem e7645 : o1.mul b263 b66=b6641 := by decide
theorem e7646 : o1.scale b263 b67=b6796 := @scale_cons V1 _ o1 b263 b66 b6641 (List.nil : V2) (List.nil : V2) b6796 e7645 e7458 (by rfl)
theorem e7647 : o1.add b6641 (List.nil : V1)=b6641 := by rfl
theorem e7648 : o2.add (List.nil : V2) b6777=b6777 := by rfl
theorem e7649 : o2.add b6796 b6797=b6776 := @add_cons V1 _ o1 b6641 (List.nil : V1) b6641 (List.nil : V2) b6777 b6777 b6776 e7647 e7648 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
