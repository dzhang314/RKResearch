module

public import RKCert.ReviewedNative.NativePencilCubicDAGData

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e0 : o3.mul (List.nil : V3) b61=(List.nil : V3) := by rfl
theorem e1 : o2.mul (List.nil : V2) b20=(List.nil : V2) := by rfl
theorem e2 : o1.mul b87 (List.nil : V1)=(List.nil : V1) := by decide
theorem e3 : o1.mul b87 b14=b611 := by decide
theorem e4 : o1.mul b87 b15=b612 := by decide
theorem e5 : o1.mul b87 b16=b613 := by decide
theorem e6 : o1.mul b87 b17=b614 := by decide
theorem e7 : o1.mul b87 b18=b615 := by decide
theorem e8 : o1.mul b87 b19=b531 := by decide
theorem e9 : o1.scale b87 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e10 : o1.scale b87 b627=b628 := @scale_cons V1 _ o1 b87 b19 b531 (List.nil : V2) (List.nil : V2) b628 e8 e9 (by rfl)
theorem e11 : o1.scale b87 b625=b626 := @scale_cons V1 _ o1 b87 b18 b615 b627 b628 b626 e7 e10 (by rfl)
theorem e12 : o1.scale b87 b623=b624 := @scale_cons V1 _ o1 b87 b17 b614 b625 b626 b624 e6 e11 (by rfl)
theorem e13 : o1.scale b87 b621=b622 := @scale_cons V1 _ o1 b87 b16 b613 b623 b624 b622 e5 e12 (by rfl)
theorem e14 : o1.scale b87 b619=b620 := @scale_cons V1 _ o1 b87 b15 b612 b621 b622 b620 e4 e13 (by rfl)
theorem e15 : o1.scale b87 b617=b618 := @scale_cons V1 _ o1 b87 b14 b611 b619 b620 b618 e3 e14 (by rfl)
theorem e16 : o1.scale b87 b20=b616 := @scale_cons V1 _ o1 b87 (List.nil : V1) (List.nil : V1) b617 b618 b616 e2 e15 (by rfl)
theorem e17 : o2.add b616 (List.nil : V2)=b616 := by rfl
theorem e18 : o2.mul b610 b20=b616 := @mul_cons V1 _ o1 b87 (List.nil : V2) b20 (List.nil : V2) b616 (List.nil : V2) b616 e1 e16 (by rfl) e17
theorem e19 : o1.mul b86 (List.nil : V1)=(List.nil : V1) := by decide
theorem e20 : o1.mul b86 b14=b604 := by decide
theorem e21 : o1.mul b86 b15=b629 := by decide
theorem e22 : o1.mul b86 b16=b630 := by decide
theorem e23 : o1.mul b86 b17=b631 := by decide
theorem e24 : o1.mul b86 b18=b632 := by decide
theorem e25 : o1.mul b86 b19=b633 := by decide
theorem e26 : o1.scale b86 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e27 : o1.scale b86 b627=b640 := @scale_cons V1 _ o1 b86 b19 b633 (List.nil : V2) (List.nil : V2) b640 e25 e26 (by rfl)
theorem e28 : o1.scale b86 b625=b639 := @scale_cons V1 _ o1 b86 b18 b632 b627 b640 b639 e24 e27 (by rfl)
theorem e29 : o1.scale b86 b623=b638 := @scale_cons V1 _ o1 b86 b17 b631 b625 b639 b638 e23 e28 (by rfl)
theorem e30 : o1.scale b86 b621=b637 := @scale_cons V1 _ o1 b86 b16 b630 b623 b638 b637 e22 e29 (by rfl)
theorem e31 : o1.scale b86 b619=b636 := @scale_cons V1 _ o1 b86 b15 b629 b621 b637 b636 e21 e30 (by rfl)
theorem e32 : o1.scale b86 b617=b635 := @scale_cons V1 _ o1 b86 b14 b604 b619 b636 b635 e20 e31 (by rfl)
theorem e33 : o1.scale b86 b20=b634 := @scale_cons V1 _ o1 b86 (List.nil : V1) (List.nil : V1) b617 b635 b634 e19 e32 (by rfl)
theorem e34 : o1.add (List.nil : V1) (List.nil : V1)=(List.nil : V1) := by rfl
theorem e35 : o1.add b604 (List.nil : V1)=b604 := by rfl
theorem e36 : o1.add b629 b611=b605 := by decide
theorem e37 : o1.add b630 b612=b606 := by decide
theorem e38 : o1.add b631 b613=b607 := by decide
theorem e39 : o1.add b632 b614=b608 := by decide
theorem e40 : o1.add b633 b615=b530 := by decide
theorem e41 : o2.add (List.nil : V2) b628=b628 := by rfl
theorem e42 : o2.add b640 b626=b647 := @add_cons V1 _ o1 b633 b615 b530 (List.nil : V2) b628 b628 b647 e40 e41 (by rfl)
theorem e43 : o2.add b639 b624=b646 := @add_cons V1 _ o1 b632 b614 b608 b640 b626 b647 b646 e39 e42 (by rfl)
theorem e44 : o2.add b638 b622=b645 := @add_cons V1 _ o1 b631 b613 b607 b639 b624 b646 b645 e38 e43 (by rfl)
theorem e45 : o2.add b637 b620=b644 := @add_cons V1 _ o1 b630 b612 b606 b638 b622 b645 b644 e37 e44 (by rfl)
theorem e46 : o2.add b636 b618=b643 := @add_cons V1 _ o1 b629 b611 b605 b637 b620 b644 b643 e36 e45 (by rfl)
theorem e47 : o2.add b635 b616=b642 := @add_cons V1 _ o1 b604 (List.nil : V1) b604 b636 b618 b643 b642 e35 e46 (by rfl)
theorem e48 : o2.add b634 b641=b609 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b635 b616 b642 b609 e34 e47 (by rfl)
theorem e49 : o2.mul b603 b20=b609 := @mul_cons V1 _ o1 b86 b610 b20 b616 b634 b641 b609 e18 e33 (by rfl) e48
theorem e50 : o1.mul b85 (List.nil : V1)=(List.nil : V1) := by decide
theorem e51 : o1.mul b85 b14=b597 := by decide
theorem e52 : o1.mul b85 b15=b648 := by decide
theorem e53 : o1.mul b85 b16=b649 := by decide
theorem e54 : o1.mul b85 b17=b650 := by decide
theorem e55 : o1.mul b85 b18=b651 := by decide
theorem e56 : o1.mul b85 b19=b652 := by decide
theorem e57 : o1.scale b85 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e58 : o1.scale b85 b627=b659 := @scale_cons V1 _ o1 b85 b19 b652 (List.nil : V2) (List.nil : V2) b659 e56 e57 (by rfl)
theorem e59 : o1.scale b85 b625=b658 := @scale_cons V1 _ o1 b85 b18 b651 b627 b659 b658 e55 e58 (by rfl)
theorem e60 : o1.scale b85 b623=b657 := @scale_cons V1 _ o1 b85 b17 b650 b625 b658 b657 e54 e59 (by rfl)
theorem e61 : o1.scale b85 b621=b656 := @scale_cons V1 _ o1 b85 b16 b649 b623 b657 b656 e53 e60 (by rfl)
theorem e62 : o1.scale b85 b619=b655 := @scale_cons V1 _ o1 b85 b15 b648 b621 b656 b655 e52 e61 (by rfl)
theorem e63 : o1.scale b85 b617=b654 := @scale_cons V1 _ o1 b85 b14 b597 b619 b655 b654 e51 e62 (by rfl)
theorem e64 : o1.scale b85 b20=b653 := @scale_cons V1 _ o1 b85 (List.nil : V1) (List.nil : V1) b617 b654 b653 e50 e63 (by rfl)
theorem e65 : o1.add b597 (List.nil : V1)=b597 := by rfl
theorem e66 : o1.add b648 b604=b598 := by decide
theorem e67 : o1.add b649 b605=b599 := by decide
theorem e68 : o1.add b650 b606=b600 := by decide
theorem e69 : o1.add b651 b607=b601 := by decide
theorem e70 : o1.add b652 b608=b529 := by decide
theorem e71 : o2.add (List.nil : V2) b647=b647 := by rfl
theorem e72 : o2.add b659 b646=b666 := @add_cons V1 _ o1 b652 b608 b529 (List.nil : V2) b647 b647 b666 e70 e71 (by rfl)
theorem e73 : o2.add b658 b645=b665 := @add_cons V1 _ o1 b651 b607 b601 b659 b646 b666 b665 e69 e72 (by rfl)
theorem e74 : o2.add b657 b644=b664 := @add_cons V1 _ o1 b650 b606 b600 b658 b645 b665 b664 e68 e73 (by rfl)
theorem e75 : o2.add b656 b643=b663 := @add_cons V1 _ o1 b649 b605 b599 b657 b644 b664 b663 e67 e74 (by rfl)
theorem e76 : o2.add b655 b642=b662 := @add_cons V1 _ o1 b648 b604 b598 b656 b643 b663 b662 e66 e75 (by rfl)
theorem e77 : o2.add b654 b609=b661 := @add_cons V1 _ o1 b597 (List.nil : V1) b597 b655 b642 b662 b661 e65 e76 (by rfl)
theorem e78 : o2.add b653 b660=b602 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b654 b609 b661 b602 e34 e77 (by rfl)
theorem e79 : o2.mul b596 b20=b602 := @mul_cons V1 _ o1 b85 b603 b20 b609 b653 b660 b602 e49 e64 (by rfl) e78
theorem e80 : o1.mul b84 (List.nil : V1)=(List.nil : V1) := by decide
theorem e81 : o1.mul b84 b14=b590 := by decide
theorem e82 : o1.mul b84 b15=b667 := by decide
theorem e83 : o1.mul b84 b16=b668 := by decide
theorem e84 : o1.mul b84 b17=b669 := by decide
theorem e85 : o1.mul b84 b18=b670 := by decide
theorem e86 : o1.mul b84 b19=b671 := by decide
theorem e87 : o1.scale b84 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e88 : o1.scale b84 b627=b678 := @scale_cons V1 _ o1 b84 b19 b671 (List.nil : V2) (List.nil : V2) b678 e86 e87 (by rfl)
theorem e89 : o1.scale b84 b625=b677 := @scale_cons V1 _ o1 b84 b18 b670 b627 b678 b677 e85 e88 (by rfl)
theorem e90 : o1.scale b84 b623=b676 := @scale_cons V1 _ o1 b84 b17 b669 b625 b677 b676 e84 e89 (by rfl)
theorem e91 : o1.scale b84 b621=b675 := @scale_cons V1 _ o1 b84 b16 b668 b623 b676 b675 e83 e90 (by rfl)
theorem e92 : o1.scale b84 b619=b674 := @scale_cons V1 _ o1 b84 b15 b667 b621 b675 b674 e82 e91 (by rfl)
theorem e93 : o1.scale b84 b617=b673 := @scale_cons V1 _ o1 b84 b14 b590 b619 b674 b673 e81 e92 (by rfl)
theorem e94 : o1.scale b84 b20=b672 := @scale_cons V1 _ o1 b84 (List.nil : V1) (List.nil : V1) b617 b673 b672 e80 e93 (by rfl)
theorem e95 : o1.add b590 (List.nil : V1)=b590 := by rfl
theorem e96 : o1.add b667 b597=b591 := by decide
theorem e97 : o1.add b668 b598=b592 := by decide
theorem e98 : o1.add b669 b599=b593 := by decide
theorem e99 : o1.add b670 b600=b594 := by decide
theorem e100 : o1.add b671 b601=b528 := by decide
theorem e101 : o2.add (List.nil : V2) b666=b666 := by rfl
theorem e102 : o2.add b678 b665=b685 := @add_cons V1 _ o1 b671 b601 b528 (List.nil : V2) b666 b666 b685 e100 e101 (by rfl)
theorem e103 : o2.add b677 b664=b684 := @add_cons V1 _ o1 b670 b600 b594 b678 b665 b685 b684 e99 e102 (by rfl)
theorem e104 : o2.add b676 b663=b683 := @add_cons V1 _ o1 b669 b599 b593 b677 b664 b684 b683 e98 e103 (by rfl)
theorem e105 : o2.add b675 b662=b682 := @add_cons V1 _ o1 b668 b598 b592 b676 b663 b683 b682 e97 e104 (by rfl)
theorem e106 : o2.add b674 b661=b681 := @add_cons V1 _ o1 b667 b597 b591 b675 b662 b682 b681 e96 e105 (by rfl)
theorem e107 : o2.add b673 b602=b680 := @add_cons V1 _ o1 b590 (List.nil : V1) b590 b674 b661 b681 b680 e95 e106 (by rfl)
theorem e108 : o2.add b672 b679=b595 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b673 b602 b680 b595 e34 e107 (by rfl)
theorem e109 : o2.mul b589 b20=b595 := @mul_cons V1 _ o1 b84 b596 b20 b602 b672 b679 b595 e79 e94 (by rfl) e108
theorem e110 : o1.mul b83 (List.nil : V1)=(List.nil : V1) := by decide
theorem e111 : o1.mul b83 b14=b522 := by decide
theorem e112 : o1.mul b83 b15=b686 := by decide
theorem e113 : o1.mul b83 b16=b687 := by decide
theorem e114 : o1.mul b83 b17=b429 := by decide
theorem e115 : o1.mul b83 b18=b416 := by decide
theorem e116 : o1.mul b83 b19=b688 := by decide
theorem e117 : o1.scale b83 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e118 : o1.scale b83 b627=b695 := @scale_cons V1 _ o1 b83 b19 b688 (List.nil : V2) (List.nil : V2) b695 e116 e117 (by rfl)
theorem e119 : o1.scale b83 b625=b694 := @scale_cons V1 _ o1 b83 b18 b416 b627 b695 b694 e115 e118 (by rfl)
theorem e120 : o1.scale b83 b623=b693 := @scale_cons V1 _ o1 b83 b17 b429 b625 b694 b693 e114 e119 (by rfl)
theorem e121 : o1.scale b83 b621=b692 := @scale_cons V1 _ o1 b83 b16 b687 b623 b693 b692 e113 e120 (by rfl)
theorem e122 : o1.scale b83 b619=b691 := @scale_cons V1 _ o1 b83 b15 b686 b621 b692 b691 e112 e121 (by rfl)
theorem e123 : o1.scale b83 b617=b690 := @scale_cons V1 _ o1 b83 b14 b522 b619 b691 b690 e111 e122 (by rfl)
theorem e124 : o1.scale b83 b20=b689 := @scale_cons V1 _ o1 b83 (List.nil : V1) (List.nil : V1) b617 b690 b689 e110 e123 (by rfl)
theorem e125 : o1.add b522 (List.nil : V1)=b522 := by rfl
theorem e126 : o1.add b686 b590=b523 := by decide
theorem e127 : o1.add b687 b591=b524 := by decide
theorem e128 : o1.add b429 b592=b525 := by decide
theorem e129 : o1.add b416 b593=b526 := by decide
theorem e130 : o1.add b688 b594=b527 := by decide
theorem e131 : o2.add (List.nil : V2) b685=b685 := by rfl
theorem e132 : o2.add b695 b684=b702 := @add_cons V1 _ o1 b688 b594 b527 (List.nil : V2) b685 b685 b702 e130 e131 (by rfl)
theorem e133 : o2.add b694 b683=b701 := @add_cons V1 _ o1 b416 b593 b526 b695 b684 b702 b701 e129 e132 (by rfl)
theorem e134 : o2.add b693 b682=b700 := @add_cons V1 _ o1 b429 b592 b525 b694 b683 b701 b700 e128 e133 (by rfl)
theorem e135 : o2.add b692 b681=b699 := @add_cons V1 _ o1 b687 b591 b524 b693 b682 b700 b699 e127 e134 (by rfl)
theorem e136 : o2.add b691 b680=b698 := @add_cons V1 _ o1 b686 b590 b523 b692 b681 b699 b698 e126 e135 (by rfl)
theorem e137 : o2.add b690 b595=b697 := @add_cons V1 _ o1 b522 (List.nil : V1) b522 b691 b680 b698 b697 e125 e136 (by rfl)
theorem e138 : o2.add b689 b696=b532 := @add_cons V1 _ o1 (List.nil : V1) (List.nil : V1) (List.nil : V1) b690 b595 b697 b532 e34 e137 (by rfl)
theorem e139 : o2.mul b88 b20=b532 := @mul_cons V1 _ o1 b83 b589 b20 b595 b689 b696 b532 e109 e124 (by rfl) e138
theorem e140 : o2.mul (List.nil : V2) b27=(List.nil : V2) := by rfl
theorem e141 : o1.mul b87 b21=b717 := by decide
theorem e142 : o1.mul b87 b22=b723 := by decide
theorem e143 : o1.mul b87 b23=b724 := by decide
theorem e144 : o1.mul b87 b24=b725 := by decide
theorem e145 : o1.mul b87 b25=b726 := by decide
theorem e146 : o1.mul b87 b26=b542 := by decide
theorem e147 : o1.scale b87 b740=b741 := @scale_cons V1 _ o1 b87 b26 b542 (List.nil : V2) (List.nil : V2) b741 e146 e9 (by rfl)
theorem e148 : o1.scale b87 b738=b739 := @scale_cons V1 _ o1 b87 b25 b726 b740 b741 b739 e145 e147 (by rfl)
theorem e149 : o1.scale b87 b736=b737 := @scale_cons V1 _ o1 b87 b24 b725 b738 b739 b737 e144 e148 (by rfl)

end RKResearch.Certified.Graded.NativePencilCubicDAG
