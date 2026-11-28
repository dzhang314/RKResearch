import RKCert.ReviewedNative.DIRKOrderTwelveFifteenNonzeroFourthObstructionCore
open RKResearch.Certified.Graded.OrderTwelveFifteen.NonzeroFourthObstructionCore

example (d s : Int) (hs : s≠0) (h : (-d*d)*s=0) : d=0 :=
  fifthDiagonalZero d s hs h

example (Q U Z A B F : Int) (hq : Q≠0)
    (shapeA : A=9*Z-8*Q)
    (cross : 9*B-(2*Q-9*U)*A=2*Q*(8*Q-9*U))
    (atEqual : Z=U → F=U*(8*Q-9*U))
    (paidA : A*F=0) (paidB : B*F=0) : F=0 :=
  commonFactorForcesCollision Q U Z A B F hq shapeA cross atEqual paidA paidB
