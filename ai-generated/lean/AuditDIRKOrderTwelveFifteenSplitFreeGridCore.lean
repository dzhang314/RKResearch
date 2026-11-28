import RKCert.ReviewedNative.DIRKOrderTwelveFifteenSplitFreeGridCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.SplitFreeGridCore

example (Q N r : Int) (hn : N≠0) (hr : r≠0)
    (h : (Q-N)*(r*r)+(-Q+2*N)*r+(Q-N)=0) : Q-N≠0 :=
  orientationLeadingNonzero Q N r hn hr h

example (N r : Int) (hn : N≠0) (hr : r≠0) :
    (N-N)*(r*r)+(-N+2*N)*r+(N-N) ≠ 0 :=
  orientationLeadAtEqual N r hn hr
