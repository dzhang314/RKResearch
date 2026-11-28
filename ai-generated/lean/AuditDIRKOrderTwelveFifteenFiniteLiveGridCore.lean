import RKCert.ReviewedNative.DIRKOrderTwelveFifteenFiniteLiveGridCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.FiniteLiveGridCore

example (b u : Int) (hb : b ≠ 0) (h0 : b*u=0) (h1 : b+6*(u*u)=0) : False :=
  constantBDegenerate b u hb h0 h1

example (δ : Int) (h : -216*(δ*(δ*δ))=0) : δ=0 := poleResidue δ h

example (γ η α : Int) (hg : γ≠0)
    (h0 : (-6*γ)*(η*η)=0) (h1 : η-γ-12*(γ*α*η)=0) : False :=
  variableBDegenerate γ η α hg h0 h1
