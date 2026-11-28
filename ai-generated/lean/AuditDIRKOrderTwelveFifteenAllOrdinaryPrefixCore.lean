import RKCert.ReviewedNative.DIRKOrderTwelveFifteenAllOrdinaryPrefixCore

open RKResearch.Certified.Graded.OrderTwelveFifteen.AllOrdinaryPrefixCore

example (J U V R ρ I Fx : Int) (hU : U = R-ρ*V) :
    J-U*I-V*Fx = J-R*I-V*(Fx-ρ*I) :=
  cardinalRowEliminate J U V R ρ I Fx hU

example (r1 rx k1 kx ρ M K I Fx : Int)
    (hρ : kx = ρ*k1) (h1 : r1*M+k1*K = I) (hx : rx*M+kx*K = Fx) :
    (rx-ρ*r1)*M = Fx-ρ*I :=
  trueMomentEliminate r1 rx k1 kx ρ M K I Fx hρ h1 hx
