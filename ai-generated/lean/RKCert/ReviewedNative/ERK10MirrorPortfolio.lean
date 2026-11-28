module

public import RKCert.ReviewedNative.ERK10RationalSixteen
public import RKCert.ReviewedNative.ERK10MirrorCompact
public import RKCert.ReviewedNative.ERK10MirrorThetaFour
public import RKCert.ReviewedNative.ERK10MirrorUnit13
public import RKCert.ReviewedNative.RobustExplicitPair

@[expose] public section

/-! Four concrete rational tableaux cover all admissible local and positive
characteristic rings. This proves no single generic factorial-localized tableau. -/
namespace RKResearch.Certified.ERK10MirrorPortfolio

open ExactExplicitPortfolio

def chartTerms : List (Int × Nat) :=
  [(5080347676082004626545044674530029107565222578596734569433568567993290074809058467981589057842209801181889179960064528852420513656773527990423375618310117615808786395097230004118833833523715359630754679925969076897313792168915856640347229577640625, 1353980995532875019859622074612347006881991195414951057609378650925859190318740101845428799345122682869247400371158194076656253000000000000),
   (-5208996867146632218488477123058817535573605342546165162285150218602586208301197661661694098901659097900765877396398236277197156588590568526725365863772719970386768811270922766275405419699844123273341827093244255982327379015472616721517353343309431337717222867167036876126792585881530074725852812305531963568397077253103010288786690851016385970007995244015000, 1320541052251127574067200000),
   (-298235168230673396529612632405277216297353720773258600975313471384616266097535778601915606114692994728267316737679162640904786451497776396881343069024159158658886011730087876899431295275380095031156129784076039415, 421382472598873671046748625598560000),
   (-111, 290196232821196345694137322475813069675494506496186181471763081111116191371804466912881497224916941237344508539033597752877877724116003196666184092361501297515967338155408717416399696203892413753685568325896474449920000)]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem literal_bezout :
    (chartTerms.map (fun term => term.1 * (term.2 : Int))).sum = (816480000 : Int) := by
  decide +kernel

private theorem int_unit_of_nat {R : Type*} [CommRing R] (d : Nat)
    (h : IsUnit (d : R)) : IsUnit ((d : Int) : R) := by
  simpa only [Int.cast_natCast] using h

set_option maxRecDepth 50000 in
theorem local_exact (R : Type*) [CommRing R] [IsLocalRing R]
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) : Exact 16 10 R := by
  have hdiv : (816480000 : Nat) ∣ (Nat.factorial 10)^2 := by decide +kernel
  have hp : IsUnit (((Nat.factorial 10)^2 : Nat) : R) := by
    simpa only [Nat.cast_pow] using hf.pow 2
  have hg : IsUnit (((816480000 : Nat)) : R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := R) hdiv) hp
  refine local_exact_of_denominators chartTerms literal_bezout hg ?_
  intro term hit unit
  simp only [chartTerms, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
  · exact ERK10RationalSixteen.exists_exact_of_unit (int_unit_of_nat _ unit)
  · exact ERK10MirrorCompact.exists_exact_of_unit (int_unit_of_nat _ unit)
  · exact ERK10MirrorThetaFour.exists_exact_of_unit (int_unit_of_nat _ unit)
  · exact ERK10MirrorUnit13.exists_exact_of_unit (int_unit_of_nat _ unit)

private theorem pair0 {R : Type*} [CommRing R]
    (hD : IsUnit (ERK10RationalSixteen.D : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (ERK10RationalSixteen.D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact PairCert.of_integer_receipts
    (ERK10RationalSixteen.explicit d) (ERK10RationalSixteen.order_ten d hd)
    ERK10RationalSixteen.d₁ ERK10RationalSixteen.d₂ ERK10RationalSixteen.n₁ ERK10RationalSixteen.n₂ ERK10RationalSixteen.e₁ ERK10RationalSixteen.e₂
    (ERK10RationalSixteen.from_integer_defect ERK10RationalSixteen.tree₁ (by decide) _ _ ERK10RationalSixteen.integer_next₁ d hd)
    (ERK10RationalSixteen.from_integer_defect ERK10RationalSixteen.tree₂ (by decide) _ _ ERK10RationalSixteen.integer_next₂ d hd) ERK10RationalSixteen.bezout

private theorem pair1 {R : Type*} [CommRing R]
    (hD : IsUnit (ERK10MirrorCompact.D : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (ERK10MirrorCompact.D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact PairCert.of_integer_receipts
    (ERK10MirrorCompact.explicit d) (ERK10MirrorCompact.order_ten d hd)
    ERK10MirrorCompact.d₁ ERK10MirrorCompact.d₂ ERK10MirrorCompact.n₁ ERK10MirrorCompact.n₂ ERK10MirrorCompact.e₁ ERK10MirrorCompact.e₂
    (ERK10MirrorCompact.from_integer_defect ERK10MirrorCompact.tree₁ (by decide) _ _ ERK10MirrorCompact.integer_next₁ d hd)
    (ERK10MirrorCompact.from_integer_defect ERK10MirrorCompact.tree₂ (by decide) _ _ ERK10MirrorCompact.integer_next₂ d hd) ERK10MirrorCompact.bezout

private theorem pair2 {R : Type*} [CommRing R]
    (hD : IsUnit (ERK10MirrorThetaFour.D : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (ERK10MirrorThetaFour.D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact PairCert.of_integer_receipts
    (ERK10MirrorThetaFour.explicit d) (ERK10MirrorThetaFour.order_ten d hd)
    ERK10MirrorThetaFour.d₁ ERK10MirrorThetaFour.d₂ ERK10MirrorThetaFour.n₁ ERK10MirrorThetaFour.n₂ ERK10MirrorThetaFour.e₁ ERK10MirrorThetaFour.e₂
    (ERK10MirrorThetaFour.from_integer_defect ERK10MirrorThetaFour.tree₁ (by decide) _ _ ERK10MirrorThetaFour.integer_next₁ d hd)
    (ERK10MirrorThetaFour.from_integer_defect ERK10MirrorThetaFour.tree₂ (by decide) _ _ ERK10MirrorThetaFour.integer_next₂ d hd) ERK10MirrorThetaFour.bezout

private theorem pair3 {R : Type*} [CommRing R]
    (hD : IsUnit (ERK10MirrorUnit13.D : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  obtain ⟨u,hu⟩ := hD
  let d : R := ↑(u⁻¹)
  have hd : (ERK10MirrorUnit13.D:R)*d=1 := by rw [←hu]; exact u.mul_inv
  exact PairCert.of_integer_receipts
    (ERK10MirrorUnit13.explicit d) (ERK10MirrorUnit13.order_ten d hd)
    ERK10MirrorUnit13.d₁ ERK10MirrorUnit13.d₂ ERK10MirrorUnit13.n₁ ERK10MirrorUnit13.n₂ ERK10MirrorUnit13.e₁ ERK10MirrorUnit13.e₂
    (ERK10MirrorUnit13.from_integer_defect ERK10MirrorUnit13.tree₁ (by decide) _ _ ERK10MirrorUnit13.integer_next₁ d hd)
    (ERK10MirrorUnit13.from_integer_defect ERK10MirrorUnit13.tree₂ (by decide) _ _ ERK10MirrorUnit13.integer_next₂ d hd) ERK10MirrorUnit13.bezout


theorem clean_ring_pair (R : Type*) [CommRing R] (hc : Clean (T := R))
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) :
    PairCert 16 10 ERK10RationalSixteen.tree₁ ERK10RationalSixteen.tree₂ R := by
  have hdiv : (816480000 : Nat) ∣ (Nat.factorial 10)^2 := by decide +kernel
  have hp : IsUnit (((Nat.factorial 10)^2 : Nat) : R) := by
    simpa only [Nat.cast_pow] using hf.pow 2
  have hg : IsUnit (((816480000 : Nat)) : R) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := R) hdiv) hp
  refine PairCert.clean_of_bezout hc chartTerms literal_bezout hg ?_
  intro S _ term hit unit
  simp only [chartTerms, List.mem_cons, List.not_mem_nil, or_false] at hit
  rcases hit with rfl | rfl | rfl | rfl
  · exact pair0 (int_unit_of_nat _ unit)
  · exact pair1 (int_unit_of_nat _ unit)
  · exact pair2 (int_unit_of_nat _ unit)
  · exact pair3 (int_unit_of_nat _ unit)

theorem clean_ring_exact (R : Type*) [CommRing R] [Nontrivial R]
    (hc : Clean (T := R)) (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) :
    Exact 16 10 R :=
  (clean_ring_pair R hc hf).exact (by decide) (by decide)

theorem clean_coefficients_exact {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (hc : Clean (T := R)) (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) (f : R →+* S) :
    Exact 16 10 S :=
  ((clean_ring_pair R hc hf).map f).exact (by decide) (by decide)

theorem positive_characteristic_exact (R : Type*) [CommRing R] [Nontrivial R]
    (n : Nat) [CharP R n] (hn : 0 < n)
    (hf : IsUnit ((Nat.factorial 10 : Nat) : R)) : Exact 16 10 R :=
  positive_characteristic_of_local_unit (Nat.factorial 10) n hn hf
    (fun T _ _ hfT => local_exact T hfT)

end RKResearch.Certified.ERK10MirrorPortfolio

#print axioms RKResearch.Certified.ERK10MirrorPortfolio.local_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.positive_characteristic_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.clean_ring_exact
#print axioms RKResearch.Certified.ERK10MirrorPortfolio.clean_coefficients_exact
