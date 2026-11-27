module

public import RKCert.ReviewedNative.SDIRKSixPaidPhysical
import Mathlib.Tactic.LinearCombination

public section
namespace RKResearch.Certified.Graded.SDIRKSix
open RKCert.ReviewedNative.SDIRKSixReceipts
variable {K : Type*} [Field K]
private theorem cancel30 (h30 : IsUnit (30 : K))
    {n : ℕ} (hn : n ∣ 30 ^ 13) {x : K} (hx : (n : K) * x = 0) : x = 0 :=
  (isUnit_of_dvd_paid_power h30 hn).mul_left_cancel (by simpa only [mul_zero] using hx)

private theorem cne (p n : ℕ) [CharP K p] (h : ¬p ∣ n) : (n : K) ≠ 0 :=
  fun hx => h ((CharP.cast_eq_zero_iff K p n).mp hx)

private theorem twelve {A : Matrix (Fin 6) (Fin 6) K} {γ z u v : K}
    (h : SixStageChart A γ z u v) (d₁ : (3846112 : K) ≠ 0) (d₂ : (198898968576 : K) ≠ 0) :
    factorTwelve z u v = 0 ∧ hTwelve z u v = 0 ∧ vTwelve z u v = 0 := by
  have h₃ : factorThree z u v ≠ 0 := by
    intro h₃
    have hH := cancel30 h.paid (n := 576) (by decide)
      (deriveHThree_mul z u v h.bridge1_zero h.front_zero h₃)
    have hV := cancel30 h.paid (n := 960) (by decide)
      (deriveVThree_mul z u v h.bridge2_zero hH h₃)
    rcases h.last_zero with hk|ht
    · exact d₁ (by simpa only [mul_one] using noThreeKappa_mul z u v hk hV hH h₃)
    · exact d₂ (by simpa only [mul_one] using noThreeTerminal_mul z u v ht hV hH h₃)
  have hg := mul_ne_zero (pow_ne_zero 2 h.z_ne) h₃
  have hp := cancel30 h.paid (n := 360) (by decide)
    (project_mul z u v h.bridge1_zero h.front_zero)
  have hQ := (mul_eq_zero.mp hp).resolve_left hg
  have hH := (mul_eq_zero.mp (hTwelve_guard_mul_eq_zero h.paid h.front_zero h.bridge1_zero)).resolve_left hg
  exact ⟨hQ,hH,cancel30 h.paid (n := 5529600) (by decide)
    (deriveVTwelve_mul z u v h.bridge2_zero hH hQ)⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
private theorem reconstruct_241 [CharP K 241] {z u v : K}
    (hQ : factorTwelve z u v = 0) (hH : hTwelve z u v = 0)
    (hV : vTwelve z u v = 0)
    (hE : terminal z u v = 0) : z = 2 ∧ u = 82 ∧ v = 82 := by
  have hchar : (241 : K) = 0 := CharP.cast_eq_zero K 241
  simp only [factorTwelve] at hQ
  simp only [hTwelve] at hH
  simp only [vTwelve] at hV
  simp only [terminal] at hE
  have hU : (u) = (-85*z^11 - 68*z^10 - 14*z^9 - 64*z^8 - 74*z^7 - 34*z^6 - 52*z^5 + 39*z^4 + 111*z^3 + 26*z^2 + 59*z + 87) := by
    linear_combination (norm := ring) (221) * hH + (-633839*u + 12104*z^11 - 767176*z^10 + 20859594*z^9 - 320075888*z^8 + 3054114874*z^7 - 18860792766*z^6 + 76459525012*z^5 - 203405744919*z^4 + 349982661729*z^3 - 371445977786*z^2 + 209642990101*z - 36249675207) * hchar
  have hvu : (v) = (u) := by
    linear_combination (norm := ring) (221) * hV + (-221) * hH + (633839*u - 633839*v) * hchar
  have hStep6 : (-40*z^3 + 480*z^2 - 1600*z + 1600) = (-40*z^3 - 2*z^2 + 87*z - 87) := by
    linear_combination (norm := ring) (2*z^2 - 7*z + 7) * hchar
  have hStep5 : (-40*u*z^3 + 480*u*z^2 - 1600*u*z + 1600*u + 2*z^6 - 48*z^5 + 508*z^4 - 2840*z^3 + 8400*z^2 - 12800*z + 8000) = (56*z^11 - 11*z^10 - 114*z^9 + 17*z^8 + 13*z^7 + 96*z^6 + 27*z^5 - 105*z^4 + 54*z^3 + 45*z^2 + 78*z - 51) := by
    linear_combination (norm := ring) (u) * hStep6 + (-40*z^3 - 2*z^2 + 87*z - 87) * hU + (26*z^2 + 79*z) * hQ + (14*z^14 + 19*z^13 - 223*z^12 + 3067*z^11 - 29083*z^10 + 171032*z^9 - 564899*z^8 + 530251*z^7 + 3578942*z^6 - 17196620*z^5 + 36660865*z^4 - 43164207*z^3 + 25697772*z^2 - 4531562*z + 2) * hchar
  have hStep4 : (-40*u^2*z^3 + 480*u^2*z^2 - 1600*u^2*z + 1600*u^2 + 2*u*z^6 - 48*u*z^5 + 508*u*z^4 - 2840*u*z^3 + 8400*u*z^2 - 12800*u*z + 8000*u - z^7 + 18*z^6 - 144*z^5 + 704*z^4 - 2560*z^3 + 7200*z^2 - 12000*z + 8000) = (-112*z^11 - 83*z^10 - 39*z^9 + 99*z^8 + 25*z^7 - 20*z^6 - 21*z^5 + 6*z^4 + 44*z^3 - 96*z^2 + 95*z - 26) := by
    linear_combination (norm := ring) (u) * hStep5 + (56*z^11 - 11*z^10 - 114*z^9 + 17*z^8 + 13*z^7 + 96*z^6 + 27*z^5 - 105*z^4 + 54*z^3 + 45*z^2 + 78*z - 51) * hU + (60*z^10 + 2*z^9 - 69*z^8 + 13*z^7 - 75*z^6 - 101*z^5 - 26*z^4 + 60*z^3 - 92*z^2 + 39*z + 26) * hQ + (-20*z^22 + 5*z^21 - 461*z^20 + 8540*z^19 - 92362*z^18 + 664837*z^17 - 3231277*z^16 + 10521755*z^15 - 22012809*z^14 + 25402349*z^13 - 2136219*z^12 - 42456606*z^11 + 67777599*z^10 - 48315773*z^9 + 17598059*z^8 - 23594336*z^7 + 74193800*z^6 - 117674436*z^5 + 97906268*z^4 - 43121124*z^3 + 1548807*z^2 + 6711202*z - 1491371) * hchar
  have hStep3 : (-40*u^3*z^3 + 480*u^3*z^2 - 1600*u^3*z + 1600*u^3 + 2*u^2*z^6 - 48*u^2*z^5 + 508*u^2*z^4 - 2840*u^2*z^3 + 8400*u^2*z^2 - 12800*u^2*z + 8000*u^2 - u*z^7 + 18*u*z^6 - 144*u*z^5 + 704*u*z^4 - 2560*u*z^3 + 7200*u*z^2 - 12000*u*z + 8000*u + 4*z^7 - 74*z^6 + 576*z^5 - 2428*z^4 + 5720*z^3 - 6480*z^2 + 1600*z + 1600) = (-74*z^11 - 73*z^10 + 113*z^9 + 36*z^8 - 69*z^7 - 42*z^6 - 93*z^5 + 50*z^4 + 56*z^3 + 50*z^2 + 53*z + 100) := by
    linear_combination (norm := ring) (u) * hStep4 + (-112*z^11 - 83*z^10 - 39*z^9 + 99*z^8 + 25*z^7 - 20*z^6 - 21*z^5 + 6*z^4 + 44*z^3 - 96*z^2 + 95*z - 26) * hU + (-120*z^10 + 4*z^9 - 90*z^8 + 40*z^7 + 69*z^6 - 88*z^5 - 102*z^4 - 117*z^3 - 79*z^2 - 91*z + 39) * hQ + (40*z^22 + 27*z^21 + 1049*z^20 - 17177*z^19 + 187780*z^18 - 1375200*z^17 + 6917165*z^16 - 24179785*z^15 + 59164164*z^14 - 102011785*z^13 + 124559150*z^12 - 105805521*z^11 + 52108390*z^10 + 14652486*z^9 - 60434475*z^8 + 52196030*z^7 - 31291451*z^6 + 40957701*z^5 - 61522325*z^4 + 66115732*z^3 - 52514033*z^2 + 18642358*z - 2237082) * hchar
  have hStep2 : (-40*u^4*z^3 + 480*u^4*z^2 - 1600*u^4*z + 1600*u^4 + 2*u^3*z^6 - 48*u^3*z^5 + 508*u^3*z^4 - 2840*u^3*z^3 + 8400*u^3*z^2 - 12800*u^3*z + 8000*u^3 - u^2*z^7 + 18*u^2*z^6 - 144*u^2*z^5 + 704*u^2*z^4 - 2560*u^2*z^3 + 7200*u^2*z^2 - 12000*u^2*z + 8000*u^2 + 4*u*z^7 - 74*u*z^6 + 576*u*z^5 - 2428*u*z^4 + 5720*u*z^3 - 6480*u*z^2 + 1600*u*z + 1600*u - 4*z^7 + 60*z^6 - 312*z^5 + 616*z^4 - 120*z^3 - 960*z^2 + 800*z) = (29*z^11 - 97*z^10 + 90*z^9 - 103*z^8 + 86*z^7 - 87*z^6 - 32*z^5 + 19*z^4 + 98*z^3 + 109*z^2 - 80*z - 16) := by
    linear_combination (norm := ring) (u) * hStep3 + (-74*z^11 - 73*z^10 + 113*z^9 + 36*z^8 - 69*z^7 - 42*z^6 - 93*z^5 + 50*z^4 + 56*z^3 + 50*z^2 + 53*z + 100) * hU + (24*z^10 + 96*z^9 + 88*z^8 - 45*z^7 + 36*z^6 + 34*z^5 - 53*z^4 - 4*z^3 - 9*z^2 - 63*z - 40) * hQ + (26*z^22 + 53*z^21 - 189*z^20 + 2627*z^19 - 24281*z^18 + 135018*z^17 - 404100*z^16 + 264858*z^15 + 2212720*z^14 - 6417729*z^13 + 541592*z^12 + 29125975*z^11 - 63529458*z^10 + 54069106*z^9 + 1387165*z^8 - 40427937*z^7 + 36076876*z^6 - 3474828*z^5 - 17638426*z^4 + 11443602*z^3 + 5219888*z^2 - 10152849*z + 2294476) * hchar
  have hStep1 : (-40*u^5*z^3 + 480*u^5*z^2 - 1600*u^5*z + 1600*u^5 + 2*u^4*z^6 - 48*u^4*z^5 + 508*u^4*z^4 - 2840*u^4*z^3 + 8400*u^4*z^2 - 12800*u^4*z + 8000*u^4 - u^3*z^7 + 18*u^3*z^6 - 144*u^3*z^5 + 704*u^3*z^4 - 2560*u^3*z^3 + 7200*u^3*z^2 - 12000*u^3*z + 8000*u^3 + 4*u^2*z^7 - 74*u^2*z^6 + 576*u^2*z^5 - 2428*u^2*z^4 + 5720*u^2*z^3 - 6480*u^2*z^2 + 1600*u^2*z + 1600*u^2 - 4*u*z^7 + 60*u*z^6 - 312*u*z^5 + 616*u*z^4 - 120*u*z^3 - 960*u*z^2 + 800*u*z) = (53*z^11 - 12*z^10 + 9*z^9 + 38*z^8 - 76*z^7 + 37*z^6 - 92*z^5 - 96*z^4 - 38*z^3 + 93*z^2 - 50*z + 90) := by
    linear_combination (norm := ring) (u) * hStep2 + (29*z^11 - 97*z^10 + 90*z^9 - 103*z^8 + 86*z^7 - 87*z^6 - 32*z^5 + 19*z^4 + 98*z^3 + 109*z^2 - 80*z - 16) * hU + (-55*z^10 - 118*z^9 - 65*z^8 - 2*z^7 + 86*z^6 - 72*z^5 - 91*z^4 + 56*z^3 - 110*z^2 + 117*z + 36) * hQ + (-10*z^22 + 11*z^21 + 421*z^20 - 6873*z^19 + 69154*z^18 - 447347*z^17 + 1849933*z^16 - 4593440*z^15 + 5274702*z^14 + 3460447*z^13 - 21241104*z^12 + 34824632*z^11 - 41752500*z^10 + 54196033*z^9 - 44411336*z^8 - 36653760*z^7 + 137361633*z^6 - 183888732*z^5 + 160843821*z^4 - 93727821*z^3 + 22829694*z^2 + 5678706*z - 2065002) * hchar
  have hStep0 : (-40*u^6*z^3 + 480*u^6*z^2 - 1600*u^6*z + 1600*u^6 + 2*u^5*z^6 - 48*u^5*z^5 + 508*u^5*z^4 - 2840*u^5*z^3 + 8400*u^5*z^2 - 12800*u^5*z + 8000*u^5 - u^4*z^7 + 18*u^4*z^6 - 144*u^4*z^5 + 704*u^4*z^4 - 2560*u^4*z^3 + 7200*u^4*z^2 - 12000*u^4*z + 8000*u^4 + 4*u^3*z^7 - 74*u^3*z^6 + 576*u^3*z^5 - 2428*u^3*z^4 + 5720*u^3*z^3 - 6480*u^3*z^2 + 1600*u^3*z + 1600*u^3 - 4*u^2*z^7 + 60*u^2*z^6 - 312*u^2*z^5 + 616*u^2*z^4 - 120*u^2*z^3 - 960*u^2*z^2 + 800*u^2*z) = (10*z^11 - 45*z^10 - 103*z^9 - 27*z^8 - 115*z^7 - 35*z^6 - 56*z^5 - 9*z^4 - 2*z^3 - 60*z^2 - 119*z + 44) := by
    linear_combination (norm := ring) (u) * hStep1 + (53*z^11 - 12*z^10 + 9*z^9 + 38*z^8 - 76*z^7 + 37*z^6 - 92*z^5 - 96*z^4 - 38*z^3 + 93*z^2 - 50*z + 90) * hU + (74*z^10 + 38*z^9 - 40*z^8 + 42*z^7 + 64*z^5 - 80*z^4 + 25*z^3 + 78*z^2 - 77*z - 74) * hQ + (-19*z^22 + 10*z^21 - 611*z^20 + 10204*z^19 - 109188*z^18 + 771025*z^17 - 3650806*z^16 + 11465766*z^15 - 22723221*z^14 + 23520839*z^13 + 3605150*z^12 - 49921711*z^11 + 80670439*z^10 - 87599787*z^9 + 95332929*z^8 - 91809440*z^7 + 46825239*z^6 + 25344373*z^5 - 58011727*z^4 + 25798153*z^3 + 17839301*z^2 - 21051481*z + 4244746) * hchar
  rw [hvu] at hE
  have hR : (10*z^11 - 45*z^10 - 103*z^9 - 27*z^8 - 115*z^7 - 35*z^6 - 56*z^5 - 9*z^4 - 2*z^3 - 60*z^2 - 119*z + 44) = 0 := by
    linear_combination hE - hStep0
  have hz : (z) = (2) := by
    linear_combination (norm := ring) (55*z^10 - 86*z^9 - 95*z^8 + 114*z^7 - 79*z^6 + 103*z^5 - 103*z^4 + 78*z^3 + 62*z^2 + 64*z + 64) * hR + (-68*z^9 - 84*z^8 - 116*z^7 - 83*z^6 + 73*z^5 - 34*z^4 + 109*z^3 - 64*z^2 + 57*z - 74) * hQ + (-2*z^21 - 5*z^20 + 557*z^19 - 9089*z^18 + 94597*z^17 - 653687*z^16 + 3030562*z^15 - 9431375*z^14 + 19471190*z^13 - 25780286*z^12 + 18408745*z^11 + 6835666*z^10 - 50699180*z^9 + 109530071*z^8 - 157626429*z^7 + 169858571*z^6 - 170685025*z^5 + 153205918*z^4 - 116285046*z^3 + 72102808*z^2 - 28737839*z + 4244702) * hchar
  rw [hz] at hU
  have hu : (u) = (82) := by
    linear_combination (norm := ring) (1) * hU + (-1157) * hchar
  exact ⟨hz, hu, hvu.trans hu⟩

theorem chartValues_241 [CharP K 241] {A : Matrix (Fin 6) (Fin 6) K} {γ z u v : K}
    (h : SixStageChart A γ z u v) : z = 2 ∧ u = 82 ∧ v = 82 := by
  obtain ⟨hQ,hH,hV⟩ := twelve h (cne 241 _ (by decide)) (cne 241 _ (by decide))
  apply reconstruct_241 hQ hH hV
  apply h.last_zero.resolve_left
  intro hn
  exact cne 241 122267206287360000 (by decide)
    (by simpa only [mul_one, Nat.cast_ofNat] using noTwelveKappa_mul z u v hn hV hH hQ)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
private theorem reconstruct_255919 [CharP K 255919] {z u v : K}
    (hQ : factorTwelve z u v = 0) (hH : hTwelve z u v = 0)
    (hV : vTwelve z u v = 0)
    (hE : kappa z u v = 0) : z = 47708 ∧ u = 250912 ∧ v = 250912 := by
  have hchar : (255919 : K) = 0 := CharP.cast_eq_zero K 255919
  simp only [factorTwelve] at hQ
  simp only [hTwelve] at hH
  simp only [vTwelve] at hV
  simp only [kappa] at hE
  have hU : (u) = (-66172*z^11 - 97557*z^10 + 29705*z^9 + 102769*z^8 + 77003*z^7 - 76201*z^6 - 113430*z^5 + 86427*z^4 + 70538*z^3 - 10208*z^2 + 32179*z + 113422) := by
    linear_combination (norm := ring) (191910) * hH + (-518321*u + 9898*z^11 - 627357*z^10 + 17057905*z^9 - 261741631*z^8 + 2497498363*z^7 - 15423388121*z^6 + 62524674570*z^5 - 166334776533*z^4 + 286197854698*z^3 - 303749452768*z^2 + 171435275459*z - 29643123538) * hchar
  have hvu : (v) = (u) := by
    linear_combination (norm := ring) (191910) * hV + (-191910) * hH + (518321*u - 518321*v) * hchar
  have hStep2 : (-1 : K) = (-1) := by ring
  have hStep1 : (2 - u) = (66172*z^11 + 97557*z^10 - 29705*z^9 - 102769*z^8 - 77003*z^7 + 76201*z^6 + 113430*z^5 - 86427*z^4 - 70538*z^3 + 10208*z^2 - 32179*z - 113420) := by
    linear_combination (norm := ring) (u) * hStep2 + (-1) * hU
  have hStep0 : (-u^2 + 2*u + 1) = (118854*z^11 + 35795*z^10 + 56190*z^9 - 78477*z^8 - 47165*z^7 - 67436*z^6 + 114867*z^5 + 26705*z^4 + 76985*z^3 + 95245*z^2 - 114117*z - 124576) := by
    linear_combination (norm := ring) (u) * hStep1 + (66172*z^11 + 97557*z^10 - 29705*z^9 - 102769*z^8 - 77003*z^7 + 76201*z^6 + 113430*z^5 - 86427*z^4 - 70538*z^3 + 10208*z^2 - 32179*z - 113420) * hU + (40506*z^10 - 30759*z^9 + 44008*z^8 + 35765*z^7 - 8921*z^6 - 115331*z^5 - 55044*z^4 - 103048*z^3 - 60157*z^2 - 4887*z - 87511) * hQ + (-17110*z^22 - 50439*z^21 - 22155*z^20 + 81491*z^19 + 50994*z^18 + 477069*z^17 - 2701047*z^16 + 9228624*z^15 - 24157056*z^14 + 45030205*z^13 - 57501164*z^12 + 49535166*z^11 - 31612015*z^10 + 30955958*z^9 - 51659120*z^8 + 62806615*z^7 - 39947606*z^6 + 215465*z^5 + 40128347*z^4 - 67089043*z^3 + 56032150*z^2 - 28127079*z + 4676823) * hchar
  have hR : (118854*z^11 + 35795*z^10 + 56190*z^9 - 78477*z^8 - 47165*z^7 - 67436*z^6 + 114867*z^5 + 26705*z^4 + 76985*z^3 + 95245*z^2 - 114117*z - 124576) = 0 := by
    linear_combination hE - hStep0
  have hz : (z) = (47708) := by
    linear_combination (norm := ring) (-101890*z^10 - 34261*z^9 - 111156*z^8 - 107885*z^7 - 17395*z^6 + 82555*z^5 - 73266*z^4 + 44168*z^3 - 53275*z^2 - 107023*z - 36122) * hR + (-53020*z^9 - 97847*z^8 - 13039*z^7 - 57060*z^6 + 90013*z^5 + 95425*z^4 - 35779*z^3 - 961*z^2 + 44441*z - 53338) * hQ + (47320*z^21 + 30149*z^20 + 79178*z^19 + 35570*z^18 + 82791*z^17 - 501747*z^16 + 1777991*z^15 - 4458178*z^14 + 4562728*z^13 + 8331908*z^12 - 38250814*z^11 + 69708365*z^10 - 75878741*z^9 + 48535516*z^8 - 777127*z^7 - 38688649*z^6 + 19637298*z^5 + 34586920*z^4 - 60150758*z^3 + 47528521*z^2 - 19755759*z + 2863580) * hchar
  rw [hz] at hU
  have hu : (u) = (250912) := by
    linear_combination (norm := ring) (1) * hU + (-753509041500180685796555955803363478481278856523042) * hchar
  exact ⟨hz, hu, hvu.trans hu⟩

theorem chartValues_255919 [CharP K 255919] {A : Matrix (Fin 6) (Fin 6) K} {γ z u v : K}
    (h : SixStageChart A γ z u v) : z = 47708 ∧ u = 250912 ∧ v = 250912 := by
  obtain ⟨hQ,hH,hV⟩ := twelve h (cne 255919 _ (by decide)) (cne 255919 _ (by decide))
  apply reconstruct_255919 hQ hH hV
  apply h.last_zero.resolve_right
  intro hn
  exact cne 255919 6214370355160790146744320000 (by decide)
    (by simpa only [mul_one, Nat.cast_ofNat] using noTwelveTerminal_mul z u v hn hV hH hQ)

end RKResearch.Certified.Graded.SDIRKSix
