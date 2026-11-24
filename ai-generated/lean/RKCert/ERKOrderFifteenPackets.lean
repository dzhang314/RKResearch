module
public import RKCert.ERKFiniteMarkedMoments

@[expose] public section

/-! # Exact order-fifteen full and marked midpoint moment decoders.
Use only small rational elimination on the actual available moments.
The generator is not a dependency of any theorem. -/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option maxHeartbeats 5000000

theorem meshOddFull7_decode (P:K[X]) (hd:P.natDegree≤8) (h0:P.coeff 0=0)
    (h:∀ i:Fin 7,scalarMoment P i.val=0) :
    ∃ t:K,P=t • odd7 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := by omega
  have z0 : a 0=0 := h0
  have z9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have m0 := h 0
  rw [scalarMoment_11 P d10] at m0
  change moment a 1 0=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10] at m1
  change moment a 1 1=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10] at m2
  change moment a 1 2=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10] at m3
  change moment a 1 3=0 at m3
  have m4 := h 4
  rw [scalarMoment_11 P d10] at m4
  change moment a 1 4=0 at m4
  have m5 := h 5
  rw [scalarMoment_11 P d10] at m5
  change moment a 1 5=0 at m5
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  norm_num [moment,Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6
  let t:K := ((1/6435)) * a 8
  have c1 : a 1=((-8/6435)) * a 8 := by
    linear_combination (1568) * m0 + (-28224) * m1 + (176400) * m2 + (-517440) * m3 + (776160) * m4 + (-576576) * m5 + (168168) * m6 + (-56) * z0 + ((-7/1430)) * z9 + ((-28/2431)) * z10
  have c2 : a 2=((28/715)) * a 8 := by
    linear_combination (-28224) * m0 + (571536) * m1 + (-3810240) * m2 + (11642400) * m3 + (-17962560) * m4 + (13621608) * m5 + (-4036032) * m6 + (756) * z0 + ((108/715)) * z9 + ((1701/4862)) * z10
  have c3 : a 3=((-56/143)) * a 8 := by
    linear_combination (176400) * m0 + (-3810240) * m1 + (26460000) * m2 + (-83160000) * m3 + (130977000) * m4 + (-100900800) * m5 + (30270240) * m6 + (-4200) * z0 + ((-210/143)) * z9 + ((-8100/2431)) * z10
  have c4 : a 4=((70/39)) * a 8 := by
    linear_combination (-517440) * m0 + (11642400) * m1 + (-83160000) * m2 + (266805000) * m3 + (-426888000) * m4 + (332972640) * m5 + (-100900800) * m6 + (11550) * z0 + ((84/13)) * z9 + ((3150/221)) * z10
  have c5 : a 5=((-56/13)) * a 8 := by
    linear_combination (776160) * m0 + (-17962560) * m1 + (130977000) * m2 + (-426888000) * m3 + (691558560) * m4 + (-544864320) * m5 + (166486320) * m6 + (-16632) * z0 + ((-189/13)) * z9 + ((-6804/221)) * z10
  have c6 : a 6=((28/5)) * a 8 := by
    linear_combination (-576576) * m0 + (13621608) * m1 + (-100900800) * m2 + (332972640) * m3 + (-544864320) * m4 + (432864432) * m5 + (-133189056) * m6 + (12012) * z0 + ((84/5)) * z9 + ((567/17)) * z10
  have c7 : a 7=((-56/15)) * a 8 := by
    linear_combination (168168) * m0 + (-4036032) * m1 + (30270240) * m2 + (-100900800) * m3 + (166486320) * m4 + (-133189056) * m5 + (41225184) * m6 + (-3432) * z0 + ((-42/5)) * z9 + ((-252/17)) * z10
  have vv : a=t • ![0, -8, 252, -2520, 11550, -27720, 36036, -24024, 6435, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp only [t]
      linear_combination z0
    · change a 1=t * (-8:K)
      dsimp only [t]
      linear_combination c1
    · change a 2=t * (252:K)
      dsimp only [t]
      linear_combination c2
    · change a 3=t * (-2520:K)
      dsimp only [t]
      linear_combination c3
    · change a 4=t * (11550:K)
      dsimp only [t]
      linear_combination c4
    · change a 5=t * (-27720:K)
      dsimp only [t]
      linear_combination c5
    · change a 6=t * (36036:K)
      dsimp only [t]
      linear_combination c6
    · change a 7=t * (-24024:K)
      dsimp only [t]
      linear_combination c7
    · change a 8=t * (6435:K)
      dsimp only [t]
      ring
    · change a 9=t * (0:K)
      dsimp only [t]
      linear_combination z9
    · change a 10=t * (0:K)
      dsimp only [t]
      linear_combination z10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • odd7 := by
      rw [vv]
      unfold odd7 from11
      simp only [map_smul]

theorem meshOddPrefix7_decode (P:K[X]) (hd:P.natDegree≤8) (h0:P.coeff 0=0)
    (h:∀ i:Fin 6,scalarMoment P i.val-scalarMoment P (i.val+1)=0) :
    ∃ t u:K,P=t • dx6+u • dx7 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := by omega
  have z0 : a 0=0 := h0
  have z9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have z10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have m0 := h 0
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m0
  change moment a 1 0-moment a 1 1=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m1
  change moment a 1 1-moment a 1 2=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m2
  change moment a 1 2-moment a 1 3=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m3
  change moment a 1 3-moment a 1 4=0 at m3
  have m4 := h 4
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m4
  change moment a 1 4-moment a 1 5=0 at m4
  have m5 := h 5
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m5
  change moment a 1 5-moment a 1 6=0 at m5
  norm_num [moment,Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5
  let t:K := ((1/24024)) * a 7 + ((1/6864)) * a 8
  let u:K := ((1/102960)) * a 8
  have c1 : a 1=((1/429)) * a 7 + ((16/2145)) * a 8 := by
    linear_combination (1176) * m0 + (-17640) * m1 + (88200) * m2 + (-194040) * m3 + (194040) * m4 + (-72072) * m5 + (-48) * z0 + ((21/1430)) * z9 + ((56/2431)) * z10
  have c2 : a 2=((-9/143)) * a 7 + ((-28/143)) * a 8 := by
    linear_combination (-17640) * m0 + (299880) * m1 + (-1605240) * m2 + (3686760) * m3 + (-3797640) * m4 + (1441440) * m5 + (540) * z0 + ((-54/143)) * z9 + ((-2835/4862)) * z10
  have c3 : a 3=((75/143)) * a 7 + ((224/143)) * a 8 := by
    linear_combination (88200) * m0 + (-1605240) * m1 + (8978760) * m2 + (-21261240) * m3 + (22397760) * m4 + (-8648640) * m5 + (-2400) * z0 + ((420/143)) * z9 + ((10800/2431)) * z10
  have c4 : a 4=((-25/13)) * a 7 + ((-70/13)) * a 8 := by
    linear_combination (-194040) * m0 + (3686760) * m1 + (-21261240) * m2 + (51503760) * m3 + (-55218240) * m4 + (21621600) * m5 + (4950) * z0 + ((-126/13)) * z9 + ((-3150/221)) * z10
  have c5 : a 5=((45/13)) * a 7 + ((112/13)) * a 8 := by
    linear_combination (194040) * m0 + (-3797640) * m1 + (22397760) * m2 + (-55218240) * m3 + (60041520) * m4 + (-23783760) * m5 + (-4752) * z0 + ((189/13)) * z9 + ((4536/221)) * z10
  have c6 : a 6=(-3) * a 7 + ((-28/5)) * a 8 := by
    linear_combination (-72072) * m0 + (1441440) * m1 + (-8648640) * m2 + (21621600) * m3 + (-23783760) * m4 + (9513504) * m5 + (1716) * z0 + ((-42/5)) * z9 + ((-189/17)) * z10
  have vv : a=t • ![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0]+u • ![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp only [t,u]
      linear_combination z0
    · change a 1=t * (56:K) + u * (-72:K)
      dsimp only [t,u]
      linear_combination c1
    · change a 2=t * (-1512:K) + u * (2520:K)
      dsimp only [t,u]
      linear_combination c2
    · change a 3=t * (12600:K) + u * (-27720:K)
      dsimp only [t,u]
      linear_combination c3
    · change a 4=t * (-46200:K) + u * (138600:K)
      dsimp only [t,u]
      linear_combination c4
    · change a 5=t * (83160:K) + u * (-360360:K)
      dsimp only [t,u]
      linear_combination c5
    · change a 6=t * (-72072:K) + u * (504504:K)
      dsimp only [t,u]
      linear_combination c6
    · change a 7=t * (24024:K) + u * (-360360:K)
      dsimp only [t,u]
      ring
    · change a 8=t * (0:K) + u * (102960:K)
      dsimp only [t,u]
      ring
    · change a 9=t * (0:K) + u * (0:K)
      dsimp only [t,u]
      linear_combination z9
    · change a 10=t * (0:K) + u * (0:K)
      dsimp only [t,u]
      linear_combination z10
  refine ⟨t,u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx6+u • dx7 := by
      rw [vv]
      unfold dx6 dx7 from11
      simp only [map_add,map_smul]

end RKCert.Paired.FiniteMidpoint
