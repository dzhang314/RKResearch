module
public import RKCert.DirkFifthMinor
public import RKCert.DirkQuinticIntegerLists
@[expose] public section
namespace RKCert.PaidFifth
open RKCert.FixedFactor RKCert.DirkQuintic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def goodInt (u v:ℤ):Bool:=integers10.all fun z=> decide (u=v ∨ u=z ∨ v=z ∨ minor u v z % 15727≠0)
private theorem tiny0_0 : goodInt 0 0=true:=by decide +kernel
private theorem tiny0_1 : goodInt 0 1069=true:=by decide +kernel
private theorem tiny0_2 : goodInt 0 1186=true:=by decide +kernel
private theorem tiny0_3 : goodInt 0 6796=true:=by decide +kernel
private theorem tiny0_4 : goodInt 0 7356=true:=by decide +kernel
private theorem tiny0_5 : goodInt 0 7876=true:=by decide +kernel
private theorem tiny0_6 : goodInt 0 8398=true:=by decide +kernel
private theorem tiny0_7 : goodInt 0 8920=true:=by decide +kernel
private theorem tiny0_8 : goodInt 0 9440=true:=by decide +kernel
private theorem tiny0_9 : goodInt 0 10000=true:=by decide +kernel
private theorem tiny0_10 : goodInt 0 15610=true:=by decide +kernel
private theorem r0 : integers10.all (goodInt 0)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny0_0
  · exact tiny0_1
  · exact tiny0_2
  · exact tiny0_3
  · exact tiny0_4
  · exact tiny0_5
  · exact tiny0_6
  · exact tiny0_7
  · exact tiny0_8
  · exact tiny0_9
  · exact tiny0_10

private theorem tiny1_0 : goodInt 1069 0=true:=by decide +kernel
private theorem tiny1_1 : goodInt 1069 1069=true:=by decide +kernel
private theorem tiny1_2 : goodInt 1069 1186=true:=by decide +kernel
private theorem tiny1_3 : goodInt 1069 6796=true:=by decide +kernel
private theorem tiny1_4 : goodInt 1069 7356=true:=by decide +kernel
private theorem tiny1_5 : goodInt 1069 7876=true:=by decide +kernel
private theorem tiny1_6 : goodInt 1069 8398=true:=by decide +kernel
private theorem tiny1_7 : goodInt 1069 8920=true:=by decide +kernel
private theorem tiny1_8 : goodInt 1069 9440=true:=by decide +kernel
private theorem tiny1_9 : goodInt 1069 10000=true:=by decide +kernel
private theorem tiny1_10 : goodInt 1069 15610=true:=by decide +kernel
private theorem r1 : integers10.all (goodInt 1069)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny1_0
  · exact tiny1_1
  · exact tiny1_2
  · exact tiny1_3
  · exact tiny1_4
  · exact tiny1_5
  · exact tiny1_6
  · exact tiny1_7
  · exact tiny1_8
  · exact tiny1_9
  · exact tiny1_10

private theorem tiny2_0 : goodInt 1186 0=true:=by decide +kernel
private theorem tiny2_1 : goodInt 1186 1069=true:=by decide +kernel
private theorem tiny2_2 : goodInt 1186 1186=true:=by decide +kernel
private theorem tiny2_3 : goodInt 1186 6796=true:=by decide +kernel
private theorem tiny2_4 : goodInt 1186 7356=true:=by decide +kernel
private theorem tiny2_5 : goodInt 1186 7876=true:=by decide +kernel
private theorem tiny2_6 : goodInt 1186 8398=true:=by decide +kernel
private theorem tiny2_7 : goodInt 1186 8920=true:=by decide +kernel
private theorem tiny2_8 : goodInt 1186 9440=true:=by decide +kernel
private theorem tiny2_9 : goodInt 1186 10000=true:=by decide +kernel
private theorem tiny2_10 : goodInt 1186 15610=true:=by decide +kernel
private theorem r2 : integers10.all (goodInt 1186)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny2_0
  · exact tiny2_1
  · exact tiny2_2
  · exact tiny2_3
  · exact tiny2_4
  · exact tiny2_5
  · exact tiny2_6
  · exact tiny2_7
  · exact tiny2_8
  · exact tiny2_9
  · exact tiny2_10

private theorem tiny3_0 : goodInt 6796 0=true:=by decide +kernel
private theorem tiny3_1 : goodInt 6796 1069=true:=by decide +kernel
private theorem tiny3_2 : goodInt 6796 1186=true:=by decide +kernel
private theorem tiny3_3 : goodInt 6796 6796=true:=by decide +kernel
private theorem tiny3_4 : goodInt 6796 7356=true:=by decide +kernel
private theorem tiny3_5 : goodInt 6796 7876=true:=by decide +kernel
private theorem tiny3_6 : goodInt 6796 8398=true:=by decide +kernel
private theorem tiny3_7 : goodInt 6796 8920=true:=by decide +kernel
private theorem tiny3_8 : goodInt 6796 9440=true:=by decide +kernel
private theorem tiny3_9 : goodInt 6796 10000=true:=by decide +kernel
private theorem tiny3_10 : goodInt 6796 15610=true:=by decide +kernel
private theorem r3 : integers10.all (goodInt 6796)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny3_0
  · exact tiny3_1
  · exact tiny3_2
  · exact tiny3_3
  · exact tiny3_4
  · exact tiny3_5
  · exact tiny3_6
  · exact tiny3_7
  · exact tiny3_8
  · exact tiny3_9
  · exact tiny3_10

private theorem tiny4_0 : goodInt 7356 0=true:=by decide +kernel
private theorem tiny4_1 : goodInt 7356 1069=true:=by decide +kernel
private theorem tiny4_2 : goodInt 7356 1186=true:=by decide +kernel
private theorem tiny4_3 : goodInt 7356 6796=true:=by decide +kernel
private theorem tiny4_4 : goodInt 7356 7356=true:=by decide +kernel
private theorem tiny4_5 : goodInt 7356 7876=true:=by decide +kernel
private theorem tiny4_6 : goodInt 7356 8398=true:=by decide +kernel
private theorem tiny4_7 : goodInt 7356 8920=true:=by decide +kernel
private theorem tiny4_8 : goodInt 7356 9440=true:=by decide +kernel
private theorem tiny4_9 : goodInt 7356 10000=true:=by decide +kernel
private theorem tiny4_10 : goodInt 7356 15610=true:=by decide +kernel
private theorem r4 : integers10.all (goodInt 7356)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny4_0
  · exact tiny4_1
  · exact tiny4_2
  · exact tiny4_3
  · exact tiny4_4
  · exact tiny4_5
  · exact tiny4_6
  · exact tiny4_7
  · exact tiny4_8
  · exact tiny4_9
  · exact tiny4_10

private theorem tiny5_0 : goodInt 7876 0=true:=by decide +kernel
private theorem tiny5_1 : goodInt 7876 1069=true:=by decide +kernel
private theorem tiny5_2 : goodInt 7876 1186=true:=by decide +kernel
private theorem tiny5_3 : goodInt 7876 6796=true:=by decide +kernel
private theorem tiny5_4 : goodInt 7876 7356=true:=by decide +kernel
private theorem tiny5_5 : goodInt 7876 7876=true:=by decide +kernel
private theorem tiny5_6 : goodInt 7876 8398=true:=by decide +kernel
private theorem tiny5_7 : goodInt 7876 8920=true:=by decide +kernel
private theorem tiny5_8 : goodInt 7876 9440=true:=by decide +kernel
private theorem tiny5_9 : goodInt 7876 10000=true:=by decide +kernel
private theorem tiny5_10 : goodInt 7876 15610=true:=by decide +kernel
private theorem r5 : integers10.all (goodInt 7876)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny5_0
  · exact tiny5_1
  · exact tiny5_2
  · exact tiny5_3
  · exact tiny5_4
  · exact tiny5_5
  · exact tiny5_6
  · exact tiny5_7
  · exact tiny5_8
  · exact tiny5_9
  · exact tiny5_10

private theorem tiny6_0 : goodInt 8398 0=true:=by decide +kernel
private theorem tiny6_1 : goodInt 8398 1069=true:=by decide +kernel
private theorem tiny6_2 : goodInt 8398 1186=true:=by decide +kernel
private theorem tiny6_3 : goodInt 8398 6796=true:=by decide +kernel
private theorem tiny6_4 : goodInt 8398 7356=true:=by decide +kernel
private theorem tiny6_5 : goodInt 8398 7876=true:=by decide +kernel
private theorem tiny6_6 : goodInt 8398 8398=true:=by decide +kernel
private theorem tiny6_7 : goodInt 8398 8920=true:=by decide +kernel
private theorem tiny6_8 : goodInt 8398 9440=true:=by decide +kernel
private theorem tiny6_9 : goodInt 8398 10000=true:=by decide +kernel
private theorem tiny6_10 : goodInt 8398 15610=true:=by decide +kernel
private theorem r6 : integers10.all (goodInt 8398)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny6_0
  · exact tiny6_1
  · exact tiny6_2
  · exact tiny6_3
  · exact tiny6_4
  · exact tiny6_5
  · exact tiny6_6
  · exact tiny6_7
  · exact tiny6_8
  · exact tiny6_9
  · exact tiny6_10

private theorem tiny7_0 : goodInt 8920 0=true:=by decide +kernel
private theorem tiny7_1 : goodInt 8920 1069=true:=by decide +kernel
private theorem tiny7_2 : goodInt 8920 1186=true:=by decide +kernel
private theorem tiny7_3 : goodInt 8920 6796=true:=by decide +kernel
private theorem tiny7_4 : goodInt 8920 7356=true:=by decide +kernel
private theorem tiny7_5 : goodInt 8920 7876=true:=by decide +kernel
private theorem tiny7_6 : goodInt 8920 8398=true:=by decide +kernel
private theorem tiny7_7 : goodInt 8920 8920=true:=by decide +kernel
private theorem tiny7_8 : goodInt 8920 9440=true:=by decide +kernel
private theorem tiny7_9 : goodInt 8920 10000=true:=by decide +kernel
private theorem tiny7_10 : goodInt 8920 15610=true:=by decide +kernel
private theorem r7 : integers10.all (goodInt 8920)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny7_0
  · exact tiny7_1
  · exact tiny7_2
  · exact tiny7_3
  · exact tiny7_4
  · exact tiny7_5
  · exact tiny7_6
  · exact tiny7_7
  · exact tiny7_8
  · exact tiny7_9
  · exact tiny7_10

private theorem tiny8_0 : goodInt 9440 0=true:=by decide +kernel
private theorem tiny8_1 : goodInt 9440 1069=true:=by decide +kernel
private theorem tiny8_2 : goodInt 9440 1186=true:=by decide +kernel
private theorem tiny8_3 : goodInt 9440 6796=true:=by decide +kernel
private theorem tiny8_4 : goodInt 9440 7356=true:=by decide +kernel
private theorem tiny8_5 : goodInt 9440 7876=true:=by decide +kernel
private theorem tiny8_6 : goodInt 9440 8398=true:=by decide +kernel
private theorem tiny8_7 : goodInt 9440 8920=true:=by decide +kernel
private theorem tiny8_8 : goodInt 9440 9440=true:=by decide +kernel
private theorem tiny8_9 : goodInt 9440 10000=true:=by decide +kernel
private theorem tiny8_10 : goodInt 9440 15610=true:=by decide +kernel
private theorem r8 : integers10.all (goodInt 9440)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny8_0
  · exact tiny8_1
  · exact tiny8_2
  · exact tiny8_3
  · exact tiny8_4
  · exact tiny8_5
  · exact tiny8_6
  · exact tiny8_7
  · exact tiny8_8
  · exact tiny8_9
  · exact tiny8_10

private theorem tiny9_0 : goodInt 10000 0=true:=by decide +kernel
private theorem tiny9_1 : goodInt 10000 1069=true:=by decide +kernel
private theorem tiny9_2 : goodInt 10000 1186=true:=by decide +kernel
private theorem tiny9_3 : goodInt 10000 6796=true:=by decide +kernel
private theorem tiny9_4 : goodInt 10000 7356=true:=by decide +kernel
private theorem tiny9_5 : goodInt 10000 7876=true:=by decide +kernel
private theorem tiny9_6 : goodInt 10000 8398=true:=by decide +kernel
private theorem tiny9_7 : goodInt 10000 8920=true:=by decide +kernel
private theorem tiny9_8 : goodInt 10000 9440=true:=by decide +kernel
private theorem tiny9_9 : goodInt 10000 10000=true:=by decide +kernel
private theorem tiny9_10 : goodInt 10000 15610=true:=by decide +kernel
private theorem r9 : integers10.all (goodInt 10000)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny9_0
  · exact tiny9_1
  · exact tiny9_2
  · exact tiny9_3
  · exact tiny9_4
  · exact tiny9_5
  · exact tiny9_6
  · exact tiny9_7
  · exact tiny9_8
  · exact tiny9_9
  · exact tiny9_10

private theorem tiny10_0 : goodInt 15610 0=true:=by decide +kernel
private theorem tiny10_1 : goodInt 15610 1069=true:=by decide +kernel
private theorem tiny10_2 : goodInt 15610 1186=true:=by decide +kernel
private theorem tiny10_3 : goodInt 15610 6796=true:=by decide +kernel
private theorem tiny10_4 : goodInt 15610 7356=true:=by decide +kernel
private theorem tiny10_5 : goodInt 15610 7876=true:=by decide +kernel
private theorem tiny10_6 : goodInt 15610 8398=true:=by decide +kernel
private theorem tiny10_7 : goodInt 15610 8920=true:=by decide +kernel
private theorem tiny10_8 : goodInt 15610 9440=true:=by decide +kernel
private theorem tiny10_9 : goodInt 15610 10000=true:=by decide +kernel
private theorem tiny10_10 : goodInt 15610 15610=true:=by decide +kernel
private theorem r10 : integers10.all (goodInt 15610)=true:=by
  apply List.all_eq_true.mpr;intro v hv
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact tiny10_0
  · exact tiny10_1
  · exact tiny10_2
  · exact tiny10_3
  · exact tiny10_4
  · exact tiny10_5
  · exact tiny10_6
  · exact tiny10_7
  · exact tiny10_8
  · exact tiny10_9
  · exact tiny10_10

theorem checkedInt : integers10.all (fun u=>integers10.all (goodInt u))=true:=by
  apply List.all_eq_true.mpr;intro u hu
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8
  · exact r9
  · exact r10

theorem mod_minor (w:Fin 3→ZMod 15727) (all:∀i,w i∈grid10) (inj:∀i j:Fin 3,i≠j→w i≠w j):
    zEval test w≠0:=by
  classical
  have lift(i:Fin 3):∃x:ℤ,x∈integers10 ∧ (Int.castRingHom (ZMod 15727)) x=w i:=by
    have m:=all i;rw [map_integers10] at m;exact List.mem_map.mp m
  choose x hx he using lift
  have n(i j:Fin 3) (ne:i≠j):x i≠x j:=fun eq=>inj i j ne ((he i).symm.trans ((congrArg _ eq).trans (he j)))
  have rr:=List.all_eq_true.mp (List.all_eq_true.mp checkedInt (x 0) (hx 0)) (x 1) (hx 1)
  have res:=of_decide_eq_true (List.all_eq_true.mp rr (x 2) (hx 2))
  obtain eq|eq|eq|nz:=res
  · exact (n 0 1 (by decide) eq).elim
  · exact (n 0 2 (by decide) eq).elim
  · exact (n 1 2 (by decide) eq).elim
  intro z
  have cast:=map_zEval (Int.castRingHom (ZMod 15727)) test x
  simp only [he,z] at cast
  rw [eval_test] at cast
  exact nz (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp cast))
end RKCert.PaidFifth

