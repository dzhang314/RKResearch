module
public import RKCert.DirkQuinticGridLists
@[expose] public section
namespace RKCert.DirkQuintic
open RKCert.FixedFactor

def sortedPair (p:ℤ) (L:List ℤ) (a b:ℤ) : Bool :=
  if a<b then L.all fun c=> if b<c then L.all fun u=>
    decide (u=a ∨ u=b ∨ u=c ∨ (obstruction a b c u)%p≠0) else true else true

theorem swap_first {R:Type*} [CommRing R] (a b c u:R):obstruction a b c u=obstruction b a c u := by
  unfold obstruction; congr 1 <;> unfold momentForm <;> ring

theorem swap_second {R:Type*} [CommRing R] (a b c u:R):obstruction a b c u=obstruction a c b u := by
  unfold obstruction; congr 1 <;> unfold momentForm <;> ring

theorem check_sorted {p:ℕ} (L:List ℤ)
    (h:L.all (fun a=>L.all (fun b=>sortedPair p L a b))=true) (a b c u:ℤ)
    (ma:a∈L) (mb:b∈L) (mc:c∈L) (mu:u∈L)
    (ab:a≠b) (ac:a≠c) (bc:b≠c) (ua:u≠a) (ub:u≠b) (uc:u≠c) :
    (obstruction a b c u)%(p:ℤ)≠0 := by
  have ordered (x y z:ℤ) (hx:x∈L) (hy:y∈L) (hz:z∈L)
      (xy:x<y) (yz:y<z) (ux:u≠x) (uy:u≠y) (uz:u≠z) : (obstruction x y z u)%(p:ℤ)≠0 := by
    have pair:=List.all_eq_true.mp (List.all_eq_true.mp h x hx) y hy
    simp only [sortedPair,ite_eq_left xy] at pair
    have triple:=List.all_eq_true.mp pair z hz
    rw [ite_eq_left yz] at triple
    have fin:=of_decide_eq_true (List.all_eq_true.mp triple u mu)
    exact ((fin.resolve_left ux).resolve_left uy).resolve_left uz
  by_cases g:a<b
  · by_cases j:b<c
    · exact ordered a b c ma mb mc g j ua ub uc
    · by_cases i:a<c
      · rw [swap_second];exact ordered a c b ma mc mb i (by omega) ua uc ub
      · rw [swap_second,swap_first];exact ordered c a b mc ma mb (by omega) g uc ua ub
  · by_cases j:a<c
    · rw [swap_first];exact ordered b a c mb ma mc (by omega) j ub ua uc
    · by_cases i:b<c
      · rw [swap_first,swap_second];exact ordered b c a mb mc ma i (by omega) ub uc ua
      · rw [swap_first,swap_second,swap_first];exact ordered c b a mc mb ma (by omega) (by omega) uc ub ua

theorem check_grid_int {p:ℕ} [Fact p.Prime] (L:List ℤ) (G:List (ZMod p)) (ge:G=L.map (Int.castRingHom _))
    (checked:L.all (fun a=>L.all (fun b=>sortedPair p L a b))=true)
    (v:Fin 4→ZMod p) (mem:∀i,v i∈G) (inj:∀i j:Fin 4,i≠j → v i≠v j) :
    zEval test v≠0 := by
  have pre(i:Fin 4):∃z∈L,(Int.castRingHom (ZMod p)) z=v i:=by
    have h:=mem i;rw [ge] at h;exact List.mem_map.mp h
  choose z hz eqn using pre
  have zneq (i j:Fin 4) (ij:i≠j): z i≠z j:=by
    intro e;apply inj i j ij;rw [←eqn,←eqn,e]
  have H:=check_sorted L checked (z 0) (z 1) (z 2) (z 3) (hz _) (hz _) (hz _) (hz _)
    (zneq 0 1 (by decide)) (zneq 0 2 (by decide)) (zneq 1 2 (by decide))
    (zneq 3 0 (by decide)) (zneq 3 1 (by decide)) (zneq 3 2 (by decide))
  intro zero
  have map:=map_zEval (Int.castRingHom (ZMod p)) test z
  simp only [eqn,zero] at map
  rw [eval_test] at map
  exact H (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp map))

end RKCert.DirkQuintic
