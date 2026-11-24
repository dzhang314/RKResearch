module
public import RKCert.Dirk17RadauMinor
public import RKCert.Dirk17RadauCheck
@[expose] public section
namespace RKCert.RadauEight
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired RKCert.Sextic
theorem prime_tupleFour (check:(integers.sublistsLen 4).all checkFour=true)
    (v:Fin 5→ZMod 293177) (mem:∀i,v i∈gridp) (inj:∀i j:Fin 5,i≠j→v i≠v j) :
    zEval universalFour v≠0 := by
  have lifts (i:Fin 5):∃z∈integers,(Int.castRingHom (ZMod 293177)) z=v i:=by
    have hi:=mem i;rw [map_integers] at hi;exact List.mem_map.mp hi
  choose z hz eqn using lifts
  have vi:Function.Injective v:=by intro i j e; by_contra h;exact inj _ _ h e
  have zi:Function.Injective z:=by
    intro i j e;apply vi;rw [←eqn,←eqn,e]
  have nd:(oldFour z).Nodup:=List.nodup_ofFn.mpr (zi.comp (Fin.castSucc_injective 4))
  have sub:oldFour z⊆integers:=by
    intro x hx;obtain ⟨i,eq⟩:=List.mem_ofFn.mp hx
    rw [←eq];apply hz
  obtain ⟨T,perm,inc⟩:=List.subperm_of_subset nd sub
  have dt:T.length=4:=by rw [perm.length_eq];simp [oldFour]
  have tm:T∈integers.sublistsLen 4:=List.mem_sublistsLen.mpr ⟨inc,dt⟩
  have q:=List.all_eq_true.mp check T tm
  have x:=List.all_eq_true.mp q (z (Fin.last 4)) (hz _)
  have outside:z (Fin.last 4)∉T:=by
    intro memT
    obtain ⟨i,e⟩:=List.mem_ofFn.mp (perm.mem_iff.mp memT)
    exact Fin.castSucc_ne_last i (zi e)
  simp only [Bool.or_eq_true,decide_eq_true_eq] at x
  have not0:=x.resolve_left outside
  have pol : tupleFour z%293177≠0:=by
    have cf:FixedFactor.coeffs (oldFour z)=FixedFactor.coeffs T:=funext (coeffs_perm perm.symm)
    simpa only [tupleFour,cf,quick_agrees] using not0
  rw [eval_universalFour]
  intro bad
  have map:=map_tupleFour (Int.castRingHom (ZMod 293177)) z
  have ev:(Int.castRingHom (ZMod 293177)) ∘ z=v:=funext eqn
  rw [ev,bad] at map
  exact pol (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp map))

theorem grid_tupleFour_of_check {K:Type*} [Field K] [CharZero K]
    (check:(integers.sublistsLen 4).all checkFour=true) (v:Fin 5→K)
    (roots:∀i,(grid K).eval (v i)=0) (inj:Function.Injective v) : tupleFour v≠0 := by
  have r (i:Fin 5):(scaledGrid.map (Int.castRingHom K)).eval (24310*v i)=0:=by
    have e:=scale_eqn (v i)
    rw [roots i,mul_zero] at e
    exact e
  have D:=split_prime_root_tuple 293177 scaledGrid scaled_monic gridp split_scaled
    (fun z hz=>by rw [split_scaled];exact simple_product_of_nodup gridp (by decide) hz)
    universalFour (fun i j:Fin 5=>i≠j) (prime_tupleFour check) (fun i=>24310*v i) r
    (fun i j ij e=>ij (inj (mul_left_cancel₀ (by norm_num : (24310:K)≠0) e)))
  rw [eval_universalFour,tupleFour_scale] at D
  exact (mul_ne_zero_iff.mp D).2

end RKCert.RadauEight
