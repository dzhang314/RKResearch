module
public import RKCert.SexticMomentCuts
public import RKCert.SexticFiniteSetup
@[expose] public section
namespace RKCert.Sextic
open Polynomial RKCert.FixedFactor RKCert.DirkQuintic RKCert.Paired.Terminal

theorem coeffs_perm {R:Type*} [CommRing R] {l t:List R} (p:l.Perm t) :
    ∀i,FixedFactor.coeffs l i=FixedFactor.coeffs t i :=by
  induction p with
  | nil=>intro;rfl
  | cons a p ih=>intro i;cases i <;>simp [FixedFactor.coeffs,ih]
  | swap a b l=>
    intro i
    cases i with
    | zero=>simp [FixedFactor.coeffs];ring
    | succ k=>cases k <;>simp [FixedFactor.coeffs] <;>ring
  | trans p q ih ij=>intro i;exact (ih i).trans (ij i)

theorem quick_agrees {R:Type*} [CommRing R] (c:ℕ→R) (u:R) :
    minor c u=quick (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) u := by
  norm_num [minor,row,Fin.sum_univ_succ,quick]
  ring

theorem prime_tuple (check:(integers10.sublistsLen 5).all checkQuint=true)
    (v:Fin 6→ZMod 15727) (mem:∀i,v i∈grid10) (inj:∀i j:Fin 6,i≠j→v i≠v j) :
    zEval universal v≠0 := by
  have lifts (i:Fin 6):∃z∈integers10,(Int.castRingHom (ZMod 15727)) z=v i:=by
    have hi:=mem i;rw [map_integers10] at hi;exact List.mem_map.mp hi
  choose z hz eqn using lifts
  have vi:Function.Injective v:=by intro i j e; by_contra h;exact inj _ _ h e
  have zi:Function.Injective z:=by
    intro i j e;apply vi;rw [←eqn,←eqn,e]
  have nd:(old z).Nodup:=List.nodup_ofFn.mpr (zi.comp (Fin.castSucc_injective 5))
  have sub:old z⊆integers10:=by
    intro x hx;obtain ⟨i,eq⟩:=List.mem_ofFn.mp hx
    rw [←eq];apply hz
  obtain ⟨T,perm,inc⟩:=List.subperm_of_subset nd sub
  have dt:T.length=5:=by rw [perm.length_eq];simp [old]
  have tm:T∈integers10.sublistsLen 5:=List.mem_sublistsLen.mpr ⟨inc,dt⟩
  have q:=List.all_eq_true.mp check T tm
  have x:=List.all_eq_true.mp q (z (Fin.last 5)) (hz _)
  have outside:z (Fin.last 5)∉T:=by
    intro memT
    obtain ⟨i,e⟩:=List.mem_ofFn.mp (perm.mem_iff.mp memT)
    exact Fin.castSucc_ne_last i (zi e)
  simp only [Bool.or_eq_true,decide_eq_true_eq] at x
  have not0:=x.resolve_left outside
  have pol : tuple z%15727≠0:=by
    have cf:FixedFactor.coeffs (old z)=FixedFactor.coeffs T:=funext (coeffs_perm perm.symm)
    simpa only [tuple,cf,quick_agrees] using not0
  rw [eval_universal]
  intro bad
  have map:=map_tuple (Int.castRingHom (ZMod 15727)) z
  have ev:(Int.castRingHom (ZMod 15727)) ∘ z=v:=funext eqn
  rw [ev,bad] at map
  exact pol (Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp map))

theorem grid_tuple_of_check {K:Type*} [Field K] [CharZero K]
    (check:(integers10.sublistsLen 5).all checkQuint=true) (v:Fin 6→K)
    (roots:∀i,((X-1)*lobatto 10).eval (v i)=0) (inj:Function.Injective v) : tuple v≠0 := by
  have r (i:Fin 6):(integral10.map (Int.castRingHom K)).eval (16796*v i)=0:=by
    have e:=scale_eqn10 (v i)
    rw [roots i,mul_zero] at e
    exact (mul_eq_zero.mp e).resolve_left (by norm_num)
  have D:=split_prime_root_tuple 15727 integral10 monic_scaled10 grid10 split_scaled10
    (fun z hz=>by rw [split_scaled10];exact simple_product_of_nodup grid10 (by decide) hz)
    universal (fun i j:Fin 6=>i≠j) (prime_tuple check) (fun i=>16796*v i) r
    (fun i j ij e=>ij (inj (mul_left_cancel₀ (by norm_num : (16796:K)≠0) e)))
  rw [eval_universal,tuple_scale] at D
  exact (mul_ne_zero_iff.mp D).2

end RKCert.Sextic
