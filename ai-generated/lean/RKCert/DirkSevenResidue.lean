module
public import RKCert.DirkSevenHankel
public import RKCert.LobattoFactorTables
@[expose] public section
namespace RKCert.SevenPort
open Polynomial Matrix RKCert.PortRank RKCert.FixedFactor
set_option maxRecDepth 6000
instance prime1009:Fact (Nat.Prime 1009):=⟨by decide +kernel⟩
abbrev E:=ZMod 1009
def horner (xs:List ℤ)(x:E):E:=xs.foldr (fun a z=>(a:E)+x*z) 0
noncomputable def mp (xs:List ℤ):E[X]:=(intHorner xs).map (Int.castRingHom E)
theorem horner_sound (xs:List ℤ)(x:E):(mp xs).eval x=horner xs x:=by
  induction xs with
  | nil=>simp [mp,intHorner,horner]
  | cons a l ih=>
    change ((C a + X*intHorner l).map _).eval x=(a:E)+x*horner l x
    rw [Polynomial.map_add,Polynomial.map_mul,map_C,map_X,eval_add,eval_C,eval_mul,eval_X,←ih];rfl

theorem injective_sample (n:ℕ)(small:n≤1009):Function.Injective (fun i:Fin n=>(i.val:E)):=by
  intro i j ij;apply Fin.ext
  have ii:=i.isLt;have jj:=j.isLt
  have eqn:=congrArg ZMod.val ij
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega:i.val<1009),Nat.mod_eq_of_lt (by omega:j.val<1009)] using eqn

theorem samples {F G:E[X]} (d:ℕ)(paid:d+1≤1009)(df:F.natDegree≤d)(dg:G.natDegree≤d)
    (checks:∀i:Fin (d+1),F.eval (i.val:E)=G.eval (i.val:E)):F=G:=by
  apply sub_eq_zero.mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (F-G) (injective_sample _ paid)
  · intro i;rw [eval_sub,checks i,sub_self]
  · have h:=natDegree_sub_le F G;simp only [Fintype.card_fin];omega

def calcMinor (t x:E)(k:ℕ):E:=smallDet 5 (matrix t x k)

theorem fits (t:E)(k:ℕ)(xs:List ℤ)(d:xs.length≤31)
    (checks:∀i:Fin 31,calcMinor t (i.val:E) k=horner xs (i.val:E)):
    minPoly t k=mp xs:=by
  apply samples 30 (by decide) (degree_minor _ _) (natDegree_map_le.trans (degree_horner_le _ _ d))
  intro i;change (minPoly t k).eval (i.val:E)=(mp xs).eval (i.val:E);rw [eval_minor,horner_sound]
  have h:=checks i
  rw [calcMinor,smallDet_eq_det] at h
  exact h

theorem coprime_from_samples (f g a b:List ℤ)(hf:f.length≤31)(hg:g.length≤31)(ha:a.length≤30)(hb:b.length≤30)
    (check:∀i:Fin 61,horner a (i.val:E)*horner f (i.val:E)+horner b (i.val:E)*horner g (i.val:E)=1):
    IsCoprime (mp f) (mp g):=by
  refine ⟨mp a,mp b,?_⟩
  have bound (l:List ℤ)(k:ℕ)(hl:l.length≤k+1):(mp l).natDegree≤k:=natDegree_map_le.trans (degree_horner_le _ _ hl)
  apply samples 60 (by decide) ((natDegree_add_le _ _).trans (max_le
    (natDegree_mul_le.trans (by have:=bound a 29 ha;have:=bound f 30 hf;omega))
    (natDegree_mul_le.trans (by have:=bound b 29 hb;have:=bound g 30 hg;omega)))) (by simp)
  intro i;rw [eval_add,eval_mul,eval_mul,horner_sound,horner_sound,horner_sound,horner_sound,eval_one];exact check i
end RKCert.SevenPort
