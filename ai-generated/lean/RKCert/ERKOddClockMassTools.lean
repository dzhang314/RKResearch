module
public import RKCert.ERKOddSignedRows

@[expose] public section
/-! # Fiber masses of original, possibly signed physical rows -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

def clockMass (y v:Vec K s)(a:K):K:=
  ∑i ∈ (activeRows v).filter (fun i=>y i=a),v i

theorem clockMass_apply (y v:Vec K s)(a:K):
    clockMass y v a=∑i ∈ Finset.univ.filter (fun i=>y i=a),v i:=by
  classical
  simp only [clockMass,activeRows,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases e:v i=0 <;> simp [e]

theorem moment_by_clockMass (y v:Vec K s)(P:K[X]):
    (∑ i,v i*P.eval (y i))=∑ a∈headSites y v,clockMass y v a*P.eval a:=by
  classical
  let I:=activeRows v
  calc
    _=∑i∈I,v i*P.eval (y i):=by
      symm
      simp only [I,activeRows,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases e:v i=0 <;> simp [e]
    _=∑a∈headSites y v,∑i∈I.filter (fun i=>y i=a),v i*P.eval (y i):=
      (Finset.sum_fiberwise_of_maps_to (fun _ ih=>Finset.mem_image_of_mem y ih) _).symm
    _=∑a∈headSites y v,clockMass y v a*P.eval a:=by
      apply Finset.sum_congr rfl
      intro a _
      rw [clockMass,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(Finset.mem_filter.mp hj).2]

/-- A known zero mass earns one full degree in all the other fibers. -/
theorem clockMass_all_zero_of_one (y v:Vec K s){q:ℕ}
    (small:(headSites y v).card≤q+2)
    (mom:∀P:K[X],P.natDegree≤q→(∑i,v i*P.eval (y i))=0)
    {a:K}(aS:a∈headSites y v)(a0:clockMass y v a=0):
    ∀z∈headSites y v,clockMass y v z=0:=by
  classical
  intro z hz
  by_cases za:z=a
  · rwa [za]
  let S:=headSites y v
  let T:=(S.erase a).erase z
  let P:K[X]:=Lagrange.nodal T id
  have z' :z∈S.erase a:=Finset.mem_erase.mpr ⟨za,hz⟩
  have d:P.natDegree≤q:=by
    rw [show P.natDegree=T.card from Lagrange.natDegree_nodal,
      show T=(S.erase a).erase z from rfl,Finset.card_erase_of_mem z',
      Finset.card_erase_of_mem aS]
    omega
  have pn:P.eval z≠0:=Lagrange.eval_nodal_not_at_node
    (fun w hw e=>(Finset.mem_erase.mp hw).1 e.symm)
  have e:=mom P d
  rw [moment_by_clockMass] at e
  change (∑x∈S,clockMass y v x*P.eval x)=0 at e
  have es:S=insert a (insert z T):=by rw [show T=(S.erase a).erase z from rfl,
    Finset.insert_erase z',Finset.insert_erase aS]
  conv_lhs at e => rw [es]
  rw [Finset.sum_insert (by simp [T,Ne.symm za]),Finset.sum_insert (Finset.notMem_erase _ _),a0,zero_mul,zero_add] at e
  have o:(∑x∈T,clockMass y v x*P.eval x)=0:=Finset.sum_eq_zero (fun x hx=>by
    have t:P.eval x=0:=Lagrange.eval_nodal_at_node (v:=id) hx
    rw [t,mul_zero])
  rw [o,add_zero] at e
  exact (mul_eq_zero.mp e).resolve_right pn

theorem same_active_div_clock (y v:Vec K s)(a:K)
    (absent:∀i,y i=a→v i=0):
    ∀i,(v i/(y i-a)≠0↔v i≠0):=by
  intro i
  constructor
  · intro n z
    exact n (by rw [z,zero_div])
  · intro z
    exact div_ne_zero z (sub_ne_zero.mpr (fun h=>z (absent i h)))

/-- Eight paid powers can be supplied by a small band and an extra single
clock vector, but the latter must actually belong to the true orbit. -/
theorem local_orbitBand_omit (y d ℓ:Vec K s){n:ℕ}{a:K}
    (lots:n+1≤(orbitSites y d).card)(support:∀i,y i≠a→ℓ i=0)(nz:ℓ≠0):
    ℓ∉orbitBand y d n:=by
  classical
  rintro ⟨v,he⟩
  let P:K[X]:=ofFn n v
  let T:Finset K:=(orbitSites y d).erase a
  have count:n≤T.card:=by
    change n≤((orbitSites y d).erase a).card
    by_cases a0:a∈orbitSites y d
    · rw [Finset.card_erase_of_mem a0];omega
    · rw [Finset.erase_eq_of_notMem a0];omega 
  have pd:P.degree<T.card:=(ofFn_degree_lt v).trans_le (by exact_mod_cast count)
  have e:P=0:=eq_zero_of_degree_lt_of_eval_finset_eq_zero T pd (by
    intro x hx
    obtain ⟨i,hi,eq⟩:=Finset.mem_image.mp (Finset.mem_erase.mp hx).2
    have pi:=congrFun he i
    change weightedEval y d P i=ℓ i at pi
    rw [weightedEval_apply,eq,support i (fun e=>(Finset.mem_erase.mp hx).1 (eq.symm.trans e))] at pi
    exact (mul_eq_zero.mp pi).resolve_right (Finset.mem_filter.mp hi).2)
  apply nz
  rw [←he,LinearMap.comp_apply,show ofFn n v=P from rfl,e,map_zero]
end
end RKCert.Paired.ReverseHull
