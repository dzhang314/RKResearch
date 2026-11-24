module
public import RKCert.ERKOddBroadCarrier
public import RKCert.DirkEvenPhysicalCount

@[expose] public section
/-! # Signed physical row counts with separately paid degree cutoff -/
namespace RKCert.Paired.ReverseHull
open RKCert.Paired.Clock RKCert.Paired.ERKEvenHidden RKCert.Endpoint Polynomial
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ}
noncomputable section

theorem local_mass_zero_of_short_support (y v:Vec K s) {l:ℕ}
    (small:(headSites y v).card≤l+1)
    (mom:∀P:K[X],P.natDegree≤l→(∑i,v i*P.eval (y i))=0)
    {a:K}(mem:a∈headSites y v):
    (∑i ∈ (activeRows v).filter (fun i=>y i=a),v i)=0:=by
  classical
  let S:=headSites y v
  change a∈S at mem
  let T:=S.erase a
  let P:=Lagrange.nodal T id
  have d:P.natDegree≤l:=by
    rw [show P.natDegree=T.card from Lagrange.natDegree_nodal,Finset.card_erase_of_mem mem]
    change S.card≤l+1 at small
    omega
  have nz:P.eval a≠0:=Lagrange.eval_nodal_not_at_node (fun a' ha e=>
    (Finset.mem_erase.mp ha).1 e.symm)
  have e:(∑i,v i*P.eval (y i))=P.eval a*(∑i ∈ (activeRows v).filter (fun i=>y i=a),v i):=by
    rw [Finset.mul_sum,Finset.sum_filter]
    symm
    have eq:(∑i ∈ activeRows v,if y i=a then P.eval a*v i else 0)=
        ∑ i ∈ Finset.univ,if v i≠0 then (if y i=a then P.eval a*v i else 0) else 0:=by
      rw [activeRows,Finset.sum_filter]
    rw [eq]
    apply Finset.sum_congr rfl
    intro i _
    by_cases e:v i=0
    · simp [e]
    by_cases z:y i=a
    · simp [e,z,mul_comm]
    have hi:y i∈T:=Finset.mem_erase.mpr ⟨z,headSites_mem (c:=y) i e⟩
    have Z:P.eval (y i)=0:=Lagrange.eval_nodal_at_node (v:=id) hi
    simp [e,z,Z]
  rw [mom P d] at e
  exact (mul_eq_zero.mp e.symm).resolve_left nz

theorem paid_signed_row_lower (y v:Vec K s) {k N:ℕ}
    (site:k≤(headSites y v).card)(N2:N≤2*k)
    (mom:∀P:K[X],P.natDegree+2≤N→(∑i,v i*P.eval (y i))=0):
    N≤(activeRows v).card:=by
  classical
  let I:=activeRows v
  let S:=headSites y v
  have e:S=I.image y:=rfl
  by_cases many:N≤S.card
  · exact many.trans (show S.card≤I.card from Finset.card_image_le)
  have N1:1≤N:=by omega
  have sc:S.card≤(N-2)+1:=by omega
  have f (a:K)(aa:a∈S):2≤(I.filter (fun i=>y i=a)).card:=by
    by_contra! low
    have sum:=local_mass_zero_of_short_support y v sc (fun P pp=>mom P (by
      have one:1≤S.card:=Finset.card_pos.mpr ⟨a,aa⟩
      omega)) aa
    obtain ⟨i,hi,e⟩:=Finset.mem_image.mp aa
    have him:i∈I.filter (fun i=>y i=a):=Finset.mem_filter.mpr ⟨hi,e⟩
    have ss:I.filter (fun i=>y i=a)={i}:=Finset.eq_singleton_iff_unique_mem.mpr ⟨him,fun j hj=>
      Finset.card_le_one.mp (by omega:(I.filter (fun i=>y i=a)).card≤1) _ hj _ him⟩
    rw [ss,Finset.sum_singleton] at sum
    exact (mem_activeRows i).mp hi sum
  calc
    N≤2*S.card:=N2.trans (Nat.mul_le_mul_left _ site)
    _=∑ _a∈S,2:=by simp [Nat.mul_comm]
    _≤∑ a∈S,(I.filter (fun i=>y i=a)).card:=Finset.sum_le_sum f
    _=I.card:=(Finset.card_eq_sum_card_image y I).symm

end
end RKCert.Paired.ReverseHull

