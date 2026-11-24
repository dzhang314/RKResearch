module
public import RKCert.DirkCubicSignedBudget
public import RKCert.DirkTwentyOrigin
@[expose] public section
namespace RKCert.Paired.Terminal
open Module
open scoped Classical
variable {K:Type*} [Field K] {s:ℕ} {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
noncomputable section

def cleanActive (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)):Finset (Fin (s+1)):=
  Finset.univ.filter fun i=>b i≠0 ∧ tau A b i=0

theorem mem_cleanActive (i:Fin (s+1)):i∈cleanActive A b ↔ b i≠0 ∧ tau A b i=0:=by simp [cleanActive]

/-- A joint hidden dimension costs an actual coordinate outside both the
clean active rows and every physically occupied cubic row. -/
theorem clean_active_plus_joint (e:ℕ): (cleanActive A b).card+finrank K (jointWithOrigin A b e)+
    (Finset.univ.filter fun i=>tau A b i≠0).card≤s+1:=by
  classical
  let N:=Finset.univ.filter fun i=>b i=0 ∧ tau A b i=0
  let D:=Finset.univ.filter fun i=>tau A b i≠0
  let U:=jointWithOrigin A b e
  let L:U→ₗ[K] (N→K):=LinearMap.pi fun i:N=>(LinearMap.proj (R:=K) i.val).comp U.subtype
  have inj:Function.Injective L:=by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro v hv
    obtain ⟨⟨bw,tw⟩,_⟩:=jointWithOrigin_iff.mp v.property
    have z:L v=0:=hv
    apply (Submodule.mem_bot K).mpr
    apply Subtype.ext
    ext i
    by_cases h:i∈N
    · exact congrFun z ⟨i,h⟩
    by_cases wb:b i=0
    · have nt:tau A b i≠0:=fun t=>h ((Finset.mem_filter.mpr ⟨Finset.mem_univ _,wb,t⟩))
      exact (mul_eq_zero.mp (congrFun tw i)).resolve_left nt
    · exact (mul_eq_zero.mp (congrFun bw i)).resolve_left wb
  have cap:finrank K U≤N.card:=by simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using LinearMap.finrank_le_finrank_of_injective inj
  have d1:Disjoint (cleanActive A b) N:=Finset.disjoint_left.mpr fun i hi hn=>(mem_cleanActive i|>.mp hi).1 (Finset.mem_filter.mp hn).2.1
  have d2:Disjoint (cleanActive A b ∪ N) D:=by
    apply Finset.disjoint_left.mpr
    intro i hi hd
    have nt:tau A b i≠0:=(Finset.mem_filter.mp hd).2
    rcases Finset.mem_union.mp hi with h|h
    · exact nt ((mem_cleanActive i).mp h).2
    · exact nt (Finset.mem_filter.mp h).2.2
  have total:=Finset.card_le_card (Finset.subset_univ (cleanActive A b∪N∪D))
  rw [Finset.card_union_of_disjoint d2,Finset.card_union_of_disjoint d1,Finset.card_univ,Fintype.card_fin] at total
  change (cleanActive A b).card+finrank K U+D.card≤s+1
  omega

def cleanSites (A:Fin (s+1)→Fin (s+1)→K) (b:Vec K (s+1)):Finset K:=(cleanActive A b).image (mirror A)

theorem mem_cleanSites (i:Fin (s+1)) (bi:b i≠0) (ti:tau A b i=0):mirror A i∈cleanSites A b:=
  Finset.mem_image_of_mem _ ((mem_cleanActive i).mpr ⟨bi,ti⟩)

theorem twenty_clean_budget [CharZero K] (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b 20) (size:s+1=28):
    (cleanSites A b).card+finrank K (jointWithOrigin A b 0)≤10:=by
  obtain ⟨h,_,_⟩:=twenty_origin ha ho size
  have big:=twenty_dirty_eighteen ha ho (twenty_paid_reverse ha ho size h) h.words
  have cap:=clean_active_plus_joint (A:=A) (b:=b) 0
  have small:(cleanSites A b).card≤(cleanActive A b).card:=Finset.card_image_le
  omega
end
end RKCert.Paired.Terminal
