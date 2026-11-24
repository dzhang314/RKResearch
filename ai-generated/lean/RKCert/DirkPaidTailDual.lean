module
public import RKCert.DirkEvenDual
public import RKCert.DirkMarkedBudget
@[expose] public section
namespace RKCert.Paired
open Module
variable {K:Type*} [Field K] {s m q r p:ℕ} {A:Fin s→Fin s→K} {b:Vec K s}

/-- For an actual zero first row, a single anchored moment also earns
the last degree inside a later pure grade, not merely on the midpoint. -/
theorem poly_separated_delayed_first {A:Fin (s+1)→Fin (s+1)→K} {b:Vec K (s+1)}
    (origin:∀j,A 0 j=0) (ho:HasTreeOrderAtLeast A b p) (low:q≤m) (pay:q+m≤p)
    (a:Fin (q+1)→K) (mem:polyEval A q a∈zeroSpace A m):a=0:=by
  have f:polyEval A q a 0=0:=zeroSpace_first_of_row origin m mem
  have az: a 0=0:=(polyEval_first_of_row origin q a).symm.trans f
  have ker (i:Fin q): (∑j:Fin q, a j.succ / ((i.val+j.val+2:ℕ):K))=0:=by
    have mom:probe A b i.val (polyEval A q a)=0:=probe_zeroSpace ho (by omega:i.val+m+1≤p) mem
    rw [probe_polyEval ho (by omega),Fin.sum_univ_succ,az,zero_div,zero_add] at mom
    simpa only [Fin.val_succ,Nat.add_assoc] using mom
  have z:=moments_detect ho (d:=2) (by decide) (by omega) (fun i j=>by omega) (fun j:Fin q=>a j.succ) ker
  ext j;exact Fin.cases az z j

/-- If a separated short scalar block attains the whole grade's rank, it
spans together with the genuine pure space. -/
theorem poly_pure_full_of_paid_rank (low:q≤m)
    (sep:∀a,polyEval A q a∈zeroSpace A m→a=0)
    (pay:finrank K (treeSpace A m)≤q+1+finrank K (zeroSpace A m)) :
    treeSpace A m=LinearMap.range (polyEval A q) ⊔ zeroSpace A m:=by
  let F:=zeroSpace A m
  let V:=LinearMap.range (polyEval A q)
  have R:finrank K V=q+1:=by
    have inj:Function.Injective (polyEval A q):=(injective_iff_map_eq_zero _).mpr
      (fun a ha=>sep a (ha ▸ F.zero_mem))
    simpa [V] using LinearMap.finrank_range_of_inj inj
  have d:Disjoint V F:=by
    rw [Submodule.disjoint_def]
    rintro _ ⟨a,rfl⟩ h
    rw [sep a h,map_zero]
  have ranks:=V.finrank_sup_add_finrank_inf_eq F
  rw [d.eq_bot,finrank_bot,add_zero,R] at ranks
  symm
  exact Submodule.eq_of_le_of_finrank_le (sup_le (by rintro _ ⟨a,rfl⟩;exact treeSpace_mono A low (polyEval_mem_treeSpace A q a)) (zeroSpace_le_treeSpace A m))
    (by change finrank K (treeSpace A m)≤finrank K (V ⊔ F : Submodule K (Vec K s));change finrank K (treeSpace A m)≤q+1+finrank K F at pay;omega)

namespace Terminal
/-- The actual paid tree/backward-word saturation from any known starting
rank and matching physical budget. No midpoint, end node, or true last
output assumption is needed. -/
theorem paid_tail_duality (ha:LowerArray A) (ho:HasTreeOrderAtLeast A b p)
    {m d r₀:ℕ} (start:d≤finrank K (treeSpace A m)) (stages:s=d+r₀) (paid:m+r₀+3=p)
    {q r:ℕ} (low:m≤q) (hpay:q+r+3=p) :
    finrank K (treeSpace A q)=d+(q-m) ∧ finrank K (dirkBack A b r)=r ∧
    dirkBack A b r=annih (treeSpace A q) ∧ treeSpace A q=annih (dirkBack A b r) :=by
  have tail:=tree_flag_gain ha ho low (by omega)
  have back:=dirkBack_rank ha ho r (by omega)
  have an:=dirkBack_annih ho q r (by omega)
  have prod:=finrank_annih_le an
  have flip:=annih_flip_le an
  have ar:=finrank_annih_le (le_refl (annih (treeSpace A q)))
  have ae:=finrank_annih_le (le_refl (annih (dirkBack A b r)))
  exact ⟨by omega,by omega,Submodule.eq_of_le_of_finrank_le an (by omega),
    Submodule.eq_of_le_of_finrank_le flip (by omega)⟩
end Terminal
end RKCert.Paired

