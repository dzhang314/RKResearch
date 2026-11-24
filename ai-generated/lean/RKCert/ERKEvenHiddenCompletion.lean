module
public import RKCert.ERKEvenHiddenCarrier
public import RKCert.GradeSeparation
public import RKCert.NodeCompletion

@[expose] public section
/-! # The ambient invisible coordinate carrier is an actual pure subspace -/
namespace RKCert.Paired.ERKEvenHidden
open RKCert.Paired
open Polynomial Module
variable {K:Type*} [Field K] {s p q:ℕ}
variable {A:Fin (s+1)→Fin (s+1)→K} {b d:Vec K (s+1)} {t:Fin (s+1)}

theorem pure_of_anchored_zero_moments (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hm:2*q≤p) (hq:q+1≤p) {v:Vec K (s+1)} (hv:v∈treeSpace A q) (org:v 0=0)
    (Z:∀k<q,probe A b k v=0) : v∈zeroSpace A q := by
  obtain ⟨a,pure⟩:=exists_poly_zeroSpace ho hq hv
  have first:=origin_zeroSpace A ha q pure
  change v 0-polyEval A q a 0=0 at first
  rw [org,polyEval_first ha,zero_sub,neg_eq_zero] at first
  have he (i:Fin q) : (∑ j:Fin q,a j.succ/((i.val+j.val+2:ℕ):K))=0 := by
    have z:=probe_zeroSpace ho (k:=i.val) (by omega) pure
    change probe A b i.val (v-polyEval A q a)=0 at z
    rw [map_sub,Z _ i.isLt,zero_sub,neg_eq_zero,probe_polyEval ho (by omega),
      Fin.sum_univ_succ,first,zero_div,zero_add] at z
    simpa only [Fin.val_succ,Nat.add_assoc] using z
  have z:=moments_detect ho (d:=2) (by decide) (by omega) (fun i j=>by omega)
    (fun j:Fin q=>a j.succ) he
  have a0:a=0:=by ext j;exact Fin.cases first z j
  simpa only [a0,map_zero,sub_zero] using pure

theorem carrier_probe_zero {v:Vec K (s+1)} (ct:nodes A t=1)
    (hv:v∈carrier (nodes A) b d 0 t) (k:ℕ) : probe A b k v=0 := by
  have eq : probe A b k v=row b v := by
    simp only [probe,row_apply]
    apply Finset.sum_congr rfl
    intro i _
    by_cases z:b i*v i=0
    · rcases mul_eq_zero.mp z with z|z <;> simp [z]
    · have e:=carrier_mirror_weight_zero ct hv i
      have mz:(1-nodes A i)*(b i*v i)=0 := by linear_combination e
      have ci:nodes A i=1:=(sub_eq_zero.mp ((mul_eq_zero.mp mz).resolve_right z)).symm
      simp [ci]
  exact eq.trans (mem_ambientHidden.mp hv).2

/-- This completion needs neither ordered positivity nor any outside
description of the hidden mask. The anchored shifted Hilbert square suffices. -/
theorem carrier_le_defects_even (ha:StrictLower A) (ho:HasTreeOrderAtLeast A b p)
    (hm:2*q≤p) (hq:q+1≤p) (tn:t≠0) (ct:nodes A t=1) (dt:d t=0)
    (supported:∀w∈annih (treeSpace A q),∀i,d i=0→w i=0) :
    carrier (nodes A) b d 0 t≤zeroSpace A q := by
  intro v hv
  have org:v 0=0:=(mem_ambientHidden.mp hv).1 0
    (fun e=>((mem_blindRows 0).mp e).1 rfl) (Ne.symm tn)
  apply pure_of_anchored_zero_moments ha ho hm hq ?_ org (fun k _=>carrier_probe_zero ct hv k)
  apply row_annih_test
  intro w hw
  rw [row_apply]
  apply Finset.sum_eq_zero
  intro i _
  by_cases e:d i=0
  · rw [supported w hw i e,zero_mul]
  · rw [carrier_zero_on_active dt hv e,mul_zero]

/-- If the true midpoint defects are terminal-zero, no hidden interior
coordinate can carry a signed output weight. Its unit basis column is then a
genuine ordinary pure defect. -/
theorem carrier_basis_of_terminal_zero (bt:b t≠0)
    (pay:carrier (nodes A) b d 0 t≤zeroSpace A q)
    (terminalZero:∀v∈zeroSpace A q,v t=0) {i:Fin (s+1)}
    (hi:i∈blindRows (nodes A) b d 0 t) :
    b i=0 ∧ (Pi.single i (1:K):Vec K (s+1))∈zeroSpace A q := by
  classical
  let v:Vec K (s+1):=Pi.single i 1-(b i/b t)•Pi.single t 1
  have hv:v∈carrier (nodes A) b d 0 t := by
    apply mem_ambientHidden.mpr
    refine ⟨fun j hj ht=>?_,?_⟩
    · have ji:j≠i:=fun eq=>hj (eq ▸ hi)
      simp [v,Pi.single_eq_of_ne ji,Pi.single_eq_of_ne ht]
    · rw [show v=Pi.single i 1-(b i/b t)•Pi.single t 1 from rfl,map_sub,map_smul,smul_eq_mul]
      simp [row_apply,Pi.single_apply,div_mul_cancel₀ _ bt]
  have vt:=terminalZero v (pay hv)
  have ti:t≠i:=Ne.symm ((mem_blindRows i).mp hi).2.1
  have bi:b i=0:=by
    change (Pi.single i 1-(b i/b t)•Pi.single t 1:Vec K (s+1)) t=0 at vt
    simp [Pi.single_eq_of_ne ti,div_eq_zero_iff,bt] at vt
    exact vt
  exact ⟨bi,by simpa [v,bi] using pay hv⟩

end RKCert.Paired.ERKEvenHidden
