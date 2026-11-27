"""Specialize the checked even preparation proof shape to the next physical extension."""
from pathlib import Path
import sys,re
P=int(sys.argv[1]);base=Path(sys.argv[2]);out=Path(sys.argv[3]);src=base/'ProofEvenPrep12.lean'
assert P in (14,16,18)
m=P//2;a=m-1;k=P-1;old=P-2;nm=m-2
n,d,N={14:(31,3,41),16:(41,4,52),18:(52,4,65)}[P]
v=n+k;new=k-d;h=m-d
prior=f'EvenPrep{old}'
s=src.read_text()
a0=s.index('def pt');a1=s.index('private theorem Ueq',a0)
s=s[:a0]+'BANK_SECTION\n\n'+s[a1:]
a0=s.index('private theorem FzeroMom');a1=s.index('private theorem top_integrates',a0)
s=s[:a0]+'TOP_BANK\n\n'+s[a1:]
a0=s.index('private theorem virt_eq');a1=s.index('\ndef A :',a0)
s=s[:a0]+'VIRTUAL_SHAPE\n'+s[a1:]
s=s.replace('public import Seed10EvenHigh',f'public import ProofEvenPrep{old}\nimport all ProofEvenPrep{old}')
s=s.replace('public import RKCert.ReviewedNative.FastCausalFold',
'public import RKCert.ReviewedNative.CausalCopyLocal\npublic import RKCert.ReviewedNative.FastCausalFold')
s=s.replace('EvenPrep12Data',f'EvenPrep{P}Data').replace('EvenPrep12\n\nopen',f'EvenPrep{P}\n\nopen').replace('end RKResearch.Certified.EvenPrep12',f'end RKResearch.Certified.EvenPrep{P}')
s=s.replace('StrictSDIRKGram22Order10.',prior+'.').replace('Seed10Even.clocks_eq',prior+'.clocks_eq')
s=s.replace(f'abbrev c0 := {prior}.clocks',f'abbrev c0 := {prior}.c')
s=s.replace('obs_col6','obs_col')
s=s.replace('keepHead 22 2 9','KEEP_HEAD').replace('(fresh := 9)','(fresh := FRESH)')
s=re.sub(r'Fin 3(?![0-9])','Fin HIGHCOUNT',s).replace('⟨3+i.val','⟨COPYCOUNT+i.val')
# All grade and dimension changes in the unchanged proof steps.
nums={5:a,6:m,7:m+1,8:m+2,10:old,11:k,12:P,22:n,31:N,33:v}
s=re.sub(r'(?<![\w])(?:5|6|7|8|10|11|12|22|31|33)(?![\w])',lambda t:str(nums[int(t[0])]),s)
s=s.replace('HIGHCOUNT',str(h)).replace('COPYCOUNT',str(d)).replace('FRESH',str(new)).replace('KEEP_HEAD',f'keepHead {n} {d} {new}')
b=f"""
def donor (i : Fin {d}) : Fin {n} := {prior}.highIndex i

def recPoint : Matrix (Fin 3) (Fin {n}) ℚ :=
  fun j => Pi.single ({prior}.highIndex (j.castLE (by decide))) 1
def recPred : Matrix (Fin {d}) (Fin {n}) ℚ :=
  fun j => A0 (donor j) - Pi.single (donor j) γ

abbrev BankIndex := Fin {nm} ⊕ (Fin 3 ⊕ Fin {d})

def bank : Matrix BankIndex (Fin {n}) ℚ :=
  combineRows (momentRows {nm} b0 c0) (combineRows recPoint recPred)
def respMom : Matrix (Fin {nm}) (Fin {m+1}) ℚ :=
  fun i k => 1 / ((i.val+k.val+1 : ℕ) : ℚ)
def respPoint : Matrix (Fin 3) (Fin {m+1}) ℚ :=
  fun i k => {prior}.highTime (i.castLE (by decide))^k.val
def respPred : Matrix (Fin {d}) (Fin {m+1}) ℚ := fun i k =>
  {prior}.highTime i^(k.val+1)/((k.val+1 : ℕ):ℚ) - γ*{prior}.highTime i^k.val
def resp : Matrix BankIndex (Fin {m+1}) ℚ :=
  combineRows respMom (combineRows respPoint respPred)
def F : Matrix (Fin {k}) BankIndex ℚ :=
  fun i j => feedMap i (finSumFinEquiv (Sum.map id finSumFinEquiv j))

private theorem obsMom (i : Fin {nm}) (t : FiniteRootedTree) (hs : (t.order : ℕ) ≤ {m+1}) :
    momentRows {nm} b0 c0 i ⬝ᵥ normalized A0 t =
      respMom i ⟨(t.order : ℕ)-1, by have := t.order.pos; omega⟩ := by
  have ht := t.order.pos
  have h' : i.val+((t.order : ℕ)-1)+1 = (t.order : ℕ)+i.val := by omega
  have h : (t.order : ℕ)+i.val ≤ {old} := by have := i.isLt; omega
  have hc : clocks A0 = c0 := {prior}.clocks_eq
  change read b0 c0 i.val (normalized A0 t) = _
  rw [← hc, read_eq_moment, moment {prior}.order t i.val h]
  simp only [respMom,h']

private theorem obsPt (i : Fin 3) (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ {m+1}) :
    recPoint i ⬝ᵥ normalized A0 t =
      respPoint i ⟨(t.order : ℕ)-1, by omega⟩ := by
  have hh := {prior}.pure_high (i.castLE (by decide : 3 ≤ {d})) t h
  rw [{prior}.high_clock] at hh
  simpa only [recPoint,respPoint,single_dotProduct,one_mul] using hh

private theorem obsPred (i : Fin {d}) (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ {m}) :
    recPred i ⬝ᵥ normalized A0 t =
      respPred i ⟨(t.order : ℕ)-1, by omega⟩ := by
  have hh := pure_predecessor (donor i) ({prior}.pure_high i) γ t h
  rw [show donor i = {prior}.highIndex i by rfl, {prior}.high_clock] at hh
  have e : (t.order : ℕ)-1+1 = (t.order : ℕ) := by have := t.order.pos; omega
  simpa only [recPred,respPred,donor,e] using hh

private theorem obs_col (t : FiniteRootedTree) (h : (t.order : ℕ) ≤ {m}) :
    bank *ᵥ normalized A0 t = resp.col ⟨(t.order : ℕ)-1, by omega⟩ := by
  funext i
  cases i with
  | inl j => exact obsMom j t (by omega)
  | inr idx =>
    cases idx with
    | inl j => exact obsPt j t (by omega)
    | inr j => exact obsPred j t h
"""
s=s.replace('BANK_SECTION',b.strip())
b=f"""
private theorem new_lower : Btail.IsLowerTriangular := by
  change ∀ ⦃i j : Fin {k}⦄, i < j → Btail i j = 0
  intro i j z
  have hh := of_decide_eq_true (check2 (fun (i j : Fin {k}) => decide (j ≤ i ∨ Btail i j = 0))
    (by decide +kernel) i j)
  exact hh.resolve_left (not_le_of_gt z)
private theorem new_diagonal (i : Fin {k}) : Btail i i = γ :=
  of_decide_eq_true (check1 (fun i : Fin {k} => decide (Btail i i = γ)) (by decide +kernel) i)
private theorem virt_eq : Av=Sv+Matrix.diagonal (fun _ => γ) :=
  strict_diag_reassembly Av γ
    (chronological_lower (U := Utail) ({prior}.physical {old}).1 new_lower)
    (chronological_diagonal (U := Utail) γ ({prior}.physical {old}).2.1 new_diagonal)
abbrev redirect : Fin {v} → Fin {N} := redirectHead (fresh := {new}) donor
abbrev keep : Fin {N} → Fin {v} := keepHead {n} {d} {new}

theorem copies (i j : Fin {v}) : Sv i j = Sv (keep (redirect i)) j := by
  apply eq_of_actual_copies (fresh := {new}) donor Sv _ i j
  intro kk ll
  exact of_decide_eq_true (check2 (fun (i : Fin {d}) (j : Fin {v}) => decide
    (Sv (copyIndex {n} {new} i) j = Sv (keep (donorLift {new} (donor i))) j))
    (by decide +kernel) kk ll)
"""
s=s.replace('VIRTUAL_SHAPE',b.strip())
b=f"""
private theorem FzeroPred (i : Fin {h}) (j : Fin {d}) :
    F (highVirtual i) (Sum.inr (Sum.inr j)) = 0 :=
  of_decide_eq_true (check2 (fun (i : Fin {h}) (j : Fin {d}) => decide
    (F (highVirtual i) (Sum.inr (Sum.inr j)) = 0)) (by decide +kernel) i j)

private theorem top_bank (i : Fin {h}) (t : FiniteRootedTree) (ht : (t.order : ℕ) ≤ {m+1}) :
    (Utail *ᵥ normalized A0 t) (highVirtual i) =
      (F*resp) (highVirtual i) ⟨(t.order : ℕ)-1,by omega⟩ := by
  rw [Ueq, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  cases j with
  | inl j =>
    have hh := obsMom j t ht
    change F (highVirtual i) (Sum.inl j) * (momentRows {nm} b0 c0 j ⬝ᵥ normalized A0 t) =
      F (highVirtual i) (Sum.inl j) * respMom j ⟨(t.order : ℕ)-1,by omega⟩
    rw [hh]
  | inr k =>
    cases k with
    | inl j =>
      have hh := obsPt j t ht
      change F (highVirtual i) (Sum.inr (Sum.inl j)) * (recPoint j ⬝ᵥ normalized A0 t) =
        F (highVirtual i) (Sum.inr (Sum.inl j)) * respPoint j ⟨(t.order : ℕ)-1,by omega⟩
      rw [hh]
    | inr j => simp [FzeroPred]
"""
s=s.replace('TOP_BANK',b.strip())
(out/f'ProofEvenPrep{P}.lean').write_text(s)
