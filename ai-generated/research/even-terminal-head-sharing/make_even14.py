"""Render the terminal witness source using the already certified order-12 proof shape."""
from pathlib import Path
import re
b=Path(__file__).resolve().parent
s=(b/'ProofEven12.lean').read_text()
s=s.replace('public import Seed10Even','public import ProofEvenPrep12\nimport all ProofEvenPrep12')
s=s.replace('public import RKCert.ReviewedNative.CausalStageMerge','public import RKCert.ReviewedNative.CausalCopyLocal')
s=s.replace('EvenTerminal12','EvenTerminal14').replace('Even12Data','Even14Data')
for a,q in {'A':'A','b':'b','clocks':'c','order':'order'}.items():
    s=s.replace('StrictSDIRKGram22Order10.'+a,'EvenPrep12.'+q)
for a,q in {'donor_pure':'pure_head','donor_clock':'head_clock','donorTime':'headTime','clocks_eq':'clocks_eq','donor':'headIndex'}.items():
    s=s.replace('Seed10Even.'+a,'EvenPrep12.'+q)
s=s.replace('(-3:ℚ)^k.val','EvenPrep12.headTime 0 ^ k.val')
s=s.replace('    have hval : EvenPrep12.headTime 0 = (-3:ℚ) := by decide +kernel\n    rw [hc,hval] at hd','    rw [hc] at hd')
s=s.replace('[Matrix.mulVec, observations, observed','[Matrix.mulVec, observed')
nums={5:6,6:7,7:8,11:13,12:14,13:15,22:31,28:38,33:44}
s=re.sub(r'(?<![\w])(?:5|6|7|11|12|13|22|28|33)(?![\w])',lambda m:str(nums[int(m[0])]),s)
a=s.index('private theorem virt_eq');j=s.index('\ndef A :=',a)
s=s[:a]+'''private theorem new_lower : Btail.IsLowerTriangular := by
  change ∀ ⦃i j : Fin 13⦄, i < j → Btail i j = 0
  intro i j h
  have hh := of_decide_eq_true (check2 (fun (i j : Fin 13) => decide (j ≤ i ∨ Btail i j = 0))
    (by decide +kernel) i j)
  exact hh.resolve_left (not_le_of_gt h)
private theorem new_diagonal (i : Fin 13) : Btail i i = γ :=
  of_decide_eq_true (check1 (fun i : Fin 13 => decide (Btail i i = γ)) (by decide +kernel) i)
private theorem virt_eq : Av=Sv+Matrix.diagonal (fun _ => γ) :=
  strict_diag_reassembly Av γ
    (chronological_lower (U := Utail) (EvenPrep12.physical 12).1 new_lower)
    (chronological_diagonal (U := Utail) γ (EvenPrep12.physical 12).2.1 new_diagonal)
abbrev redirect : Fin 44 → Fin 38 := redirectHead (fresh := 7) EvenPrep12.headIndex
abbrev keep : Fin 38 → Fin 44 := keepHead 31 6 7

theorem copies (i j : Fin 44) : Sv i j = Sv (keep (redirect i)) j := by
  apply eq_of_actual_copies (fresh := 7) EvenPrep12.headIndex Sv _ i j
  intro k l
  exact of_decide_eq_true (check2 (fun (k : Fin 6) (l : Fin 44) => decide
    (Sv (copyIndex 31 7 k) l = Sv (keep (donorLift 7 (EvenPrep12.headIndex k))) l))
    (by decide +kernel) k l)
'''+s[j:]
(b/'ProofEven14.lean').write_text(s)
