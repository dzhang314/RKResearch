module
public import RKCert.ReviewedNative.ERK10StepanovClassCore

@[expose] public section

namespace RKResearch.Certified.ERK10Stepanov

def joinPoint (i : Fin ClassCount) (jval : ℕ) : Bool :=
  let j := ctag jval
  let k := cjoin i j
  decide (cgrade k = cgrade i+cgrade j) &&
    (List.finRange 15).all fun c => decide (cprofile k c = sparseMul (cprofile i c) (caction j c))

def joinSlice (i : Fin ClassCount) (start count : ℕ) : Bool :=
  (List.range' start count).all (joinPoint i)

theorem cJoinOK_eq (i : Fin ClassCount) :
    cJoinOK i = (List.range (classCut (10-cgrade i))).all (joinPoint i) := rfl

theorem glueJoin {i : Fin ClassCount} {s m n : ℕ}
    (h₀ : joinSlice i s m = true)
    (h₁ : joinSlice i (s+m) n = true) :
    joinSlice i s (m+n) = true := by
  unfold joinSlice at h₀ h₁ ⊢
  simp only [← List.range'_append_1, List.all_append, h₀, h₁, Bool.and_self]

theorem finishJoin {i : Fin ClassCount} {m : ℕ}
    (hm : classCut (10-cgrade i) = m) (h : joinSlice i 0 m = true) :
    cJoinOK i = true := by
  simpa only [cJoinOK_eq,hm,List.range_eq_range',joinSlice] using h

end RKResearch.Certified.ERK10Stepanov
