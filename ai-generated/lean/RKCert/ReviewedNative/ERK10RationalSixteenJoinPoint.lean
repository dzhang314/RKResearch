module

public import RKCert.ReviewedNative.ERK10RationalSixteenCore

@[expose] public section

namespace RKResearch.Certified.ERK10RationalSixteen

def joinPoint (i : Fin Count) (jval : ℕ) : Bool :=
  let j := tag jval
  decide (grade (join i j) = grade i+grade j) &&
    (List.finRange 16).all fun c => decide (V (join i j) c = V i c * W j c)

def joinSlice (i : Fin Count) (start count : ℕ) : Bool :=
  (List.range' start count).all (joinPoint i)

theorem joinOK_eq (i : Fin Count) :
    joinOK i = (List.range (cut (10-grade i))).all (joinPoint i) := rfl

theorem glueJoin {i : Fin Count} {s m n : ℕ}
    (h₀ : joinSlice i s m = true)
    (h₁ : joinSlice i (s+m) n = true) :
    joinSlice i s (m+n) = true := by
  unfold joinSlice at h₀ h₁ ⊢
  simp only [← List.range'_append_1, List.all_append, h₀, h₁, Bool.and_self]

theorem finishJoin {i : Fin Count} {m : ℕ}
    (hm : cut (10-grade i) = m) (h : joinSlice i 0 m = true) :
    joinOK i = true := by
  simpa only [joinOK_eq,hm,List.range_eq_range',joinSlice] using h

end RKResearch.Certified.ERK10RationalSixteen
