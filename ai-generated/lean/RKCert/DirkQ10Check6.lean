module
public import RKCert.DirkQuinticIntegerLists
@[expose] public section
namespace RKCert.DirkQuintic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem h0 : sortedPair 15727 integers10 8398 0=true :=by decide +kernel
private theorem h1 : sortedPair 15727 integers10 8398 1069=true :=by decide +kernel
private theorem h2 : sortedPair 15727 integers10 8398 1186=true :=by decide +kernel
private theorem h3 : sortedPair 15727 integers10 8398 6796=true :=by decide +kernel
private theorem h4 : sortedPair 15727 integers10 8398 7356=true :=by decide +kernel
private theorem h5 : sortedPair 15727 integers10 8398 7876=true :=by decide +kernel
private theorem h6 : sortedPair 15727 integers10 8398 8398=true :=by decide +kernel
private theorem h7 : sortedPair 15727 integers10 8398 8920=true :=by decide +kernel
private theorem h8 : sortedPair 15727 integers10 8398 9440=true :=by decide +kernel
private theorem h9 : sortedPair 15727 integers10 8398 10000=true :=by decide +kernel
private theorem h10 : sortedPair 15727 integers10 8398 15610=true :=by decide +kernel

theorem checkInt10_6 : integers10.all (fun b=>sortedPair 15727 integers10 8398 b)=true := by
  apply List.all_eq_true.mpr
  intro b hb
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
end RKCert.DirkQuintic

