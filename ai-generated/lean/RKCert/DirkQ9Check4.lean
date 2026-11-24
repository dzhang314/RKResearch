module
public import RKCert.DirkQuinticIntegerLists
@[expose] public section
namespace RKCert.DirkQuintic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem h0 : sortedPair 10709 integers9 5525 0=true :=by decide +kernel
private theorem h1 : sortedPair 10709 integers9 5525 1103=true :=by decide +kernel
private theorem h2 : sortedPair 10709 integers9 5525 3759=true :=by decide +kernel
private theorem h3 : sortedPair 10709 integers9 5525 4862=true :=by decide +kernel
private theorem h4 : sortedPair 10709 integers9 5525 5525=true :=by decide +kernel
private theorem h5 : sortedPair 10709 integers9 5525 7562=true :=by decide +kernel
private theorem h6 : sortedPair 10709 integers9 5525 7742=true :=by decide +kernel
private theorem h7 : sortedPair 10709 integers9 5525 7829=true :=by decide +kernel
private theorem h8 : sortedPair 10709 integers9 5525 8009=true :=by decide +kernel
private theorem h9 : sortedPair 10709 integers9 5525 10046=true :=by decide +kernel

theorem checkInt9_4 : integers9.all (fun b=>sortedPair 10709 integers9 5525 b)=true := by
  apply List.all_eq_true.mpr
  intro b hb
  simp only [integers9,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
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
end RKCert.DirkQuintic

