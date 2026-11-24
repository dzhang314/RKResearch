module
public import RKCert.DirkQ9Check0
public import RKCert.DirkQ9Check1
public import RKCert.DirkQ9Check2
public import RKCert.DirkQ9Check3
public import RKCert.DirkQ9Check4
public import RKCert.DirkQ9Check5
public import RKCert.DirkQ9Check6
public import RKCert.DirkQ9Check7
public import RKCert.DirkQ9Check8
public import RKCert.DirkQ9Check9
@[expose] public section
namespace RKCert.DirkQuintic
theorem checked_int9 : integers9.all (fun a=>integers9.all (fun b=>sortedPair 10709 integers9 a b))=true := by
  apply List.all_eq_true.mpr
  intro a ha
  simp only [integers9,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checkInt9_0
  · exact checkInt9_1
  · exact checkInt9_2
  · exact checkInt9_3
  · exact checkInt9_4
  · exact checkInt9_5
  · exact checkInt9_6
  · exact checkInt9_7
  · exact checkInt9_8
  · exact checkInt9_9
end RKCert.DirkQuintic

