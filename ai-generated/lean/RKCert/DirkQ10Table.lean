module
public import RKCert.DirkQ10Check0
public import RKCert.DirkQ10Check1
public import RKCert.DirkQ10Check2
public import RKCert.DirkQ10Check3
public import RKCert.DirkQ10Check4
public import RKCert.DirkQ10Check5
public import RKCert.DirkQ10Check6
public import RKCert.DirkQ10Check7
public import RKCert.DirkQ10Check8
public import RKCert.DirkQ10Check9
public import RKCert.DirkQ10Check10
@[expose] public section
namespace RKCert.DirkQuintic
theorem checked_int10 : integers10.all (fun a=>integers10.all (fun b=>sortedPair 15727 integers10 a b))=true := by
  apply List.all_eq_true.mpr
  intro a ha
  simp only [integers10,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact checkInt10_0
  · exact checkInt10_1
  · exact checkInt10_2
  · exact checkInt10_3
  · exact checkInt10_4
  · exact checkInt10_5
  · exact checkInt10_6
  · exact checkInt10_7
  · exact checkInt10_8
  · exact checkInt10_9
  · exact checkInt10_10
end RKCert.DirkQuintic

