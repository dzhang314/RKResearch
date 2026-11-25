module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorStripRowCheck

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

def rawStripRect (p : StripRowPacket) : DyadicRect := p.row.rect

def closedSliceOfPackets (lo hi : ℕ) (P : List StripRowPacket) : GridSlice :=
  ⟨lo,hi,P.map (fun p => (rawStripRect p).normalize 8 6)⟩

/-- A small local vertical replay needs no repeated lookup through the
whole corpus. Membership in the original corpus is separately supplied
from the addressed packet witnesses. -/
theorem sliceCheck_of_self_and_members {s : GridSlice} {R : List GridRect}
    (localCheck : checkSlice s.vertical 64 s = true)
    (globalMembers : ∀ x ∈ s.vertical, x ∈ R) :
    checkSlice R 64 s = true := by
  unfold checkSlice at localCheck ⊢
  obtain ⟨span,chain⟩ := Bool.and_eq_true_iff.mp localCheck
  refine Bool.and_eq_true_iff.mpr ⟨?_,chain⟩
  apply List.all_eq_true.mpr
  intro x hx
  have good : x ∈ s.vertical ∧ x.xLo ≤ s.xLo ∧ s.xHi ≤ x.xHi :=
    of_decide_eq_true (List.all_eq_true.mp span x hx)
  exact decide_eq_true ⟨globalMembers x hx,good.2⟩

theorem sliceCheck_of_packets {P Q : List StripRowPacket} {a b : ℕ}
    (localCheck : checkSlice (closedSliceOfPackets a b P).vertical 64
      (closedSliceOfPackets a b P) = true)
    (mem : ∀ p ∈ P, p ∈ Q) :
    checkSlice ((Q.map rawStripRect).map (DyadicRect.normalize 8 6)) 64
      (closedSliceOfPackets a b P) = true := by
  apply sliceCheck_of_self_and_members localCheck
  intro x hx
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨rawStripRect p,List.mem_map.mpr ⟨p,mem p hp,rfl⟩,rfl⟩

theorem packet_mem_of_chunk {P : List (List StripRowPacket)}
    {chunk : List StripRowPacket} {p : StripRowPacket}
    (hc : chunk ∈ P) (hp : p ∈ chunk) : p ∈ P.flatten :=
  List.mem_flatten.mpr ⟨chunk,hc,hp⟩

theorem flatten_all_of_groups {α : Type*} (f : α → Bool) {P : List (List α)}
    (h : P.all (fun p => p.all f) = true) : P.flatten.all f = true := by
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨p,hp,hm⟩ := List.mem_flatten.mp ha
  exact List.all_eq_true.mp (List.all_eq_true.mp h p hp) a hm

end RKCert.ReviewedNative.ThreeInteriorPencil
