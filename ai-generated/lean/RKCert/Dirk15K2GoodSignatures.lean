module

public import RKCert.Dirk15K2JointCount

@[expose] public section

/-! # Seventeen retained joint signatures and no discarded active pivot -/
namespace RKCert.Paired
open Module Polynomial RKCert.Endpoint
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b v : Vec K 20}

namespace Order15K2Head
variable (h : Order15K2Head A b v) (D : h.head.DeletedPencil)

def goodRows (R : K[X]) : Finset (Fin 20) :=
  (retainedNonghostPositions A b).filter (fun i =>
    D.D.eval (nodes A i)=v i*R.eval (nodes A i))

def goodSignatures (R : K[X]) : Finset (K×K) :=
  (h.goodRows D R).image (fun i => (nodes A i,v i))

set_option maxHeartbeats 2700000 in
theorem actual_good_signatures (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (H : Order15MinimalMarkedChart A b) :
    ∃ R : K[X],R.natDegree≤4 ∧ 17≤(h.goodSignatures D R).card ∧
      ∀ i : Fin 20,i≠Fin.last 19 → nodes A i≠1 → b i≠0 →
        D.D.eval (nodes A i)=v i*R.eval (nodes A i) := by
  obtain ⟨R,rd,z,hz,eq⟩ := h.residual_pencil_difference D
  let c := nodes A
  let I := retainedNonghostPositions A b
  let pair : Fin 20→K×K := fun i=>(c i,v i)
  let S := h.goodSignatures D R
  let V := h.residual
  have sz : ∀ i∈I,z i=0 → i∈h.goodRows D R := by
    intro i hi p
    apply Finset.mem_filter.mpr
    exact ⟨hi,sub_eq_zero.mp ((eq i hi).trans p)⟩
  have active (i : Fin 20) (nt : i≠Fin.last 19) (bi : b i≠0) : i∈I :=
    mem_retainedNonghostPositions.mpr ⟨nt,fun x => bi (mem_ghostPositions.mp x).2.1⟩
  have ret := retainedNonghostPositions_card H.terminal.weight_ne (A:=A)
  change I.card=19-finrank K (simultaneousGhosts A b) at ret
  have rs := h.rank_split H
  change finrank K (simultaneousGhosts A b)+finrank K V=2 ∧ finrank K V≤1 at rs
  have count_inj {X : Finset (Fin 20)} (p : X⊆h.goodRows D R)
      (q : Set.InjOn pair (X:Set (Fin 20))) : X.card≤S.card := by
    have e := Finset.card_le_card (Finset.image_subset_image p : X.image pair⊆S)
    rwa [Finset.card_image_of_injOn q] at e
  have only_one {X : Finset (Fin 20)} {a t : K}
      (span : X⊆h.jointBlock a t) (hz : ∀ z∈V,∀ i∈h.jointBlock a t,z i=0) : X.card≤1 :=
    (Finset.card_le_card span).trans ((h.joint_block_counts ha ho H a t).2.1 hz)
  refine ⟨R,rd,?_,?_⟩
  · change 17≤S.card
    by_cases empty : V=⊥
    · have all (x : Vec K 20) (hx : x∈V) (i : Fin 20) : x i=0 := by
        rw [empty,Submodule.mem_bot] at hx
        rw [hx,Pi.zero_apply]
      have inc : I⊆h.goodRows D R := fun i hi => sz i hi (all z hz i)
      have inj : Set.InjOn pair (I:Set (Fin 20)) := by
        intro i ia j ja same
        have nc : c j=c i := (congrArg Prod.fst same).symm
        have vc : v j=v i := (congrArg Prod.snd same).symm
        have A := (h.joint_block_counts ha ho H (c i) (v i)).2.1
          (fun u hu k _ => all u hu k)
        exact Finset.card_le_one_iff.mp A
          (h.mem_jointBlock.mpr ⟨ia,rfl,rfl⟩) (h.mem_jointBlock.mpr ⟨ja,nc,vc⟩)
      have d := count_inj inc inj
      rw [empty,finrank_bot,add_zero] at rs
      omega
    · obtain ⟨x,hx,xn,sp,a,t,region⟩ := h.one_joint_line D ha ho H empty
      let B := h.jointBlock a t
      let Outside := I \ B
      have Bd : B⊆I := fun i hi => (h.mem_jointBlock.mp hi).1
      have onBlock {u : Vec K 20} (hu : u∈V) {i : Fin 20} (le : u i≠0) : c i=a ∧ v i=t := by
        change V=K∙x at sp
        rw [sp] at hu
        obtain ⟨q,rfl⟩ := Submodule.mem_span_singleton.mp hu
        exact region i (fun e => le (by simp [e]))
      have out : Outside⊆h.goodRows D R := by
        intro i hi
        obtain ⟨m,notM⟩ := Finset.mem_sdiff.mp hi
        apply sz i m
        by_contra e
        exact notM (h.mem_jointBlock.mpr ⟨m,onBlock hz e⟩)
      have inj : Set.InjOn pair (Outside:Set (Fin 20)) := by
        intro i hi j hj same
        have ⟨im,notI⟩ := Finset.mem_sdiff.mp hi
        have ⟨jm,notJ⟩ := Finset.mem_sdiff.mp hj
        have zi : ∀ u∈V,∀ k∈h.jointBlock (c i) (v i),u k=0 := by
          intro u hu k km
          by_contra nz
          have ⟨hca,hvt⟩ := onBlock hu nz
          have ⟨_,ce,ve⟩ := h.mem_jointBlock.mp km
          exact notI (h.mem_jointBlock.mpr ⟨im,ce.symm.trans hca,ve.symm.trans hvt⟩)
        have cap := (h.joint_block_counts ha ho H (c i) (v i)).2.1 zi
        exact Finset.card_le_one_iff.mp cap (h.mem_jointBlock.mpr ⟨im,rfl,rfl⟩)
          (h.mem_jointBlock.mpr ⟨jm,(congrArg Prod.fst same).symm,(congrArg Prod.snd same).symm⟩)
      have v1 : finrank K V=1 := by
        have n : finrank K V≠0 := fun e => empty (Submodule.finrank_eq_zero.mp e)
        exact le_antisymm rs.2 (Nat.pos_of_ne_zero n)
      have cardI : I.card=18 := by have e := rs.1; omega
      have oCard : Outside.card=18-B.card := by
        change (I\B).card=18-B.card
        rw [Finset.card_sdiff_of_subset Bd,cardI]
      have c0 := count_inj out inj
      by_cases bad : ∃ i∈I,z i≠0
      · obtain ⟨i,ii,inZ⟩ := bad
        have ⟨ia,it⟩ := onBlock hz inZ
        have zi : z i=D.D.eval a-t*R.eval a := by
          have p := eq i ii
          change nodes A i=a at ia
          rwa [ia,it,eq_comm] at p
        have b1 : B.card≤1 := (h.joint_block_counts ha ho H a t).2.2
          ⟨z,hz,z i,inZ,fun k km => by
            have ⟨kI,ka,kt⟩ := h.mem_jointBlock.mp km
            have p := eq k kI
            rw [ka,kt,←zi] at p
            exact p.symm⟩
        omega
      · have all (i : Fin 20) (hi : i∈I) : i∈h.goodRows D R :=
          sz i hi (by_contra (fun e => bad ⟨i,hi,e⟩))
        by_cases e0 : B.Nonempty
        · obtain ⟨i,im⟩ := e0
          have b2 : B.card≤2 := (h.joint_block_counts ha ho H a t).1
          have pnt : (a,t)∉Outside.image pair := by
            intro m
            obtain ⟨j,jm,je⟩ := Finset.mem_image.mp m
            have ⟨jr,jb⟩ := Finset.mem_sdiff.mp jm
            exact jb (h.mem_jointBlock.mpr ⟨jr,congrArg Prod.fst je,congrArg Prod.snd je⟩)
          have isSig : insert (a,t) (Outside.image pair)⊆S := by
            apply Finset.insert_subset_iff.mpr
            have ⟨ir,ic,iv⟩ := h.mem_jointBlock.mp im
            refine ⟨Finset.mem_image.mpr ⟨i,all i ir,Prod.ext ic iv⟩,
              Finset.image_subset_image out⟩
          have rb := Finset.card_le_card isSig
          rw [Finset.card_insert_of_notMem pnt,Finset.card_image_of_injOn inj] at rb
          omega
        · have b0 : B.card=0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp e0)
          omega
  · intro i it c1 bi
    have ir : i∈I := active i it bi
    apply sub_eq_zero.mp
    rw [eq i ir]
    by_contra zi
    have rne : V≠⊥ := by
      intro e
      have z0 : z∈V := hz
      rw [e,Submodule.mem_bot] at z0
      exact zi (by rw [z0,Pi.zero_apply])
    obtain ⟨x,hx,xn,span,a,t,region⟩ := h.one_joint_line D ha ho H rne
    have onBlock {j : Fin 20} (e : z j≠0) : c j=a ∧ v j=t := by
      have hx' : z∈K∙x := span ▸ hz
      obtain ⟨q,e'⟩ := Submodule.mem_span_singleton.mp hx'
      exact region j (fun xx => e (by rw [←e',Pi.smul_apply,xx,smul_zero]))
    have ⟨ia,iv⟩ := onBlock zi
    have ae : a≠1 := fun e => c1 (ia.trans e)
    let B := h.jointBlock a t
    have im : i∈B := h.mem_jointBlock.mpr ⟨ir,ia,iv⟩
    have ziEq : z i=D.D.eval a-t*R.eval a := by
      have p := eq i ir
      change nodes A i=a at ia
      rwa [ia,iv,eq_comm] at p
    have b1 : B.card≤1 := (h.joint_block_counts ha ho H a t).2.2
      ⟨z,hz,z i,zi,fun k km => by
        have ⟨ki,ka,kt⟩ := h.mem_jointBlock.mp km
        have e := eq k ki
        rw [ka,kt,←ziEq] at e
        exact e.symm⟩
    have support (j : Fin 20) (jn : j≠i) : z j=0 := by
      by_contra jz
      have ⟨ja,jv⟩ := onBlock jz
      have jt : j≠Fin.last 19 := fun e => ae (ja.symm.trans (e ▸ H.terminal.node_one))
      have jg : j∉ghostPositions A b := fun e => jz (mem_noGhostEntries.mp hz.2 j e)
      have jm : j∈B := h.mem_jointBlock.mpr ⟨mem_retainedNonghostPositions.mpr ⟨jt,jg⟩,ja,jv⟩
      exact jn (Finset.card_le_one_iff.mp b1 jm im)
    have hp : probe A b 0 z=0 := probe_zeroSpace ho (by decide : 0+7+1≤15) (h.head.maximal.1 hz.1)
    change row (fun j => b j*(nodes A j)^0) z=0 at hp
    rw [row_apply,Finset.sum_eq_single i] at hp
    · exact (mul_ne_zero bi zi) (by simpa only [pow_zero,mul_one] using hp)
    · intro j _ jn; rw [support j jn,mul_zero]
    · simp

end Order15K2Head
end
end RKCert.Paired
