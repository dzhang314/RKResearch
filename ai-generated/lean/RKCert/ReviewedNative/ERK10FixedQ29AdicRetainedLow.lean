module

public import RKCert.ReviewedNative.ERK10FixedQ29AdicRetainedRows

@[expose] public section

namespace RKResearch.Certified.ERK10FixedQ29Adic.Physical
open Nonlinear Polynomial
open scoped Ring BigOperators
noncomputable section
set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R]

def oldT2 : RKCert.Tree := .attach .leaf .leaf
def oldT3Chain : RKCert.Tree := .attach oldT2 .leaf
def oldT3Bush : RKCert.Tree := .attach .leaf oldT2
def oldT4Chain : RKCert.Tree := .attach oldT3Chain .leaf
def oldT4UnaryBush : RKCert.Tree := .attach oldT3Bush .leaf
def oldT4MixL : RKCert.Tree := .attach oldT2 oldT2
def oldT4MixR : RKCert.Tree := .attach .leaf oldT3Chain
def oldT4Bush : RKCert.Tree := .attach .leaf oldT3Bush

theorem tree_order_one (t : RKCert.Tree) (h : t.order=1) : t=.leaf := by
  cases t with
  | leaf => rfl
  | attach u v =>
    have hu:=u.order_pos
    have hv:=v.order_pos
    change u.order+v.order=1 at h
    omega

theorem tree_order_two (t : RKCert.Tree) (h : t.order=2) : t=oldT2 := by
  cases t with
  | leaf => simp [RKCert.Tree.order] at h
  | attach u v =>
    have hu:=u.order_pos
    have hv:=v.order_pos
    change u.order+v.order=2 at h
    rw [tree_order_one u (by omega),tree_order_one v (by omega)]
    rfl

theorem tree_order_three (t : RKCert.Tree) (h : t.order=3) :
    t=oldT3Chain ∨ t=oldT3Bush := by
  cases t with
  | leaf => simp [RKCert.Tree.order] at h
  | attach u v =>
    have hu:=u.order_pos
    have hv:=v.order_pos
    change u.order+v.order=3 at h
    by_cases h1 : u.order=1
    · rw [tree_order_one u h1,tree_order_two v (by omega)]
      exact Or.inr rfl
    · rw [tree_order_two u (by omega),tree_order_one v (by omega)]
      exact Or.inl rfl

theorem tree_order_four (t : RKCert.Tree) (h : t.order=4) :
    t=oldT4Chain ∨ t=oldT4UnaryBush ∨ t=oldT4MixL ∨ t=oldT4MixR ∨ t=oldT4Bush := by
  cases t with
  | leaf => simp [RKCert.Tree.order] at h
  | attach u v =>
    have hu:=u.order_pos
    have hv:=v.order_pos
    change u.order+v.order=4 at h
    by_cases h1 : u.order=1
    · rw [tree_order_one u h1]
      rcases tree_order_three v (by omega) with rfl|rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · by_cases h2 : u.order=2
      · rw [tree_order_two u h2,tree_order_two v (by omega)]
        exact Or.inr (Or.inr (Or.inl rfl))
      · rw [tree_order_one v (by omega)]
        rcases tree_order_three u (by omega) with rfl|rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)

theorem retained_projected_chain4 (p : HostInput R) (ε : R)
    (he : IsUnit ε) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R)) (hs : IsUnit p.s) :
    retainedProj p (retainedAct p ε (retainedAct p ε (retainedClock p ε))) =
      (Ring.inverse (2:R)*Ring.inverse (3:R))*p.q^3-
        p.α*((Ring.inverse (2:R)*Ring.inverse (3:R))*p.s^3) := by
  let i2 := Ring.inverse (2:R)
  let i3 := Ring.inverse (3:R)
  let x := retainedClock p ε
  have hL := retained_linear_primitive p ε he h2 hs
  have hX : retainedAct p ε x =
      (fun i=>i2*(x i)^2)+(fun i=>-(ε^2*i2)*oldBasis 1 i) := by
    change retainedAct p ε (retainedClock p ε)=_
    rw [hL]
    funext i
    simp only [Pi.add_apply]
    unfold x i2
    ring
  rw [hX]
  have hQ := retained_quadratic_primitive p ε he h2 h3 hs
  have hB := retained_basis_drop p ε
  change retainedAct p ε (fun i=>(x i)^2) 3-p.α*retainedAct p ε (fun i=>(x i)^2) 2=
      p.q^3*i3-p.α*(p.s^3*i3) at hQ
  unfold retainedProj at hB ⊢
  simp only [retainedAct_add,retainedAct_scale]
  change _=(i2*i3)*p.q^3-p.α*((i2*i3)*p.s^3)
  linear_combination i2*hQ-(ε^2*i2)*hB

section Physical
variable (c a b : R)

def oldActualClock : Old→R := retainedClock (actualHost c a b) (Ring.inverse (8:R))
def oldActualAct (v : Old→R) : Old→R :=
  retainedAct (actualHost c a b) (Ring.inverse (8:R)) v

theorem retained_leaf : retainedTreeProfile c a b .leaf=1 := rfl

theorem retained_t2 : retainedTreeProfile c a b oldT2=oldActualClock c a b := by
  rw [oldT2,retainedTreeProfile_attach,retained_leaf,mul_one]
  exact retainedAct_one _ _

theorem retained_t3_chain :
    retainedTreeProfile c a b oldT3Chain=oldActualAct c a b (oldActualClock c a b) := by
  rw [oldT3Chain,retainedTreeProfile_attach,retained_t2,retained_leaf,mul_one]
  rfl

theorem retained_t3_bush :
    retainedTreeProfile c a b oldT3Bush=oldActualClock c a b*oldActualClock c a b := by
  rw [oldT3Bush,retainedTreeProfile_attach,retained_leaf,retainedAct_one,retained_t2]
  rfl

theorem retained_t4_chain :
    retainedTreeProfile c a b oldT4Chain=
      oldActualAct c a b (oldActualAct c a b (oldActualClock c a b)) := by
  rw [oldT4Chain,retainedTreeProfile_attach,retained_t3_chain,retained_leaf,mul_one]
  rfl

theorem retained_t4_unary_bush :
    retainedTreeProfile c a b oldT4UnaryBush=
      oldActualAct c a b (fun i=>(oldActualClock c a b i)^2) := by
  rw [oldT4UnaryBush,retainedTreeProfile_attach,retained_t3_bush,retained_leaf,mul_one]
  congr 1
  funext i
  simp only [Pi.mul_apply,pow_two]

theorem retained_t4_mixL :
    retainedTreeProfile c a b oldT4MixL=
      oldActualAct c a b (oldActualClock c a b)*oldActualClock c a b := by
  rw [oldT4MixL,retainedTreeProfile_attach,retained_t2]
  rfl

theorem retained_t4_mixR :
    retainedTreeProfile c a b oldT4MixR=
      oldActualAct c a b (oldActualClock c a b)*oldActualClock c a b := by
  rw [oldT4MixR,retainedTreeProfile_attach,retained_leaf,retainedAct_one,retained_t3_chain]
  exact mul_comm _ _

theorem retained_t4_bush :
    retainedTreeProfile c a b oldT4Bush=
      oldActualClock c a b*(oldActualClock c a b*oldActualClock c a b) := by
  rw [oldT4Bush,retainedTreeProfile_attach,retained_leaf,retainedAct_one,retained_t3_bush]
  rfl

/-- The true projected retained profile through size four. This
includes all five plane size-four tree shapes and does not assume any
of the two global forward host residuals. -/
theorem retained_projected_low (t : RKCert.Tree) (ht : t.order≤4)
    (he : IsUnit (Ring.inverse (8:R))) (h2 : IsUnit (2:R)) (h3 : IsUnit (3:R))
    (hs : IsUnit (actualHost c a b).s) :
    retainedProj (actualHost c a b) (retainedTreeProfile c a b t)=
      treeModel t (actualHost c a b).q-(actualHost c a b).α*treeModel t (actualHost c a b).s := by
  let p:=actualHost c a b
  let eps:=Ring.inverse (8:R)
  have hL := retained_linear_primitive p eps he h2 hs
  have hQ := retained_quadratic_primitive p eps he h2 h3 hs
  have hChain := retained_projected_chain4 p eps he h2 h3 hs
  have ht0 := t.order_pos
  have hCases : t.order=1 ∨ t.order=2 ∨ t.order=3 ∨ t.order=4 := by omega
  rcases hCases with hh|hh|hh|hh
  · rw [tree_order_one t hh,retained_leaf]
    simp [retainedProj,treeModel,treeScale,RKCert.Tree.order]
  · rw [tree_order_two t hh,retained_t2]
    simp [oldActualClock,retainedClock,retainedProj,treeModel,treeScale,oldT2,
      RKCert.Tree.order,Ring.inverse_one]
  · rcases tree_order_three t hh with rfl|rfl
    · rw [retained_t3_chain,oldActualAct,oldActualClock,hL]
      simp [retainedProj,oldBasis,retainedClock,treeModel,treeScale,oldT3Chain,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring
    · rw [retained_t3_bush]
      simp [retainedProj,oldActualClock,retainedClock,treeModel,treeScale,oldT3Bush,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring
  · rcases tree_order_four t hh with rfl|rfl|rfl|rfl|rfl
    · rw [retained_t4_chain,oldActualAct,oldActualAct,oldActualClock,hChain]
      norm_num [treeModel,treeScale,oldT4Chain,oldT3Chain,oldT2,RKCert.Tree.order,Ring.inverse_one] <;> rfl
    · rw [retained_t4_unary_bush,oldActualAct,oldActualClock,hQ]
      simp [retainedProj,retainedClock,treeModel,treeScale,oldT4UnaryBush,oldT3Bush,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring
    · rw [retained_t4_mixL,oldActualAct,oldActualClock,hL]
      simp [retainedProj,retainedClock,oldBasis,treeModel,treeScale,oldT4MixL,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring
    · rw [retained_t4_mixR,oldActualAct,oldActualClock,hL]
      simp [retainedProj,retainedClock,oldBasis,treeModel,treeScale,oldT4MixR,oldT3Chain,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring
    · rw [retained_t4_bush]
      simp [retainedProj,oldActualClock,retainedClock,treeModel,treeScale,oldT4Bush,oldT3Bush,oldT2,
        RKCert.Tree.order,Ring.inverse_one] <;> ring

end Physical
end
end RKResearch.Certified.ERK10FixedQ29Adic.Physical

#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.tree_order_four
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.retained_projected_chain4
#print axioms RKResearch.Certified.ERK10FixedQ29Adic.Physical.retained_projected_low
