module

public import RKCert.ReviewedNative.SDIRKNineReplayAlias4
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.SDIRKNineReplay

open RKResearch FiniteRootedTree
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 4500000
set_option maxRecDepth 12000

private theorem cover_nil {R : Type*} [CommRing R] {x y : R} :
    ∀ t ∈ ([] : List FiniteRootedTree), Paid x y t := by simp

private theorem cover_cons {R : Type*} [CommRing R] {x y : R} {a : FiniteRootedTree}
    {tail : List FiniteRootedTree} (ha : Paid x y a)
    (ht : ∀ t ∈ tail, Paid x y t) : ∀ t ∈ a :: tail, Paid x y t := by
  intro t h
  rcases List.mem_cons.mp h with rfl | hp
  · exact ha
  · exact ht _ hp

theorem catalogue_paid0 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 0, Paid x y t := by
  change ∀ t ∈ [tree0], Paid x y t
  exact cover_cons (pay0 h) (
    cover_nil (x := x) (y := y))

theorem catalogue_paid1 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 1, Paid x y t := by
  change ∀ t ∈ [tree1], Paid x y t
  exact cover_cons (pay1 h) (
    cover_nil (x := x) (y := y))

theorem catalogue_paid2 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 2, Paid x y t := by
  change ∀ t ∈ [tree2, tree3], Paid x y t
  exact cover_cons (pay2 h) (
    cover_cons (pay3 h) (
    cover_nil (x := x) (y := y)))

theorem catalogue_paid3 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 3, Paid x y t := by
  change ∀ t ∈ [tree4, tree5, tree6, tree7, tree8], Paid x y t
  exact cover_cons (pay4 h) (
    cover_cons (pay5 h) (
    cover_cons (pay6 h) (
    cover_cons (pay7 h) (
    cover_cons (pay8 h) (
    cover_nil (x := x) (y := y))))))

theorem catalogue_paid4 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 4, Paid x y t := by
  change ∀ t ∈ [tree9, tree10, tree11, tree12, tree13, tree14, tree15, tree16, tree17, tree18, tree19, tree20, tree21, tree22], Paid x y t
  exact cover_cons (pay9 h) (
    cover_cons (pay10 h) (
    cover_cons (pay11 h) (
    cover_cons (pay12 h) (
    cover_cons (pay13 h) (
    cover_cons (pay14 h) (
    cover_cons (pay15 h) (
    cover_cons (pay16 h) (
    cover_cons (pay17 h) (
    cover_cons (pay18 h) (
    cover_cons (pay19 h) (
    cover_cons (pay20 h) (
    cover_cons (pay21 h) (
    cover_cons (pay22 h) (
    cover_nil (x := x) (y := y)))))))))))))))

theorem catalogue_paid5 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 5, Paid x y t := by
  change ∀ t ∈ [tree23, tree24, tree25, tree26, tree27, tree28, tree29, tree30, tree31, tree32, tree33, tree34, tree35, tree36, tree37, tree38, tree39, tree40, tree41, tree42, tree43, tree44, tree45, tree46, tree47, tree48, tree49, tree50, tree51, tree52, tree53, tree54, tree55, tree56, tree57, tree58, tree59, tree60, tree61, tree62, tree63, tree64], Paid x y t
  exact cover_cons (pay23 h) (
    cover_cons (pay24 h) (
    cover_cons (pay25 h) (
    cover_cons (pay26 h) (
    cover_cons (pay27 h) (
    cover_cons (pay28 h) (
    cover_cons (pay29 h) (
    cover_cons (pay30 h) (
    cover_cons (pay31 h) (
    cover_cons (pay32 h) (
    cover_cons (pay33 h) (
    cover_cons (pay34 h) (
    cover_cons (pay35 h) (
    cover_cons (pay36 h) (
    cover_cons (pay37 h) (
    cover_cons (pay38 h) (
    cover_cons (pay39 h) (
    cover_cons (pay40 h) (
    cover_cons (pay41 h) (
    cover_cons (pay42 h) (
    cover_cons (pay43 h) (
    cover_cons (pay44 h) (
    cover_cons (pay45 h) (
    cover_cons (pay46 h) (
    cover_cons (pay47 h) (
    cover_cons (pay48 h) (
    cover_cons (pay49 h) (
    cover_cons (pay50 h) (
    cover_cons (pay51 h) (
    cover_cons (pay52 h) (
    cover_cons (pay53 h) (
    cover_cons (pay54 h) (
    cover_cons (pay55 h) (
    cover_cons (pay56 h) (
    cover_cons (pay57 h) (
    cover_cons (pay58 h) (
    cover_cons (pay59 h) (
    cover_cons (pay60 h) (
    cover_cons (pay61 h) (
    cover_cons (pay62 h) (
    cover_cons (pay63 h) (
    cover_cons (pay64 h) (
    cover_nil (x := x) (y := y)))))))))))))))))))))))))))))))))))))))))))

theorem catalogue_paid6 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : ∀ t ∈ catalogue 6, Paid x y t := by
  change ∀ t ∈ [tree65, tree66, tree67, tree68, tree69, tree70, tree71, tree72, tree73, tree74, tree75, tree76, tree77, tree78, tree79, tree80, tree81, tree82, tree83, tree84, tree85, tree86, tree87, tree88, tree89, tree90, tree91, tree92, tree93, tree94, tree95, tree96, tree97, tree98, tree99, tree100, tree101, tree102, tree103, tree104, tree105, tree106, tree107, tree108, tree109, tree110, tree111, tree112, tree113, tree114, tree115, tree116, tree117, tree118, tree119, tree120, tree121, tree122, tree123, tree124, tree125, tree126, tree127, tree128, tree129, tree130, tree131, tree132, tree133, tree134, tree135, tree136, tree137, tree138, tree139, tree140, tree141, tree142, tree143, tree144, tree145, tree146, tree147, tree148, tree149, tree150, tree151, tree152, tree153, tree154, tree155, tree156, tree157, tree158, tree159, tree160, tree161, tree162, tree163, tree164, tree165, tree166, tree167, tree168, tree169, tree170, tree171, tree172, tree173, tree174, tree175, tree176, tree177, tree178, tree179, tree180, tree181, tree182, tree183, tree184, tree185, tree186, tree187, tree188, tree189, tree190, tree191, tree192, tree193, tree194, tree195, tree196], Paid x y t
  exact cover_cons (pay65 h) (
    cover_cons (pay66 h) (
    cover_cons (pay67 h) (
    cover_cons (pay68 h) (
    cover_cons (pay69 h) (
    cover_cons (pay70 h) (
    cover_cons (pay71 h) (
    cover_cons (pay72 h) (
    cover_cons (pay73 h) (
    cover_cons (pay74 h) (
    cover_cons (pay75 h) (
    cover_cons (pay76 h) (
    cover_cons (pay77 h) (
    cover_cons (pay78 h) (
    cover_cons (pay79 h) (
    cover_cons (pay80 h) (
    cover_cons (pay81 h) (
    cover_cons (pay82 h) (
    cover_cons (pay83 h) (
    cover_cons (pay84 h) (
    cover_cons (pay85 h) (
    cover_cons (pay86 h) (
    cover_cons (pay87 h) (
    cover_cons (pay88 h) (
    cover_cons (pay89 h) (
    cover_cons (pay90 h) (
    cover_cons (pay91 h) (
    cover_cons (pay92 h) (
    cover_cons (pay93 h) (
    cover_cons (pay94 h) (
    cover_cons (pay95 h) (
    cover_cons (pay96 h) (
    cover_cons (pay97 h) (
    cover_cons (pay98 h) (
    cover_cons (pay99 h) (
    cover_cons (pay100 h) (
    cover_cons (pay101 h) (
    cover_cons (pay102 h) (
    cover_cons (pay103 h) (
    cover_cons (pay104 h) (
    cover_cons (pay105 h) (
    cover_cons (pay106 h) (
    cover_cons (pay107 h) (
    cover_cons (pay108 h) (
    cover_cons (pay109 h) (
    cover_cons (pay110 h) (
    cover_cons (pay111 h) (
    cover_cons (pay112 h) (
    cover_cons (pay113 h) (
    cover_cons (pay114 h) (
    cover_cons (pay115 h) (
    cover_cons (pay116 h) (
    cover_cons (pay117 h) (
    cover_cons (pay118 h) (
    cover_cons (pay119 h) (
    cover_cons (pay120 h) (
    cover_cons (pay121 h) (
    cover_cons (pay122 h) (
    cover_cons (pay123 h) (
    cover_cons (pay124 h) (
    cover_cons (pay125 h) (
    cover_cons (pay126 h) (
    cover_cons (pay127 h) (
    cover_cons (pay128 h) (
    cover_cons (pay129 h) (
    cover_cons (pay130 h) (
    cover_cons (pay131 h) (
    cover_cons (pay132 h) (
    cover_cons (pay133 h) (
    cover_cons (pay134 h) (
    cover_cons (pay135 h) (
    cover_cons (pay136 h) (
    cover_cons (pay137 h) (
    cover_cons (pay138 h) (
    cover_cons (pay139 h) (
    cover_cons (pay140 h) (
    cover_cons (pay141 h) (
    cover_cons (pay142 h) (
    cover_cons (pay143 h) (
    cover_cons (pay144 h) (
    cover_cons (pay145 h) (
    cover_cons (pay146 h) (
    cover_cons (pay147 h) (
    cover_cons (pay148 h) (
    cover_cons (pay149 h) (
    cover_cons (pay150 h) (
    cover_cons (pay151 h) (
    cover_cons (pay152 h) (
    cover_cons (pay153 h) (
    cover_cons (pay154 h) (
    cover_cons (pay155 h) (
    cover_cons (pay156 h) (
    cover_cons (pay157 h) (
    cover_cons (pay158 h) (
    cover_cons (pay159 h) (
    cover_cons (pay160 h) (
    cover_cons (pay161 h) (
    cover_cons (pay162 h) (
    cover_cons (pay163 h) (
    cover_cons (pay164 h) (
    cover_cons (pay165 h) (
    cover_cons (pay166 h) (
    cover_cons (pay167 h) (
    cover_cons (pay168 h) (
    cover_cons (pay169 h) (
    cover_cons (pay170 h) (
    cover_cons (pay171 h) (
    cover_cons (pay172 h) (
    cover_cons (pay173 h) (
    cover_cons (pay174 h) (
    cover_cons (pay175 h) (
    cover_cons (pay176 h) (
    cover_cons (pay177 h) (
    cover_cons (pay178 h) (
    cover_cons (pay179 h) (
    cover_cons (pay180 h) (
    cover_cons (pay181 h) (
    cover_cons (pay182 h) (
    cover_cons (pay183 h) (
    cover_cons (pay184 h) (
    cover_cons (pay185 h) (
    cover_cons (pay186 h) (
    cover_cons (pay187 h) (
    cover_cons (pay188 h) (
    cover_cons (pay189 h) (
    cover_cons (pay190 h) (
    cover_cons (pay191 h) (
    cover_cons (pay192 h) (
    cover_cons (pay193 h) (
    cover_cons (pay194 h) (
    cover_cons (pay195 h) (
    cover_cons (pay196 h) (
    cover_nil (x := x) (y := y)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem all_moments {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) :
    ∀ t : FiniteRootedTree, (t.order:ℕ) ≤ 7 → Paid x y t := by
  intro t ht
  have hpos := t.order.pos
  let n : ℕ := (t.order:ℕ) - 1
  have hn : n < 7 := by dsimp [n]; omega
  have hmem : t ∈ catalogue n := by
    rw [catalogue_eq n hn]
    apply (mem_treesOfOrderSucc n t).2
    dsimp [n]
    omega
  have ha : ∀ j < 7, ∀ s ∈ catalogue j, Paid x y s := by
    intro j hj
    interval_cases j
    · exact catalogue_paid0 h
    · exact catalogue_paid1 h
    · exact catalogue_paid2 h
    · exact catalogue_paid3 h
    · exact catalogue_paid4 h
    · exact catalogue_paid5 h
    · exact catalogue_paid6 h
  exact ha n hn t hmem

end RKResearch.Certified.SDIRKNineReplay
