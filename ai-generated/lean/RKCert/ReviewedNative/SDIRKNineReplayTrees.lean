module

public import RKCert.ReviewedNative.SDIRKNineReplayData
public import RKCert.ReviewedNative.FiniteOrderCheck
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

def tree0 : FiniteRootedTree := .leaf
def tree1 : FiniteRootedTree := tree0 ◂ tree0
def tree2 : FiniteRootedTree := tree0 ◂ tree1
def tree3 : FiniteRootedTree := tree1 ◂ tree0
def tree4 : FiniteRootedTree := tree0 ◂ tree2
def tree5 : FiniteRootedTree := tree0 ◂ tree3
def tree6 : FiniteRootedTree := tree1 ◂ tree1
def tree7 : FiniteRootedTree := tree2 ◂ tree0
def tree8 : FiniteRootedTree := tree3 ◂ tree0
def tree9 : FiniteRootedTree := tree0 ◂ tree4
def tree10 : FiniteRootedTree := tree0 ◂ tree5
def tree11 : FiniteRootedTree := tree0 ◂ tree6
def tree12 : FiniteRootedTree := tree0 ◂ tree7
def tree13 : FiniteRootedTree := tree0 ◂ tree8
def tree14 : FiniteRootedTree := tree1 ◂ tree2
def tree15 : FiniteRootedTree := tree1 ◂ tree3
def tree16 : FiniteRootedTree := tree2 ◂ tree1
def tree17 : FiniteRootedTree := tree3 ◂ tree1
def tree18 : FiniteRootedTree := tree4 ◂ tree0
def tree19 : FiniteRootedTree := tree5 ◂ tree0
def tree20 : FiniteRootedTree := tree6 ◂ tree0
def tree21 : FiniteRootedTree := tree7 ◂ tree0
def tree22 : FiniteRootedTree := tree8 ◂ tree0
def tree23 : FiniteRootedTree := tree0 ◂ tree9
def tree24 : FiniteRootedTree := tree0 ◂ tree10
def tree25 : FiniteRootedTree := tree0 ◂ tree11
def tree26 : FiniteRootedTree := tree0 ◂ tree12
def tree27 : FiniteRootedTree := tree0 ◂ tree13
def tree28 : FiniteRootedTree := tree0 ◂ tree14
def tree29 : FiniteRootedTree := tree0 ◂ tree15
def tree30 : FiniteRootedTree := tree0 ◂ tree16
def tree31 : FiniteRootedTree := tree0 ◂ tree17
def tree32 : FiniteRootedTree := tree0 ◂ tree18
def tree33 : FiniteRootedTree := tree0 ◂ tree19
def tree34 : FiniteRootedTree := tree0 ◂ tree20
def tree35 : FiniteRootedTree := tree0 ◂ tree21
def tree36 : FiniteRootedTree := tree0 ◂ tree22
def tree37 : FiniteRootedTree := tree1 ◂ tree4
def tree38 : FiniteRootedTree := tree1 ◂ tree5
def tree39 : FiniteRootedTree := tree1 ◂ tree6
def tree40 : FiniteRootedTree := tree1 ◂ tree7
def tree41 : FiniteRootedTree := tree1 ◂ tree8
def tree42 : FiniteRootedTree := tree2 ◂ tree2
def tree43 : FiniteRootedTree := tree2 ◂ tree3
def tree44 : FiniteRootedTree := tree3 ◂ tree2
def tree45 : FiniteRootedTree := tree3 ◂ tree3
def tree46 : FiniteRootedTree := tree4 ◂ tree1
def tree47 : FiniteRootedTree := tree5 ◂ tree1
def tree48 : FiniteRootedTree := tree6 ◂ tree1
def tree49 : FiniteRootedTree := tree7 ◂ tree1
def tree50 : FiniteRootedTree := tree8 ◂ tree1
def tree51 : FiniteRootedTree := tree9 ◂ tree0
def tree52 : FiniteRootedTree := tree10 ◂ tree0
def tree53 : FiniteRootedTree := tree11 ◂ tree0
def tree54 : FiniteRootedTree := tree12 ◂ tree0
def tree55 : FiniteRootedTree := tree13 ◂ tree0
def tree56 : FiniteRootedTree := tree14 ◂ tree0
def tree57 : FiniteRootedTree := tree15 ◂ tree0
def tree58 : FiniteRootedTree := tree16 ◂ tree0
def tree59 : FiniteRootedTree := tree17 ◂ tree0
def tree60 : FiniteRootedTree := tree18 ◂ tree0
def tree61 : FiniteRootedTree := tree19 ◂ tree0
def tree62 : FiniteRootedTree := tree20 ◂ tree0
def tree63 : FiniteRootedTree := tree21 ◂ tree0
def tree64 : FiniteRootedTree := tree22 ◂ tree0
def tree65 : FiniteRootedTree := tree0 ◂ tree23
def tree66 : FiniteRootedTree := tree0 ◂ tree24
def tree67 : FiniteRootedTree := tree0 ◂ tree25
def tree68 : FiniteRootedTree := tree0 ◂ tree26
def tree69 : FiniteRootedTree := tree0 ◂ tree27
def tree70 : FiniteRootedTree := tree0 ◂ tree28
def tree71 : FiniteRootedTree := tree0 ◂ tree29
def tree72 : FiniteRootedTree := tree0 ◂ tree30
def tree73 : FiniteRootedTree := tree0 ◂ tree31
def tree74 : FiniteRootedTree := tree0 ◂ tree32
def tree75 : FiniteRootedTree := tree0 ◂ tree33
def tree76 : FiniteRootedTree := tree0 ◂ tree34
def tree77 : FiniteRootedTree := tree0 ◂ tree35
def tree78 : FiniteRootedTree := tree0 ◂ tree36
def tree79 : FiniteRootedTree := tree0 ◂ tree37
def tree80 : FiniteRootedTree := tree0 ◂ tree38
def tree81 : FiniteRootedTree := tree0 ◂ tree39
def tree82 : FiniteRootedTree := tree0 ◂ tree40
def tree83 : FiniteRootedTree := tree0 ◂ tree41
def tree84 : FiniteRootedTree := tree0 ◂ tree42
def tree85 : FiniteRootedTree := tree0 ◂ tree43
def tree86 : FiniteRootedTree := tree0 ◂ tree44
def tree87 : FiniteRootedTree := tree0 ◂ tree45
def tree88 : FiniteRootedTree := tree0 ◂ tree46
def tree89 : FiniteRootedTree := tree0 ◂ tree47
def tree90 : FiniteRootedTree := tree0 ◂ tree48
def tree91 : FiniteRootedTree := tree0 ◂ tree49
def tree92 : FiniteRootedTree := tree0 ◂ tree50
def tree93 : FiniteRootedTree := tree0 ◂ tree51
def tree94 : FiniteRootedTree := tree0 ◂ tree52
def tree95 : FiniteRootedTree := tree0 ◂ tree53
def tree96 : FiniteRootedTree := tree0 ◂ tree54
def tree97 : FiniteRootedTree := tree0 ◂ tree55
def tree98 : FiniteRootedTree := tree0 ◂ tree56
def tree99 : FiniteRootedTree := tree0 ◂ tree57
def tree100 : FiniteRootedTree := tree0 ◂ tree58
def tree101 : FiniteRootedTree := tree0 ◂ tree59
def tree102 : FiniteRootedTree := tree0 ◂ tree60
def tree103 : FiniteRootedTree := tree0 ◂ tree61
def tree104 : FiniteRootedTree := tree0 ◂ tree62
def tree105 : FiniteRootedTree := tree0 ◂ tree63
def tree106 : FiniteRootedTree := tree0 ◂ tree64
def tree107 : FiniteRootedTree := tree1 ◂ tree9
def tree108 : FiniteRootedTree := tree1 ◂ tree10
def tree109 : FiniteRootedTree := tree1 ◂ tree11
def tree110 : FiniteRootedTree := tree1 ◂ tree12
def tree111 : FiniteRootedTree := tree1 ◂ tree13
def tree112 : FiniteRootedTree := tree1 ◂ tree14
def tree113 : FiniteRootedTree := tree1 ◂ tree15
def tree114 : FiniteRootedTree := tree1 ◂ tree16
def tree115 : FiniteRootedTree := tree1 ◂ tree17
def tree116 : FiniteRootedTree := tree1 ◂ tree18
def tree117 : FiniteRootedTree := tree1 ◂ tree19
def tree118 : FiniteRootedTree := tree1 ◂ tree20
def tree119 : FiniteRootedTree := tree1 ◂ tree21
def tree120 : FiniteRootedTree := tree1 ◂ tree22
def tree121 : FiniteRootedTree := tree2 ◂ tree4
def tree122 : FiniteRootedTree := tree2 ◂ tree5
def tree123 : FiniteRootedTree := tree2 ◂ tree6
def tree124 : FiniteRootedTree := tree2 ◂ tree7
def tree125 : FiniteRootedTree := tree2 ◂ tree8
def tree126 : FiniteRootedTree := tree3 ◂ tree4
def tree127 : FiniteRootedTree := tree3 ◂ tree5
def tree128 : FiniteRootedTree := tree3 ◂ tree6
def tree129 : FiniteRootedTree := tree3 ◂ tree7
def tree130 : FiniteRootedTree := tree3 ◂ tree8
def tree131 : FiniteRootedTree := tree4 ◂ tree2
def tree132 : FiniteRootedTree := tree4 ◂ tree3
def tree133 : FiniteRootedTree := tree5 ◂ tree2
def tree134 : FiniteRootedTree := tree5 ◂ tree3
def tree135 : FiniteRootedTree := tree6 ◂ tree2
def tree136 : FiniteRootedTree := tree6 ◂ tree3
def tree137 : FiniteRootedTree := tree7 ◂ tree2
def tree138 : FiniteRootedTree := tree7 ◂ tree3
def tree139 : FiniteRootedTree := tree8 ◂ tree2
def tree140 : FiniteRootedTree := tree8 ◂ tree3
def tree141 : FiniteRootedTree := tree9 ◂ tree1
def tree142 : FiniteRootedTree := tree10 ◂ tree1
def tree143 : FiniteRootedTree := tree11 ◂ tree1
def tree144 : FiniteRootedTree := tree12 ◂ tree1
def tree145 : FiniteRootedTree := tree13 ◂ tree1
def tree146 : FiniteRootedTree := tree14 ◂ tree1
def tree147 : FiniteRootedTree := tree15 ◂ tree1
def tree148 : FiniteRootedTree := tree16 ◂ tree1
def tree149 : FiniteRootedTree := tree17 ◂ tree1
def tree150 : FiniteRootedTree := tree18 ◂ tree1
def tree151 : FiniteRootedTree := tree19 ◂ tree1
def tree152 : FiniteRootedTree := tree20 ◂ tree1
def tree153 : FiniteRootedTree := tree21 ◂ tree1
def tree154 : FiniteRootedTree := tree22 ◂ tree1
def tree155 : FiniteRootedTree := tree23 ◂ tree0
def tree156 : FiniteRootedTree := tree24 ◂ tree0
def tree157 : FiniteRootedTree := tree25 ◂ tree0
def tree158 : FiniteRootedTree := tree26 ◂ tree0
def tree159 : FiniteRootedTree := tree27 ◂ tree0
def tree160 : FiniteRootedTree := tree28 ◂ tree0
def tree161 : FiniteRootedTree := tree29 ◂ tree0
def tree162 : FiniteRootedTree := tree30 ◂ tree0
def tree163 : FiniteRootedTree := tree31 ◂ tree0
def tree164 : FiniteRootedTree := tree32 ◂ tree0
def tree165 : FiniteRootedTree := tree33 ◂ tree0
def tree166 : FiniteRootedTree := tree34 ◂ tree0
def tree167 : FiniteRootedTree := tree35 ◂ tree0
def tree168 : FiniteRootedTree := tree36 ◂ tree0
def tree169 : FiniteRootedTree := tree37 ◂ tree0
def tree170 : FiniteRootedTree := tree38 ◂ tree0
def tree171 : FiniteRootedTree := tree39 ◂ tree0
def tree172 : FiniteRootedTree := tree40 ◂ tree0
def tree173 : FiniteRootedTree := tree41 ◂ tree0
def tree174 : FiniteRootedTree := tree42 ◂ tree0
def tree175 : FiniteRootedTree := tree43 ◂ tree0
def tree176 : FiniteRootedTree := tree44 ◂ tree0
def tree177 : FiniteRootedTree := tree45 ◂ tree0
def tree178 : FiniteRootedTree := tree46 ◂ tree0
def tree179 : FiniteRootedTree := tree47 ◂ tree0
def tree180 : FiniteRootedTree := tree48 ◂ tree0
def tree181 : FiniteRootedTree := tree49 ◂ tree0
def tree182 : FiniteRootedTree := tree50 ◂ tree0
def tree183 : FiniteRootedTree := tree51 ◂ tree0
def tree184 : FiniteRootedTree := tree52 ◂ tree0
def tree185 : FiniteRootedTree := tree53 ◂ tree0
def tree186 : FiniteRootedTree := tree54 ◂ tree0
def tree187 : FiniteRootedTree := tree55 ◂ tree0
def tree188 : FiniteRootedTree := tree56 ◂ tree0
def tree189 : FiniteRootedTree := tree57 ◂ tree0
def tree190 : FiniteRootedTree := tree58 ◂ tree0
def tree191 : FiniteRootedTree := tree59 ◂ tree0
def tree192 : FiniteRootedTree := tree60 ◂ tree0
def tree193 : FiniteRootedTree := tree61 ◂ tree0
def tree194 : FiniteRootedTree := tree62 ◂ tree0
def tree195 : FiniteRootedTree := tree63 ◂ tree0
def tree196 : FiniteRootedTree := tree64 ◂ tree0

def catalogue : ℕ → List FiniteRootedTree
  | 0 => [tree0]
  | 1 => [tree1]
  | 2 => [tree2, tree3]
  | 3 => [tree4, tree5, tree6, tree7, tree8]
  | 4 => [tree9, tree10, tree11, tree12, tree13, tree14, tree15, tree16, tree17, tree18, tree19, tree20, tree21, tree22]
  | 5 => [tree23, tree24, tree25, tree26, tree27, tree28, tree29, tree30, tree31, tree32, tree33, tree34, tree35, tree36, tree37, tree38, tree39, tree40, tree41, tree42, tree43, tree44, tree45, tree46, tree47, tree48, tree49, tree50, tree51, tree52, tree53, tree54, tree55, tree56, tree57, tree58, tree59, tree60, tree61, tree62, tree63, tree64]
  | 6 => [tree65, tree66, tree67, tree68, tree69, tree70, tree71, tree72, tree73, tree74, tree75, tree76, tree77, tree78, tree79, tree80, tree81, tree82, tree83, tree84, tree85, tree86, tree87, tree88, tree89, tree90, tree91, tree92, tree93, tree94, tree95, tree96, tree97, tree98, tree99, tree100, tree101, tree102, tree103, tree104, tree105, tree106, tree107, tree108, tree109, tree110, tree111, tree112, tree113, tree114, tree115, tree116, tree117, tree118, tree119, tree120, tree121, tree122, tree123, tree124, tree125, tree126, tree127, tree128, tree129, tree130, tree131, tree132, tree133, tree134, tree135, tree136, tree137, tree138, tree139, tree140, tree141, tree142, tree143, tree144, tree145, tree146, tree147, tree148, tree149, tree150, tree151, tree152, tree153, tree154, tree155, tree156, tree157, tree158, tree159, tree160, tree161, tree162, tree163, tree164, tree165, tree166, tree167, tree168, tree169, tree170, tree171, tree172, tree173, tree174, tree175, tree176, tree177, tree178, tree179, tree180, tree181, tree182, tree183, tree184, tree185, tree186, tree187, tree188, tree189, tree190, tree191, tree192, tree193, tree194, tree195, tree196]
  | _ => []

theorem catalogue_eq (n : ℕ) (hn : n < 7) : catalogue n = treesOfOrderSucc n := by
  interval_cases n
  · simp [catalogue, treesOfOrderSucc, tree0]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1, tree2, tree3]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1, tree2, tree3, tree4, tree5, tree6, tree7, tree8]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1, tree2, tree3, tree4, tree5, tree6, tree7, tree8, tree9, tree10, tree11, tree12, tree13, tree14, tree15, tree16, tree17, tree18, tree19, tree20, tree21, tree22]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1, tree2, tree3, tree4, tree5, tree6, tree7, tree8, tree9, tree10, tree11, tree12, tree13, tree14, tree15, tree16, tree17, tree18, tree19, tree20, tree21, tree22, tree23, tree24, tree25, tree26, tree27, tree28, tree29, tree30, tree31, tree32, tree33, tree34, tree35, tree36, tree37, tree38, tree39, tree40, tree41, tree42, tree43, tree44, tree45, tree46, tree47, tree48, tree49, tree50, tree51, tree52, tree53, tree54, tree55, tree56, tree57, tree58, tree59, tree60, tree61, tree62, tree63, tree64]
  · simp [catalogue, treesOfOrderSucc, List.finRange_succ, tree0, tree1, tree2, tree3, tree4, tree5, tree6, tree7, tree8, tree9, tree10, tree11, tree12, tree13, tree14, tree15, tree16, tree17, tree18, tree19, tree20, tree21, tree22, tree23, tree24, tree25, tree26, tree27, tree28, tree29, tree30, tree31, tree32, tree33, tree34, tree35, tree36, tree37, tree38, tree39, tree40, tree41, tree42, tree43, tree44, tree45, tree46, tree47, tree48, tree49, tree50, tree51, tree52, tree53, tree54, tree55, tree56, tree57, tree58, tree59, tree60, tree61, tree62, tree63, tree64, tree65, tree66, tree67, tree68, tree69, tree70, tree71, tree72, tree73, tree74, tree75, tree76, tree77, tree78, tree79, tree80, tree81, tree82, tree83, tree84, tree85, tree86, tree87, tree88, tree89, tree90, tree91, tree92, tree93, tree94, tree95, tree96, tree97, tree98, tree99, tree100, tree101, tree102, tree103, tree104, tree105, tree106, tree107, tree108, tree109, tree110, tree111, tree112, tree113, tree114, tree115, tree116, tree117, tree118, tree119, tree120, tree121, tree122, tree123, tree124, tree125, tree126, tree127, tree128, tree129, tree130, tree131, tree132, tree133, tree134, tree135, tree136, tree137, tree138, tree139, tree140, tree141, tree142, tree143, tree144, tree145, tree146, tree147, tree148, tree149, tree150, tree151, tree152, tree153, tree154, tree155, tree156, tree157, tree158, tree159, tree160, tree161, tree162, tree163, tree164, tree165, tree166, tree167, tree168, tree169, tree170, tree171, tree172, tree173, tree174, tree175, tree176, tree177, tree178, tree179, tree180, tree181, tree182, tree183, tree184, tree185, tree186, tree187, tree188, tree189, tree190, tree191, tree192, tree193, tree194, tree195, tree196]

end RKResearch.Certified.SDIRKNineReplay
