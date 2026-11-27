#!/usr/bin/env python3
"""Emit compact kernel-checked modular flag receipts for a CRT tableau."""
from pathlib import Path
from argparse import ArgumentParser
import json

def emit(source,out):
    o=json.loads(source.read_text())
    S,N=o["sizes"],o["modulus"]
    assert S==[0,0,0,1,2,3,5,7,8,9]
    assert all(s==[[j+1,1]] for d in o["selectors"] for j,s in enumerate(d))
    assert all(0<=v<N for row in o["A"] for v in row)
    stem="DIRK10PrimeCRT"
    ns=f"RKResearch.Certified.{stem}"
    pre="RKCert.ReviewedNative."
    m=o["moduli"]; assert m[0]==3481
    pp=[59]+m[1:]
    def hs(imports):
        return "module\n\n"+"".join(f"public import {v}\n" for v in imports)+"\n@[expose] public section\n\n"
    def cfg(imports):
        return hs([pre+v for v in imports])+f"namespace {ns}\nopen RKResearch FiniteRootedTree RingFlagReplay\nopen scoped Matrix\nset_option maxHeartbeats 0\nset_option maxRecDepth 36000\nset_option Elab.async false\n\n"
    tail=f"\nend {ns}\n"
    def write(suf,v):
        (out/(stem+suf+'.lean')).write_text(v)
    def arr(x):
        return "#["+", ".join(map(arr,x))+"]" if isinstance(x,(list,tuple)) else str(x)
    def list_(x):
        return "["+", ".join(map(str,x))+"]"
    write("Arithmetic",f"""module

@[expose] public section

/-! Arithmetic receipts for the common modulus. This module only uses core Lean. -/

namespace {ns}

def modulus : Nat := {N}
def primes : List Nat := {list_(pp)}
def factorModuli : List Nat := {list_(m)}

theorem factorProduct : factorModuli.prod=modulus := by decide +kernel

theorem supportedDivisors :
    ((3481::primes).all fun p => decide (modulus % p = 0)) = true := by decide +kernel

theorem divides_of_mem {{p : Nat}} (h : p ∈ 3481::primes) : p ∣ modulus :=
  Nat.dvd_iff_mod_eq_zero.mpr (of_decide_eq_true (List.all_eq_true.mp supportedDivisors p h))

theorem prime_divides {{p : Nat}} (h : p ∈ primes) : p ∣ modulus :=
  divides_of_mem (List.mem_cons_of_mem _ h)

theorem squared_59_divides : (59^2:Nat) ∣ modulus :=
  divides_of_mem (by decide)

#print axioms factorProduct
#print axioms divides_of_mem
{tail}""")
    data=hs([pre+"RingFlagReplay",pre+stem+"Arithmetic","Mathlib.Data.ZMod.Basic"])
    data+=f"""namespace {ns}
open RKResearch RingFlagReplay
open scoped Matrix
set_option maxHeartbeats 0
set_option maxRecDepth 36000

abbrev F := ZMod modulus
def a0 : Array (Array Nat) := {arr(o["A"])}
def b0 : Array Nat := {arr(o["b"])}
def c0 : Array Nat := {arr(o["c"])}
def sizes : Array Nat := {arr(S)}
def bases : Array (Array (Array Nat)) := {arr(o["basis"])}
def star : F := {o['star']}
def starInv : F := {o['starInv']}

def packet : Packet 11 F where
  a i j := ((a0.getD i.val #[]).getD j.val 0 : Nat)
  b i := (b0.getD i.val 0 : Nat)
  clock i := (c0.getD i.val 0 : Nat)
  size d := sizes.getD d 0
  pivot _ i := ⟨(i.val+1) % 11, Nat.mod_lt _ (by decide)⟩
  basis d i j := (((bases.getD d #[]).getD i.val #[]).getD j.val 0 : Nat)

def blockA (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkA packet d)
def blockC (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : Nat) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : Nat) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)
"""
    write("Data",data+tail)
    groups={
       "Moments":[("node","checkNode packet")]+[(f"primitive{d}",f"checkPrimitive packet {d}")for d in range(9)]
           +[(f"scalar{d}",f"checkScalar packet {d}")for d in range(10)],
       "ActionsA":[(f"actA{d}",f"blockA {d}")for d in range(9)],
       "ActionsC":[(f"actC{d}",f"blockC {d}")for d in range(9)],
       "Silence":[(f"silent{d}",f"blockS {d}")for d in range(10)],
       "Products":[(f"product{d}_{e}",f"blockP {d} {e}") for d in range(10) for e in range(10-d)],
    }
    for g,receipts in groups.items():
        z=cfg([stem+"Data"])
        if g=="Products":
            z+="/-! Each grade pair is checked as an actual modular projection, not a sum of squares. -/\n"
        z+="".join(f"theorem {nm} : {ex}=true := by decide +kernel\n" for nm,ex in receipts)
        if g=="Moments":
            z+="\ntheorem next_star : bushResidual packet 10 = star := by decide +kernel\n"
            z+="theorem star_inv : star * starInv = 1 := by decide +kernel\n"
        write(g,z+tail)
    H=cfg([stem+g for g in groups]+["DIRKUniform"])
    H=H.replace("\n\n@[expose]","\nimport Mathlib.Tactic.IntervalCases\n\n@[expose]",1)
    for n0,to,head in [("stepA",9,"actA"),("stepC",9,"actC"),("silence",10,"silent")]:
        bc=f"block{head[-1]}" if head.startswith("act") else "blockS"
        H+=f"theorem {n0} (d : Nat) (hd : d < {to}) : {bc} d = true := by\n  interval_cases d\n"
        H+="".join(f"  · exact {head}{i}\n" for i in range(to))+"\n"
    for head,to,fun in [("primitive",9,"checkPrimitive"),("scalar",10,"checkScalar")]:
        H+=f"theorem {head}Receipt (d : Nat) (hd : d < {to}) : {fun} packet d = true := by\n  interval_cases d\n"
        H+="".join(f"  · exact {head}{i}\n" for i in range(to))+"\n"
    H+="theorem products (d e : Nat) (h : d+e < 10) : blockP d e = true := by\n  have hd : d < 10 := by omega\n  interval_cases d\n"
    for d in range(10):
        H+=f"  · have he : e < {10-d} := by omega\n    interval_cases e\n"
        H+="".join(f"    · exact product{d}_{e}\n" for e in range(10-d))
    H+="""
theorem receipts : Receipts 10 packet := by
  refine ⟨node,?_,?_,?_,?_,?_,scalarReceipt⟩
  · intro d hd i
    exact List.all_eq_true.mp (stepA d (by omega)) i (List.mem_finRange i)
  · intro d hd i
    exact List.all_eq_true.mp (stepC d (by omega)) i (List.mem_finRange i)
  · intro d e hd i j
    exact List.all_eq_true.mp (List.all_eq_true.mp (products d e hd) i
      (List.mem_finRange i)) j (List.mem_finRange j)
  · intro d hd
    exact primitiveReceipt d (by omega)
  · intro d hd i
    exact List.all_eq_true.mp (silence d hd) i (List.mem_finRange i)

def A : Matrix (Fin 11) (Fin 11) F := matrix packet
def b : Fin 11 → F := packet.b

theorem paid : HasOrder 10 A b := RingFlagReplay.order receipts

theorem lowerA : A.IsLowerTriangular := RingFlagReplay.lower packet

theorem next_unit : IsUnit (((bushyTree 11).factorial:F)*(b ⬝ᵥ Φ (bushyTree 11) A)-1) := by
  have hu : IsUnit (bushResidual packet 10) := by
    rw [next_star]
    exact IsUnit.of_mul_eq_one starInv star_inv
  rw [bushResidual,output_eq,node_eq receipts,Graded.row_apply] at hu
  have hf : (((bushyTree 11).factorial : ℕ) : F) = (11 : ℕ) := by decide +kernel
  have hg : ((11 : ℕ+) : ℕ)-1=10 := by decide +kernel
  rw [Φ_bushyTree, hf, hg]
  exact hu

/-- One literal width-eleven tableau gives order ten and a unit eleventh
bush over each nonzero ring of any characteristic dividing the combined modulus. -/
theorem exists_paid_of_dvd (R : Type*) [CommRing R] (n : Nat) [CharP R n]
    (h : n ∣ modulus) :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧
      IsUnit (((bushyTree 11).factorial:R)*(w ⬝ᵥ Φ (bushyTree 11) U)-1) := by
  let f := ZMod.castHom h R
  refine ⟨A.map f, f ∘ b, ?_, paid.map f, ?_⟩
  · intro i j hij
    change f (A i j)=0
    rw [lowerA hij, map_zero]
  · simpa only [map_sub,map_mul,map_natCast,map_one,RingHom.map_dotProduct,map_Φ] using
      next_unit.map f

theorem exists_exact_of_dvd (R : Type*) [CommRing R] [Nontrivial R] (n : Nat) [CharP R n]
    (h : n ∣ modulus) :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w := by
  obtain ⟨U,w,hL,hOrder,hUnit⟩ := exists_paid_of_dvd R n h
  refine ⟨U,w,hL,hOrder,?_⟩
  intro hNext
  rw [hNext (bushyTree 11) (by decide),sub_self] at hUnit
  exact hUnit.ne_zero rfl

theorem exists_exact_prime_in_list (K : Type*) [Field K] (p : Nat) [CharP K p]
    (hp : p ∈ primes) :
    ∃ (U : Matrix (Fin 11) (Fin 11) K) (w : Fin 11 → K),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd K p (prime_divides hp)

theorem exists_exact_char_59 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 59] :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd R 59 (prime_divides (by decide))

theorem exists_exact_char_3481 (R : Type*) [CommRing R] [Nontrivial R] [CharP R 3481] :
    ∃ (U : Matrix (Fin 11) (Fin 11) R) (w : Fin 11 → R),
      U.IsLowerTriangular ∧ HasOrder 10 U w ∧ ¬ HasOrder 11 U w :=
  exists_exact_of_dvd R 3481 squared_59_divides

theorem minimum_stages_floor {R : Type*} [CommRing R] [Nontrivial R] {s : Nat}
    {U : Matrix (Fin s) (Fin s) R} {w : Fin s → R}
    (hL : U.IsLowerTriangular) (ho : HasOrder 10 U w) : 11 ≤ s :=
  ho.dirk_uniform_stages hL (by decide)
"""
    write("",H+tail)

if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("source",type=Path)
    p.add_argument("out",type=Path)
    a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=True)
    emit(a.source,a.out)
