#!/usr/bin/env python3
"""Emit exact rational echelon-basis certificates from a literal tableau."""
import argparse
import json
from fractions import Fraction as Q
from math import lcm
from pathlib import Path

def sub(u,w,k=1):return tuple(a-k*b for a,b in zip(u,w))
def mul(u,w):return tuple(a*b for a,b in zip(u,w))
def dot(u,w):return sum((a*b for a,b in zip(u,w) if a and b),Q(0))

def echelon(candidates):
    E={}
    for v in candidates:
        for p,z in sorted(E.items()):
            if v[p]:v=sub(v,z,v[p])
        j=next((i for i,x in enumerate(v)if x),None)
        if j is None:continue
        v=tuple(x/v[j]for x in v)
        for p,z in E.items():
            if z[j]:E[p]=sub(z,v,z[j])
        E[j]=v
    return sorted(E.items())

def make_data(record):
    n=record["stages"]
    A=[tuple(map(Q,r))+((Q(0),)*(n-len(r))) for r in record["A"]]
    b=tuple(map(Q,record["b"]))
    c=tuple(map(Q,record["c"]))
    assert tuple(map(sum,A))==c
    assert all(r[j]==0 for i,r in enumerate(A) for j in range(i+1,n))
    def act(u):return tuple(dot(r,u)for r in A)
    def power(d):return tuple(x**d for x in c)
    grade=[[]]
    sizes=[0]
    for d in range(1,10):
        V=[sub(tuple(d*x for x in act(power(d-1))),power(d))]
        V.extend(act(v)for _,v in grade[d-1])
        V.extend(mul(c,v)for _,v in grade[d-1])
        V.extend(mul(v,w)for j in range(1,d)for _,v in grade[j]for _,w in grade[d-j])
        E=echelon(V)
        for v in V:
            w=tuple(sum(v[p]*z[i]for p,z in E)for i in range(n))
            assert v==w
        assert all(dot(b,v)==0 for p,v in E)
        assert (d+1)*dot(b,power(d))==1
        grade.append(E);sizes.append(len(E))
    assert sum(b)==1
    failure=11*dot(b,power(10))-1
    assert failure
    if "eleventh_bush_defect" in record:
        assert failure==11*Q(record["eleventh_bush_defect"])
    D=lcm(*(x.denominator for row in A for x in row),*(x.denominator for x in b))
    return A,b,c,grade,sizes,D,failure

def emit(input,output,stem):
    record=json.loads(input.read_text())
    A,b,c,grade,sizes,D,failure=make_data(record)
    n=record["stages"]
    print(f"n={n}; homogeneous flag sizes {sizes}; literal denominator {D}; residual {failure}")
    frag=lambda s:(f"(-{abs(s.numerator)} : ℚ)" if s<0 else f"({s.numerator} : ℚ)")+(f"/{s.denominator}"if s.denominator!=1 else "") if s not in [0,1] else str(s)
    def array(xs):
        if isinstance(xs,(tuple,list)):return "#["+", ".join(map(array,xs))+"]"
        if isinstance(xs,Q):return frag(xs)
        return str(xs)
    pf=[ [p for p,_ in E]for E in grade]
    bf=[ [v for _,v in E]for E in grade]
    header=lambda imports:("module\n\n"+
       "".join(f"public import RKCert.ReviewedNative.{m}\n"for m in imports)+
       "\n@[expose] public section\n\n"
       f"namespace RKResearch.Certified.{stem}\n"
       "open RKResearch RationalFlagReplay\nopen scoped Matrix\n"
       "set_option maxHeartbeats 0\nset_option maxRecDepth 50000\n\n")
    footer=f"\nend RKResearch.Certified.{stem}\n"
    def write(suf,ss): (output/(stem+suf+".lean")).write_text(ss)
    txt=header(["RationalFlagReplay"])
    for tag,typ,v in [('a0','Array (Array ℚ)',A),('b0','Array ℚ',b),('c0','Array ℚ',c),
            ('sizes','Array ℕ',sizes),('pivots','Array (Array ℕ)',pf),('bases','Array (Array (Array ℚ))',bf)]:
        txt+=f"def {tag} : {typ} := {array(v)}\n\n"
    txt+=f"""def packet : Packet {n} where
  a i j := (a0.getD i.val #[]).getD j.val 0
  b i := b0.getD i.val 0
  clock i := c0.getD i.val 0
  size d := sizes.getD d 0
  pivot d i := ⟨((pivots.getD d #[]).getD i.val 0) % {n}, Nat.mod_lt _ (by decide)⟩
  basis d i j := ((bases.getD d #[]).getD i.val #[]).getD j.val 0

def blockA (d : ℕ) : Bool := (List.finRange (packet.size d)).all (checkA packet d)
def blockC (d : ℕ) : Bool := (List.finRange (packet.size d)).all (checkC packet d)
def blockS (d : ℕ) : Bool := (List.finRange (packet.size d)).all (checkSilent packet d)
def blockP (d e : ℕ) : Bool := (List.finRange (packet.size d)).all fun i =>
  (List.finRange (packet.size e)).all (checkProduct packet d e i)
"""
    write("Data",txt+footer)
    groups={
       "Moments":[("node","checkNode packet")]+[(f"primitive{d}",f"checkPrimitive packet {d}")for d in range(9)]
             +[(f"scalar{d}",f"checkScalar packet {d}")for d in range(10)],
       "ActionsA":[(f"actA{d}",f"blockA {d}")for d in range(9)],
       "ActionsC":[(f"actC{d}",f"blockC {d}")for d in range(9)],
       "Silence":[(f"silent{d}",f"blockS {d}")for d in range(10)],
    }
    groups["Products"]=[(f"product{d}_{e}",f"blockP {d} {e}")
                        for d in range(10) for e in range(10-d)]
    for g,L in groups.items():
        z=header([stem+"Data"])
        z+="".join(f"theorem {nm} : {ex} = true := by decide +kernel\n"for nm,ex in L)
        if g=="Moments":
            z+=f"theorem next_star : bushResidual packet 10 = {frag(failure)} := by decide +kernel\n"
        write(g,z+footer)
    H=header([stem+g for g in groups])
    H=H.replace("\n\n@[expose]", "\nimport Mathlib.Tactic.IntervalCases\n\n@[expose]",1)
    for n0,to,head in [("stepA",9,"actA"),("stepC",9,"actC"),("silence",10,"silent")]:
        bc=f"block{head[-1]}" if head.startswith("act") else "blockS"
        H+=f"theorem {n0} (d : ℕ) (hd : d < {to}) : {bc} d = true := by\n  interval_cases d\n"
        H+="".join(f"  · exact {head}{i}\n"for i in range(to))+"\n"
    for head,to,fun in [("primitive",9,"checkPrimitive"),("scalar",10,"checkScalar")]:
        H+=f"theorem {head}Receipt (d : ℕ) (hd : d < {to}) : {fun} packet d = true := by\n  interval_cases d\n"
        H+="".join(f"  · exact {head}{i}\n"for i in range(to))+"\n"
    H+="theorem products (d e : ℕ) (h : d+e < 10) : blockP d e = true := by\n  have hd : d < 10 := by omega\n  interval_cases d\n"
    for d in range(10):
        H+=f"  · have he : e < {10-d} := by omega\n    interval_cases e\n"
        H+="".join(f"    · exact product{d}_{e}\n"for e in range(10-d))
    H+=f"""
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

/-- The literal lower triangular rational matrix satisfies all reviewed
rooted-tree order conditions through ten. -/
theorem order_ten : HasOrder 10 (matrix packet) packet.b :=
  RationalFlagReplay.order receipts

theorem not_order_eleven : ¬ HasOrder 11 (matrix packet) packet.b :=
  no_order_succ receipts (by rw [next_star]; decide +kernel)

theorem lower_triangular : (matrix packet).IsLowerTriangular :=
  lower packet

theorem exists_exact :
    ∃ (A : Matrix (Fin {n}) (Fin {n}) ℚ) (b : Fin {n} → ℚ),
      A.IsLowerTriangular ∧ HasOrder 10 A b ∧ ¬ HasOrder 11 A b :=
  ⟨matrix packet,packet.b,lower_triangular,order_ten,not_order_eleven⟩
"""
    H+=footer+f"\n#print axioms RKResearch.Certified.{stem}.order_ten\n#print axioms RKResearch.Certified.{stem}.exists_exact\n"
    write("",H)
    return ["RationalFlagReplay",stem+"Data",*(stem+g for g in groups),stem]

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("input",type=Path)
    cli.add_argument("out",type=Path)
    cli.add_argument("--stem",default="DIRK10RationalTwelveFlagReplay")
    root=cli.parse_args()
    units=emit(root.input,root.out,root.stem)
    print("\n".join(units))
if __name__=="__main__":main()
