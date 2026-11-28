#!/usr/bin/env python3
"""Create integer coefficient/cache data for the review-kernel proof.

The cache is untrusted. Lean checks each join and action used to cover the
ordinary trees, plus all output moments and the next-order tree defect.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from itertools import zip_longest
from math import lcm, ceil
from pathlib import Path
import json

NS="RKResearch.Certified.ERK10RationalSixteen"
PREFIX="RKCert.ReviewedNative."


def numerical(source):
    obj=json.loads(source.read_text())
    A=[list(map(F,row)) for row in obj["A"]]
    b=list(map(F,obj["b"]))
    D=lcm(*(u.denominator for r in A for u in r),*(u.denominator for u in b))
    return D, [tuple(int(D*x) for x in r) for r in A], tuple(int(D*x) for x in b)


def cache(D,A,b):
    dot=lambda u,v:sum(x*y for x,y in zip(u,v) if x and y)
    V=[(1,)*16]
    W=[tuple(map(sum,A))]
    G=[1]
    cuts=[0,1]
    join={}
    for n in range(2,11):
        found={}
        for i,ni in enumerate(G[:cuts[-1]]):
            for j in range(cuts[n-ni-1],cuts[n-ni]):
                v=tuple(a*c for a,c in zip(V[i],W[j]))
                if v not in found:
                    found[v]=len(V)
                    V.append(v)
                    G.append(n)
                    if n<10:
                        W.append(tuple(n*dot(row,v) for row in A))
                join[i,j]=found[v]
        cuts.append(len(V))
    assert all(n*dot(b,v)==D**n for n,v in zip(G,V))
    return V,W,G,cuts,join


def array(xs):
    return "#["+", ".join(map(str,xs))+"]"


def array2(rows):
    return "#[\n  "+",\n  ".join(array(r) for r in rows)+" ]"


def write(dst,file,imports,data,extra=""):
    (dst/(file+".lean")).write_text(
        "module\n\n"+"\n".join("public import "+PREFIX+i for i in imports)+extra+
        "\n\n@[expose] public section\n\n"
        "/-! Generated exact certificate; see the literal tableau and generator. -/\n\n"
        "namespace "+NS+"\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 50000\n\n"
        +data+"\n\nend "+NS+"\n"
    )


def emit_data(out,D,A,b,V,W,G,cuts,join):
    n,m=len(V),len(W)
    body=f"""def D : ℤ := {D}
abbrev Count := {n}
abbrev ActCount := {m}
def tag (i : ℕ) : Fin Count := ⟨i%Count,Nat.mod_lt _ (by decide)⟩
def gradeTable : Array ℕ := {array(G)}
def grade (i : Fin Count) : ℕ := gradeTable[i.val]!
def cut (q : ℕ) : ℕ := ({array(cuts)} : Array ℕ)[q]!
def aRows : Array (Array ℤ) := {array2(A)}
def bVec : Array ℤ := {array(b)}
def cVec : Array ℤ := {array(map(sum,A))}
def aTable : Array (List ℕ) := {array(str([j for j,v in enumerate(r) if v]) for r in A)}
def bTable : List ℕ := {[j for j,v in enumerate(b) if v]}
def joinTable : Array (Array ℕ) :=
  {array2([[join[i,j] for j in range(cuts[10-G[i]])] for i in range(m)])}
def join (i j : Fin Count) : Fin Count := tag ((joinTable[i.val]!)[j.val]!)
def aNum (i j : Fin 16) : ℤ := if j < i then (aRows[i.val]!)[j.val]! else 0
def bNum (i : Fin 16) : ℤ := bVec[i.val]!
def cNum (i : Fin 16) : ℤ := cVec[i.val]!
def aSupport (i : Fin 16) : List (Fin 16) := (aTable[i.val]!).map fun j => ⟨j%16,Nat.mod_lt _ (by decide)⟩
def bSupport : List (Fin 16) := bTable.map fun j => ⟨j%16,Nat.mod_lt _ (by decide)⟩
"""
    for name,data,export in (("profile",V,"V"),("action",W,"W")):
        k=16
        body+=f"\ndef {name}Bucket : ℕ → Array (Array ℤ)\n"
        body+="\n".join(f"  | {i//k} => "+array2(data[i:i+k]) for i in range(0,len(data),k))
        body+="\n  | _ => #[]\n"
        body+=f"\ndef {export} (i : Fin Count) (x : Fin 16) : ℤ := "
        body+=f"(({name}Bucket (i.val/{k}))[i.val%{k}]!)[x.val]!\n"
    write(out,"ERK10RationalSixteenData",[],body,"\npublic import RKResearch.ERK")


def emit_checks(out,n,m,G,cuts):
    prefix="ERK10RationalSixteen"
    suites=[("Grade","gradeOK","Count",n,64,4),
            ("Join","joinOK","ActCount",m,4,2),
            ("Action","actOK","ActCount",m,4,3),
            ("Pay","payOK","Count",n,16,4)]
    outmods=[]
    master=[]
    early=((cuts[5]+3)//4)*4
    assert early%4==0
    prec=[]
    joinproof=[]
    for i in range(early):
        right=cuts[10-G[i]]
        parts=[(start,min(12,right-start)) for start in range(0,right,12)]
        imps=[]
        for h in range(0,len(parts),2):
            mod=prefix+"JoinSlice"+str(i)+"At"+str(parts[h][0])
            chunk=parts[h:h+2]
            body="\n".join(f"theorem jSlice{i}At{st} : joinSlice (tag {i}) {st} {cnt} = true := by decide +kernel"
                           for st,cnt in chunk)
            write(out,mod,[prefix+"JoinPoint"],body)
            imps.append(mod)
        prec.extend(imps)
        mod=prefix+"JoinValue"+str(i)
        proof=f"theorem joinValue{i} : joinOK (tag {i}) = true := by\n"
        proof+="  apply finishJoin (by decide +kernel : cut (10-grade (tag "+str(i)+")) = "+str(right)+")\n"
        proof+=f"  have H0 := jSlice{i}At0\n"
        for j,(st,cnt) in enumerate(parts[1:],1):
            proof+=f"  have H{j} := glueJoin H{j-1} jSlice{i}At{st}\n"
        proof+=f"  exact H{len(parts)-1}\n"
        write(out,mod,imps,proof)
        prec.append(mod)
        joinproof.append(mod)
    for lab,test,bound,limit,width,chl in suites:
        blocks=ceil(limit/width)
        mods=[]
        for start in range(0,blocks,chl):
            mod=prefix+"Check"+lab+str(start)
            body=[]
            imports=[prefix+"Core"]
            for j in range(start,min(blocks,start+chl)):
                hdr=f"theorem check{lab}{j} : checkBlock {test} {bound} {j} {width} = true := by "
                if lab=="Join" and j*width<early:
                    xs=list(range(j*width,(j+1)*width))
                    terms=", ".join(f"tag {i}" for i in xs)
                    body.append(hdr.rstrip()+f"\n  change ([{terms}].all joinOK) = true\n"
                                +"  simp only [List.all_cons, List.all_nil, Bool.and_self, "+
                                ", ".join("joinValue"+str(i) for i in xs)+"]")
                    imports.extend(joinproof[i] for i in xs)
                else:
                    body.append(hdr+"decide +kernel")
            write(out,mod,imports,"\n".join(body))
            mods.append(mod)
        outmods.append(mods)
        master.append(f"theorem all{lab} (i : ℕ) (hi : i < {blocks}) :\n"
                      f"    checkBlock {test} {bound} i {width} = true := by\n"
                      "  interval_cases i\n"+
                      "\n".join(f"  · exact check{lab}{j}" for j in range(blocks)))
    master.append("""
theorem receipts : Receipts where
  grade i := checkBlock_covers (by decide) (by decide) allGrade i i.isLt
  join i hi := checkBlock_covers (by decide) (by decide) allJoin i hi
  act i hi := checkBlock_covers (by decide) (by decide) allAction i hi
  pay i := checkBlock_covers (by decide) (by decide) allPay i i.isLt
""")
    allmods=[x for row in zip_longest(*outmods) for x in row if x is not None]
    write(out,prefix+"Checks",allmods,"\n\n".join(master),"\nimport Mathlib.Tactic.IntervalCases")
    return [prefix+"JoinPoint",*prec,*allmods]


if __name__=="__main__":
    p=ArgumentParser()
    p.add_argument("--source",type=Path,default=Path(__file__).with_name("tableau.json"))
    p.add_argument("--emit",type=Path,required=True)
    p.add_argument("--modules",type=Path,required=True)
    a=p.parse_args()
    D,A,b=numerical(a.source)
    V,W,G,cuts,join=cache(D,A,b)
    print("Classes by grade:",[y-x for x,y in zip(cuts,cuts[1:])])
    print("Profiles:",len(V),"Actions:",len(W),"Joins:",len(join))
    emit_data(a.emit,D,A,b,V,W,G,cuts,join)
    a.modules.write_text("\n".join(emit_checks(a.emit,len(V),len(W),G,cuts))+"\n")
