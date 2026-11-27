#!/usr/bin/env python3
"""Break expensive checks into named kernel receipts instead of one giant reduction.

Pass the frozen list of baseline modules not to rewrite, or omit that list
to use the low-memory proof layout for all blocks.
"""
from argparse import ArgumentParser
from pathlib import Path
from itertools import zip_longest
from math import ceil
from generate_checks import write
from generate_class_checks import SUITES

CUTS = [0,1,2,4,8,16,32,65,132,274,582]


def sharded(emit,legacy):
    parts=[]
    blocks=[]
    for label,f,limit,count,width,terms in SUITES:
        suite=[]
        for first in range(0,ceil(count/width),terms):
            nm="ERK10StepanovCheck"+label+str(first)
            if nm in legacy:
                continue
            methods=[]
            uses=["ERK10StepanovClassCore"]
            for k in range(first,min(ceil(count/width),first+terms)):
                actual=list(range(k*width,min(count,(k+1)*width)))
                proof=f"theorem check{label}{k} : cBlock {f} {limit} {k} {width} = true := by\n"
                for i in actual:
                    if f=="cJoinOK":
                        grade=next(j for j in range(1,11) if i<CUTS[j])
                        countJoin=CUTS[10-grade]
                    if f!="cJoinOK" or countJoin<=12:
                        proof+=f"  have h{i} : {f} (ctag {i}) = true := by decide +kernel\n"
                        continue
                    facts=[]
                    for start in range(0,countJoin,12):
                        ln=min(12,countJoin-start)
                        fact=f"joinSlice_{i}_{start}"
                        name=f"ERK10StepanovJoinSlice{i}At{start}"
                        write(emit,name,["ERK10StepanovJoinPoint"],
                              f"theorem {fact} : joinSlice (ctag {i}) {start} {ln} = true := by decide +kernel\n")
                        uses.append(name)
                        parts.append(name)
                        facts.append(fact)
                    combined=facts[0]
                    for fact in facts[1:]:
                        combined=f"(glueJoin {combined} {fact})"
                    proof+=f"  have h{i} : cJoinOK (ctag {i}) = true :=\n"
                    proof+=f"    finishJoin (by decide +kernel) {combined}\n"
                proof+=f"  change ({actual} : List ℕ).all (fun i => {f} (ctag i)) = true\n"
                proof+=("  simp only [List.all_cons,List.all_nil,Bool.and_self,"+
                        ",".join(f"h{i}" for i in actual)+"]\n")
                methods.append(proof)
            write(emit,nm,uses,"\n\n".join(methods))
            suite.append(nm)
        blocks.append(suite)
    return parts,[part for row in zip_longest(*blocks) for part in row if part is not None]


if __name__ == "__main__":
    p=ArgumentParser()
    p.add_argument("--emit",type=Path,required=True)
    p.add_argument("--legacy",type=Path)
    p.add_argument("--parts",type=Path,required=True)
    p.add_argument("--blocks",type=Path,required=True)
    args=p.parse_args()
    legacy=set(args.legacy.read_text().splitlines()) if args.legacy else set()
    parts,blocks=sharded(args.emit,legacy)
    args.parts.write_text("\n".join(parts)+"\n")
    args.blocks.write_text("\n".join(blocks)+"\n")
