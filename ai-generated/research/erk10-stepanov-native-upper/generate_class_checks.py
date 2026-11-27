#!/usr/bin/env python3
"""Generate standard-kernel check blocks for the normalized stage-vector cache."""
from pathlib import Path
from argparse import ArgumentParser
from math import ceil
from itertools import zip_longest
from generate_checks import write

SUITES = [
    ("ClassGrade", "cGradeOK", "ClassCount", 582, 64, 4),
    ("ClassJoin", "cJoinOK", "ActionCount", 274, 2, 4),
    ("ClassAction", "cActionOK", "ActionCount", 274, 4, 4),
    ("ClassPay", "cPayOK", "ClassCount", 582, 16, 4),
]


def generate(emit):
    lists = []
    hs = []
    for label,f,limit,count,width,terms in SUITES:
        n = ceil(count/width)
        chunks = []
        for first in range(0,n,terms):
            name = "ERK10StepanovCheck" + label + str(first)
            write(emit,name,["ERK10StepanovClassCore"],"\n".join(
                f"theorem check{label}{j} : cBlock {f} {limit} {j} {width} = true := by decide +kernel"
                for j in range(first,min(n,first+terms))))
            chunks.append(name)
        lists.append(chunks)
        hs.append(
            f"theorem check{label} (k : ℕ) (hk : k<{n}) : cBlock {f} {limit} k {width} = true := by\n"
            "  interval_cases k\n" + "\n".join(f"  · exact check{label}{j}" for j in range(n))
        )

    hs.append("""
theorem classReceipts : ClassReceipts where
  rootGrade := by decide +kernel
  rootProfile j := of_decide_eq_true (List.all_eq_true.mp
    (show (List.finRange 15).all (fun j => decide (cprofile (ctag 0) j = pack 1)) = true
      by decide +kernel) j (List.mem_finRange j))
  grade i := cBlock_covers (by decide) (by decide) checkClassGrade i i.isLt
  join i hi := cBlock_covers (by decide) (by decide) checkClassJoin i hi
  action i hi := cBlock_covers (by decide) (by decide) checkClassAction i hi
  pay i := cBlock_covers (by decide) (by decide) checkClassPay i i.isLt
  aSupportCert j := List.all_eq_true.mp
    (show (List.finRange 15).all aSupportOK = true by decide +kernel) j (List.mem_finRange j)
  bSupportCert := by decide +kernel
  clock j := List.all_eq_true.mp
    (show (List.finRange 15).all cClockReceipt = true by decide +kernel) j (List.mem_finRange j)
  bush := by decide +kernel
""")
    mods = [k for row in zip_longest(*lists) for k in row if k is not None]
    s = "\n\n".join(hs).replace("\ntheorem classReceipts", "\nopen ERKNestedRadicalReplay\n\ntheorem classReceipts")
    write(emit,"ERK10StepanovClassChecks",mods,s,"\nimport Mathlib.Tactic.IntervalCases")
    return mods


if __name__ == '__main__':
    parser=ArgumentParser()
    parser.add_argument('--emit',type=Path,required=True)
    args=parser.parse_args()
    print("\n".join(generate(args.emit)))
