"""Direct exact verification on one representative of every unordered rooted tree.
Only the standard library, integer recurrence for the supplied scaled tableau, no cached assertions.
Usage: python3 check.py tableau-9.json tableau-11.json
"""
import json,sys
from fractions import Fraction
from pathlib import Path

def verify(path):
    t=json.loads(Path(path).read_text());s,p=t['stages'],t['order']; M=t['a_integer']; w=t['b_integer'];d=t['a_denominator'];e=t['b_denominator']
    def require(ok,reason):
        if not ok:raise ValueError(reason)
    require(s==len(M)==len(w) and all(len(r)==s for r in M) and d>0 and e>0,'shape/scale')
    require(all(type(v) is int for r in M for v in r) and all(type(v) is int for v in w),'literal integers')
    require(all(M[i][i]==d and all(v==0 for v in M[i][i+1:]) for i in range(s)),'strict SDIRK, common diagonal 1')
    mat=[[(i,v) for i,v in enumerate(row) if v] for row in M]; w=[(i,v) for i,v in enumerate(w) if v]
    # List and number tree shapes in independent root-multiset order (children sorted by integer ID).
    # Integrated vectors and tree factorials are cached only at smaller grades.
    E=[]; facts=[]; orders=[]; checks=[]
    for n in range(1,p+1):
        end=len(orders); total=0
        def rooted(rem,lo,child_ids):
            if rem==0: yield child_ids;return
            for i in range(lo,end):
                m=orders[i]
                if m>rem:break
                yield from rooted(rem-m,i,child_ids+(i,))
        for children in rooted(n-1,0,()):
            v=[1]*s; fac=n
            for i in children:
                fac*=facts[i];v=[x*y for x,y in zip(v,E[i])]
            require(fac*sum(weight*v[i] for i,weight in w)==e*d**(n-1),('tree failed',n,children))
            if n<p:
                E.append([sum(v[i]*a for i,a in row) for row in mat]);facts.append(fac);orders.append(n)
            total+=1
        checks.append(total)
    clock=[sum(row) for row in M]
    defect=Fraction((p+1)*sum(a*clock[i]**p for i,a in w),e*d**p)-1
    require(bool(defect) and defect==Fraction(t['next_bush_defect']),'next bush')
    print(f"order {p}; {s} stages; diagonal 1; trees {checks}, total {sum(checks)}; cleared next-bush defect {defect}",flush=True)
if __name__=='__main__':
    for path in sys.argv[1:]:verify(path)
