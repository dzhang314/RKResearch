#!/usr/bin/env python3
"""Generate standalone Lean Euclidean traces of the published unit receipts."""
from pathlib import Path
import argparse,json

def add(a,b,p,s=1):
    t=[0]*max(len(a),len(b))
    for i,v in enumerate(a):t[i]=v%p
    for i,v in enumerate(b):t[i]=(t[i]+s*v)%p
    while t and not t[-1]:t.pop()
    return t
def mul(a,b,p):
    if not a or not b:return []
    t=[0]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b):t[i+j]=(t[i+j]+v*w)%p
    return t
def divrem(a,b,p):
    q=[0]*max(0,(len(a)-len(b)+1));a=a[:]
    while len(a)>=len(b) and a:
        j=len(a)-len(b)
        f=a[-1]*pow(b[-1],-1,p)%p
        q[j]=f
        a=add(a,[0]*j+[f*x%p for x in b],p,-1)
    return q,a
def bez(f,g,p):
    a,b=f,g; u,v=[1],[0]; r,s=[0],[1]
    while b:
        q,c=divrem(a,b,p)
        a,b=b,c;u,v=v,add(u,mul(q,v,p),p,-1);r,s=s,add(r,mul(q,s,p),p,-1)
    assert len(a)==1
    z=pow(a[0],-1,p)
    u=[a*z%p for a in u]; r=[a*z%p for a in r]
    assert add(mul(u,f,p),mul(r,g,p),p)==[1]
    return u,r

def fmt(a,br="["):
    return br+", ".join(map(str,a))+"]"

def render(inp):
    data=next(row for row in json.loads(inp.read_text()) if row["prime"]==1009)
    p=1009
    anchor=data["parameter"]
    assert len(anchor)==37 and anchor[-1]==1 and len(data["units"])==8
    raws=[(name,p,anchor,gate) for name,gate in sorted(data["units"].items())]
    raws.append(("quadratic_remainders",p,*data["quadratic"]))
    assert [len(g) for g in data["quadratic"]]==[9,10]
    A=[]
    for n,(label,p,f,g) in enumerate(raws):
        bez(f,g,p)
        polys=[f,g]; quotients=[]
        while polys[-1]:
            j,k=polys[-2:]
            q,r=divrem(j,k,p)
            assert add(mul(q,k,p),r,p)==j
            quotients.append(q)
            polys.append(r)
        assert len(polys[-2])==1 and polys[-2][0]
        section=f"Pair{n}"
        def nm(i):return f"p{i}"
        T=[f"-- Expanded receipt: {label}.","namespace "+section,""]
        for i,h in enumerate(polys):
            T.append(f"def {nm(i)} : List Nat := {fmt(h)}")
        j=len(polys)-2
        T+=["",f"private theorem tail{j} : CheckedEuclid {p} {nm(j)} {nm(j+1)} :=",
            f"  CheckedEuclid.done {nm(j)} (by decide) (by decide)"]
        for i in range(j-1,-1,-1):
            T+=[f"private theorem tail{i} : CheckedEuclid {p} {nm(i)} {nm(i+1)} :=",
                f"  CheckedEuclid.step (q := {fmt(quotients[i])}) (r := {nm(i+2)})",
                f"    (by decide_cbv) tail{i+1}"]
        T+=["",f"theorem euclid : CheckedEuclid {p} {nm(0)} {nm(1)} := tail0",
            f"theorem degreesPreserved : {nm(0)}.length = {len(f)} ∧ {nm(1)}.length = {len(g)} ∧",
            f"    {nm(0)}.getLastD 0 % {p} = {f[-1]} ∧ {nm(1)}.getLastD 0 % {p} = {g[-1]} := by decide",
            "",f"end {section}"]
        A.append("\n".join(T))
    return """import Lean

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.UniformChartUnitArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- The only possible proper prime divisors of 1009 would be at most 31. -/
theorem certifyPrime : ((List.range 30).map (· + 2)).all (fun q => 1009 % q != 0) = true := by decide

def addMod (p : Nat) (x y : List Nat) : List Nat :=
  match x, y with
  | [], ys => ys
  | xs, [] => xs
  | a::as, b::bs => ((a+b)%p)::addMod p as bs

def mulMod (p : Nat) (f g : List Nat) : List Nat :=
  match f with
  | [] => []
  | a::as => addMod p (g.map (fun b => a*b%p)) (0::mulMod p as g)

def normalize (f : List Nat) : List Nat :=
  (f.reverse.dropWhile (· == 0)).reverse

def pays (p : Nat) (f g q r : List Nat) : Bool :=
  g.getLastD 0 % p != 0 && r.length < g.length && normalize r == r &&
  normalize (addMod p (mulMod p q g) r) == f

/-- Linked decreasing polynomial remainder identities ending at a nonzero constant. -/
inductive CheckedEuclid (p : Nat) : List Nat → List Nat → Prop where
  | done (f : List Nat) : f.length = 1 → f.headD 0 % p ≠ 0 → CheckedEuclid p f []
  | step {f g q r : List Nat} :
      pays p f g q r = true → CheckedEuclid p g r → CheckedEuclid p f g

"""+ "\n\n".join(A) + """

#print axioms certifyPrime
"""+ "\n".join(f"#print axioms Pair{i}.euclid" for i in range(len(raws))) + """

end RKResearch.Certified.Graded.OrderTwelveFifteen.UniformChartUnitArithmetic
"""

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("out",type=Path)
    p.add_argument("--input",type=Path,default=Path(__file__).with_name("expanded.json"))
    args=p.parse_args()
    args.out.write_text(render(args.input))
