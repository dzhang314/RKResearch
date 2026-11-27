"""Normalized modular flags and CRT merge of separately audited literal tableaux."""
from pathlib import Path
from math import gcd, prod
from collections import Counter
from argparse import ArgumentParser
import json

def calc(data):
    p=data["p"]; A=data["A"]; b=data["bvec"]; c=data["c"]
    comp=lambda a,b:tuple((x*y)%p for x,y in zip(a,b))
    sub=lambda a,b,k=1:tuple((x-k*y)%p for x,y in zip(a,b))
    powV=lambda d:tuple(pow(x,d,p) for x in c)
    act=lambda v:tuple(sum(x*y for x,y in zip(row,v))%p for row in A)
    dot=lambda v:sum(x*y for x,y in zip(b,v))%p
    assert len(A)==len(c)==len(b)==11 and list(map(len,A))==list(range(1,12))
    assert all(sum(row)%p==x for row,x in zip(A,c))
    def echelon(cols):
        E={}
        for v in cols:
            for j,w in sorted(E.items()):
                if v[j]:
                    v=sub(v,w,v[j])
            if any(v):
                i=next((i for i,t in enumerate(v) if t and gcd(t,p)==1),None)
                if i is None:
                    raise ValueError(("non-free grade",p,v))
                inv=pow(v[i],-1,p)
                v=tuple(x*inv%p for x in v)
                for j,w in E.items():
                    if w[i]: E[j]=sub(w,v,w[i])
                E[i]=v
        return sorted(E.items())
    grades=[[]]
    for d in range(1,10):
        arr=[sub(tuple(x*d%p for x in act(powV(d-1))),powV(d))]
        arr.extend(act(v) for _,v in grades[d-1])
        arr.extend(comp(c,v) for _,v in grades[d-1])
        arr.extend(comp(v,w) for j in range(1,d) for _,v in grades[j] for _,w in grades[d-j])
        E=echelon(arr)
        for v in arr:
            assert v==tuple(sum(v[j]*w[i] for j,w in E)%p for i in range(11))
        assert all(dot(v)==0 for _,v in E)
        assert (d+1)*dot(powV(d))%p==1
        grades.append(E)
    assert dot(powV(0))==1
    z=(11*dot(powV(10))-1)%p
    assert z==data["star"] and gcd(z,p)==1
    return dict(A=A,b=b,c=c,p=p,star=z,starInv=pow(z,-1,p),flags=grades)

def combine(packets):
    moduli=[P["p"] for P in packets]; N=prod(moduli)
    def crt(xs):
        m=[(N//q)*pow(N//q,-1,q) for q in moduli]
        x=sum(t*mi for t,mi in zip(xs,m))%N
        assert all(x%q==a for a,q in zip(xs,moduli))
        return x
    def nested(xs):
        if isinstance(xs[0],list):
            assert all(len(a)==len(xs[0]) for a in xs)
            return [nested(x) for x in zip(*xs)]
        return crt(xs)
    m=max
    flags=[m(len(P["flags"][d]) for P in packets) for d in range(10)]
    zero=(0,)*11
    selectors=[]
    bases=[]
    for d,r in enumerate(flags):
        sels=[]; bs=[]
        for j in range(r):
            basis=[]; piv=[]
            for P in packets:
                if j>=len(P["flags"][d]):
                    k,w=11,zero
                else:
                    k,w=P["flags"][d][j]
                basis.append(w)
                piv.append(k)
            bs.append([crt(vals) for vals in zip(*basis)])
            sels.append([(i,crt([int(k==i) for k in piv])) for i in sorted(set(piv)-{11})])
        selectors.append(sels);bases.append(bs)
    return dict(modulus=N,moduli=moduli,A=nested([P["A"] for P in packets]),
      b=nested([P["b"] for P in packets]),c=nested([P["c"] for P in packets]),
      star=crt([P["star"] for P in packets]),
      starInv=crt([P["starInv"] for P in packets]),
      sizes=flags,basis=bases,selectors=selectors)

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--seeds",type=Path,required=True)
    ap.add_argument("--literals",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args(); a.out.mkdir(parents=True,exist_ok=True)
    s=json.loads(a.seeds.read_text());t=json.loads(a.literals.read_text())
    recs=[dict(p=P["p"],A=P["A"],c=P["c"],bvec=P["b"],star=P["scaled_order_11_star_defect"]) for P in t]
    assert len(recs)==32 and [P["p"] for P in recs]==[z[0] for z in s["seeds"]]
    seed59=s["examples"][0]; assert seed59["p"]==59
    assert all(seed59[k]==recs[0][k] for k in ["p","A","bvec","c","star"])
    seedSq=s["examples"][1]; assert seedSq["p"]==59**2
    Qs=[calc(P) for P in recs]
    print("seed moduli", [P["p"] for P in Qs])
    print("flag rank profiles",Counter(tuple(len(F) for F in P["flags"]) for P in Qs))
    print("flag pivot profiles",Counter(tuple(tuple(j for j,_ in F) for F in P["flags"]) for P in Qs))
    qSq=calc(seedSq)
    merged=combine([qSq]+Qs[1:])
    print("CRT modulus",merged["modulus"],"basis ranks",merged["sizes"],
      "selectors max terms", max(len(T) for S in merged["selectors"] for T in S))
    for n,rec in [("mod59",combine([Qs[0]])),("mod3481",combine([qSq])),("tableau-crt",merged)]:
        (a.out/(n+".json")).write_text(json.dumps(rec,indent=2)+"\n")
    exact=dict(primes=recs,extra_lift=seedSq)
    (a.out/"specialized-tableaux.json").write_text(json.dumps(exact,indent=2)+"\n")

if __name__=="__main__": main()
