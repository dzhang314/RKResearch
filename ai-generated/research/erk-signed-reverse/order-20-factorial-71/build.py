"""A paired late projection on seven existing clocks: exact factorial-unit ERK20."""
import argparse
import json
import sys
from fractions import Fraction as Q
from functools import cache
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from math import factorial, gcd, lcm, prod
from pathlib import Path
from tempfile import TemporaryDirectory

import receipt_arithmetic as ar

P=20
M=G=9
PAY=factorial(P)
Z=Q(0)
O=Q(1)
RADII=tuple(Q(i,6) for i in (1,4,5,7,8))
OLD_PURE=tuple(map(Q,("-2","-1/2","-1/3","0","1/3","1/2","2")))
ELL=(-2487,-6632,1473,3928,5433,14488,9393,25048)
SOURCES={
    "construct.py":"74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
    "weighted_regular.py":"f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571",
    "tableau-20-weighted.json":"a08c3229cd058edf41eb91241852166fcdf2f0712d10a850539c07b278bb9cb3",
    "../erk-eleven-twelve-moment-splice/paid9-seed.json":
        "8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
}


def get(path,h):
    body=path.read_bytes()
    assert sha256(body).hexdigest()==h,path
    return body


def module(path,name):
    spec=spec_from_file_location(name,path)
    obj=module_from_spec(spec)
    sys.modules[name]=obj
    spec.loader.exec_module(obj)
    return obj


def pad(r,n):
    assert len(r)<=n
    return r+[Z]*(n-len(r))


def dot(u,v): return sum((a*b for a,b in zip(u,v,strict=True)),Z)

def h(x): return 1-x*x


def pure_basis(rk,sites,a):
    assert tuple(sites)==OLD_PURE
    p=rk.nodal([v for v in sites if a!=v])
    z=h(a)*prod(a-v for v in sites if a!=v)
    assert rk.unit(z)
    p=[v/z for v in pad(p,8)]
    hull=rk.nodal(sites)
    d=dot(ELL,hull)
    assert d==-31616 and rk.unit(d)
    q=[x-y*dot(ELL,p)/d for x,y in zip(p,hull,strict=True)]
    assert dot(ELL,q)==0
    return [x-y for x,y in zip(q+[Z,Z],[Z,Z]+q,strict=True)]


def measure_inverse(rk,sites,weights):
    assert tuple(sites)==tuple(sorted([sign*r for r in RADII for sign in (-1,1)]))
    # The five subgrids omit both members of one physical radius.
    blocks=[tuple(x for x in sites if abs(x)!=r) for r in RADII]
    mass=[prod(weights[x] for x in b) for b in blocks]
    d=lcm(*(v.denominator for v in mass))
    m=[int(v*d) for v in mass]
    g=0
    u=[]
    for x in m:
        g,a,b=ar.egcd(g,x)
        u=[a*v for v in u]+[b]
    assert g and rk.unit(Q(g,d))
    blend=[Q(d*v,g) for v in u]
    assert dot(blend,mass)==1
    A=[[Z]*len(sites) for _ in range(8)]
    for x,b in zip(blend,blocks,strict=True):
        for j,t in enumerate(sites):
            if t not in b:
                continue
            other=[v for v in b if v!=t]
            d0=h(t)*prod(t-v for v in other)
            assert rk.unit(d0)
            w=x*prod(weights[v] for v in other)/d0
            for i,c in enumerate(rk.nodal(other)):
                A[i][j]+=w*c
    assert all(rk.paid_integer(v.denominator) for row in A for v in row)
    return A,blend


def patch_text(s):
    def one(a,b):
        nonlocal s
        assert s.count(a)==1,a[:70]
        s=s.replace(a,b)
    one("def build(rk, seed, order, verify_reads=False):",
        "def build(rk, seed, order, capture, pure_basis, measure_inverse):\n"
        "    assert order==20\n    verify_reads=False")
    one("""            split = [z]
            old = {2*sum(row)-1 for row in reverse}
            early = [a for a in grid if a not in old and a!=F(1,6)]
            late = sorted((old-{-o,o})|{F(1,6)})""",
        """            split = []
            old = {2*sum(row)-1 for row in reverse}
            early = [a for a in grid if a not in old]
            late = sorted(old-{-o,o})""")
    one("    assert len(late)==(fgrade if order in (15,16) else fgrade-1)",
        "    assert len(late)==7")
    one("injection = {17:128,18:-256,19:512,20:-1024}[order]",
        "injection = {17:128,18:-256,19:512,20:0}[order]")
    one("""        axes = [[z]*j+h for j in range(1,8)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rows = paid_left_inverse(entries)""",
        """        axes = [[z]*j+h for j in range(8)]
        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]
        rows,blend = measure_inverse(rk,early,weight)""")
    one("        e = mul(forward_factor,scale(cardinal(late,a),o/vv(forward_factor,a)))",
        "        e = pure_basis(rk,late,a)")
    one("    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])",
        "    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])\n    capture(locals())")
    one("    assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]",
        "    assert len(out)==71")
    return s


def construct(source):
    for name,h in SOURCES.items(): get(source/name,h)
    r=module(source/"construct.py","rk_paired20_public")
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    state={}
    with TemporaryDirectory(prefix="rk-paired20-literal-",dir="/tmp") as d:
        path=Path(d)/"paired.py"
        path.write_text(patch_text((source/"weighted_regular.py").read_text()))
        v=module(path,"rk_paired20_factorial").build(r,seed,20,state.update,pure_basis,measure_inverse)
    assert state["fgrade"]==M and state["top"]==G and not state["split"]
    assert tuple(state["late"])==OLD_PURE and len(state["early"])==10
    return r,state,json.loads(v)


def word(w,t):
    for s in reversed(w): t=(t,) if s=="A" else t+((),)
    return t


def next_data(lit):
    A=[pad(list(map(Q,r)),71) for r in lit["A"]]
    b=list(map(Q,lit["b"]))
    assert len(A)==len(b)==71
    @cache
    def phi(t):
        ch=[tuple(dot(row,phi(x)) for row in A) for x in t]
        return tuple(prod(c[i] for c in ch) for i in range(len(b)))
    def size(t): return 1+sum(map(size,t))
    def fact(t): return size(t)*prod(map(fact,t))
    initial=("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    alpha=(136080,-272160,204120,-34020)
    prefixes=("CCCCCCCCAA","AAAAAAAAAA")
    expected=(Q(57445,1997706028032),Q(-39955501009,97088512962355200))
    weights=(-1910834258198528885450342400,-133516500603057781639372800)
    assert dot(weights,expected)==1
    grafts=[]
    for prefix,v in zip(prefixes,expected,strict=True):
        ts=[word(prefix+w,()) for w in initial]
        raw=[dot(b,phi(t)) for t in ts]
        assert all(size(t)==P+1 for t in ts)
        assert sum(Q(i*21,fact(t)) for i,t in zip(alpha,ts,strict=True))==0
        assert dot(alpha,raw)==v
        grafts.append({"prefix":prefix,"terms":[[t,a,str(x),str(fact(t)*x-1)]
                        for t,a,x in zip(ts,alpha,raw,strict=True)],"raw":str(v)})
    pair=[[t,df] for t,_,_,df in grafts[0]["terms"][:2]]
    x,y=[Q(v) for _,v in pair]
    D=lcm(x.denominator,y.denominator)
    G,u,v=ar.egcd(int(D*x),int(D*y))
    assert G==1
    blend=[u*D,v*D]
    assert dot(blend,[x,y])==1
    bush=((),)*20
    bush_output=dot(b,phi(bush))
    return {"grafts":grafts,"raw_blend":list(weights),
            "literal_witness":pair,"blend":ar.encode(blend,1,PAY),
            "bush_output":str(bush_output),"bush_defect":str(21*bush_output-1)}


def receipt(r,s,lit,w):
    nf,ns=len(s["fo_prefix"]),len(s["l"])
    assert (nf,ns,len(lit["A"]))==(27,87,71)
    m=nf+ns
    A=[pad(row,m) for row in s["fwd"]]
    AF=[row[:nf] for row in A[:nf]]
    T=[row[nf:] for row in A[nf:]]
    L=[pad(row,ns)[::-1] for row in reversed(s["l"])]
    N=[[row[j] if j<len(row) and j<s["base_n"] else s["weighted_columns"].get((i,j),Z)
         for j in range(ns)][::-1] for i,row in enumerate(s["l"])][::-1]
    b=s["beta"][::-1]
    c=s["x"]
    DF=[pad(r.read(s["fo"],s["fr"],lambda k,j=j: int(k==j))[0],nf)
        for j in range(M)]+[[Z]*nf for _ in range(P-M)]
    a={i-1:j-1 for i,j in s["mergers"]}
    rep=[i for i in range(m) if i not in a]
    k={i:j for j,i in enumerate(rep)}
    owner=[k[a.get(i,i)] for i in range(m)]
    dd=lcm(*(v.denominator for row in L for v in row),*(v.denominator for v in c))
    L0=[[int(dd*v) for v in row] for row in L]
    c0=[int(dd*v) for v in c]
    U=[[1]*ns]
    dual=[{"cols":ar.ints(U)}]
    for _ in range(G):
        V,cb=ar.modular_bilattice([[v*w for v,w in zip(c0,t,strict=True)] for t in U]+
                                  [ar.matvec(L0,t) for t in U],PAY)
        dual[-1]["C_scale_cols"]=ar.ints(cb[:len(U)])
        dual[-1]["L_scale_cols"]=ar.ints(cb[len(U):])
        dual.append({"cols":ar.ints(V)})
        U=V
    df=lcm(*(v.denominator for row in AF for v in row))
    AF0=[[int(df*v) for v in row] for row in AF]
    F={1:[[1]*(nf+1)]}
    forward=[{"cols":ar.ints(F[1])}]
    for size in range(2,M+2):
        V,cb=ar.modular_bilattice([ar.native_attach(AF0,df,size-a,x,y)
                  for a in range(1,size) for x in F[a] for y in F[size-a]],PAY)
        F[size]=V
        forward.append({"cols":ar.ints(V),"attach_coords":ar.ints(cb)})
    pack=lambda xs,n: ar.encode(xs,n,PAY)
    return dict(schema="rk-weighted-upper-structural-paired-v1",p=P,m=M,g=G,
                source_hashes=SOURCES,nf=nf,ns=ns,final=len(rep),owner=owner,rep=rep,
                A_unfolded=pack(A,2),N=pack(N,2),L=pack(L,2),T=pack(T,2),DF=pack(DF,2),
                beta=pack(b,1),clocks=pack(c,1),measurement=pack(s["entries"],2),left_inverse=pack(s["rows"],2),
                weighted_receivers=[ns-1-s["base_n"]-i for i in range(10)],
                receiver_sites=list(map(str,s["early"])),receiver_masses=[str(s["weight"][v]) for v in s["early"]],
                scalar_sites=list(map(str,s["grid"])),pure_late_sites=list(map(str,s["late"])),
                pure_late_basis=pack([pure_basis(r,s["late"],v) for v in s["late"]],2),
                ell=list(ELL),omission_blend=pack(s["blend"],1),
                dual_scale=ar.require_paid(dd,PAY),forward_scale=ar.require_paid(df,PAY),
                dual=dual,forward=forward,next=w)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("published_source",type=Path)
    parser.add_argument("out",type=Path)
    arg=parser.parse_args()
    r,s,lit=construct(arg.published_source)
    w=next_data(lit)
    cert=receipt(r,s,lit,w)
    arg.out.mkdir(parents=True,exist_ok=True)
    (arg.out/"tableau-20-factorial-71.json").write_text(json.dumps(lit,indent=2)+"\n")
    (arg.out/"receipt-20-factorial-71.json").write_text(json.dumps(cert,separators=(",",":"),sort_keys=True)+"\n")
    print("literal-stage count",len(lit["A"]),"common denominator",lit["coefficient_common_denominator"])
    print("two size-21 raw combinations",[u["raw"] for u in w["grafts"]])
    print("dual widths",[len(u["cols"]) for u in cert["dual"]])
    print("forward widths",[len(u["cols"]) for u in cert["forward"]])


if __name__=="__main__":main()
