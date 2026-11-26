"""Exact no-zero-split order-20 upper tableau from a pinned public architecture."""
from fractions import Fraction as Q
from functools import cache
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from math import factorial,gcd,lcm,prod
from pathlib import Path
import argparse
import json
import sys
import tempfile

P=20
M=9
G=P-M-2
EXTRA=(37,911,15901,1120673,86775809,1034700137)
PAY=factorial(P)*prod(EXTRA)
SELECTED=tuple(sorted(Q(sign*j,6) for sign in (-1,1) for j in (4,5,7,8)))
SOURCE_PINS = {
    "construct.py": "74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
    "weighted_regular.py": "f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571",
    "tableau-20-weighted.json": "a08c3229cd058edf41eb91241852166fcdf2f0712d10a850539c07b278bb9cb3",
    "witness-20-weighted.json": "85fe4ade0371313977dbeb5c5adf2c990871e25ef4beb9103684989c3830a841",
    "../erk-eleven-twelve-moment-splice/paid9-seed.json":
      "8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
}
HELPER = Path(__file__).with_name("receipt_arithmetic.py")
HELPER_PIN = "d01c8df19abe1deba54160afc9f63ea0d997af97f4901607d450db7f4b959f16"
sys.dont_write_bytecode=True


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def module(path,name):
    spec=spec_from_file_location(name,path)
    out=module_from_spec(spec)
    sys.modules[name]=out
    spec.loader.exec_module(out)
    return out


def patch_once(s,old,new):
    if s.count(old)!=1:
        raise ValueError(f"pinned architecture changed: {old[:80]}")
    return s.replace(old,new)


def variant_text(src):
    s=patch_once(src,
        "def build(rk, seed, order, verify_reads=False):\n    rk.PAID = factorial(order)",
        "def build(rk, seed, order, selected, payment, capture):\n"
        "    assert order==20\n    rk.PAID = payment\n    verify_reads = False")
    s=patch_once(s,
        "            split = [z]\n            old = {2*sum(row)-1 for row in reverse}",
        "            split = []\n            old = {2*sum(row)-1 for row in reverse}")
    s=patch_once(s,
        "        axes = [[z]*j+h for j in range(1,8)]\n"
        "        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]\n"
        "        rows = paid_left_inverse(entries)",
        "        axes = [[z]*j+h for j in range(8)]\n"
        "        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]\n"
        "        assert len(selected)==8 and set(selected).issubset(early)\n"
        "        rows = [[z]*len(early) for _ in axes]\n"
        "        for a in selected:\n"
        "            pivot = weight[a]*vv(h,a)\n"
        "            assert rk.unit(pivot), ('unpaid selected weighted pivot',a,pivot)\n"
        "            i = early.index(a)\n"
        "            for j, coeff in enumerate(cardinal(selected,a)):\n"
        "                rows[j][i] = coeff/pivot")
    s=patch_once(s,"    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])",
                   "    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])\n"
                   "    capture(locals())")
    s=patch_once(s,
        "    assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]",
        "    assert len(out)<=71, ('literal count',len(out))")
    return s


def construct(source):
    for name,sha in SOURCE_PINS.items():
        assert digest(source/name)==sha, name
    rk=module(source/"construct.py","rk_order20_published_upper")
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    private=variant_text((source/"weighted_regular.py").read_text())
    state={}
    with tempfile.TemporaryDirectory(prefix="rk-order20-localized-upper-") as d:
        target=Path(d)/"weighted_localized_candidate.py"
        target.write_text(private)
        upper=module(target,"rk_localized71_constructor")
        literal=upper.build(rk,seed,P,SELECTED,PAY,state.update)
    return rk,state,json.loads(literal)


def next_receipts(literal,pinned_witness):
    aa=[[Q(v) for v in r] for r in literal["A"]]
    bb=[Q(v) for v in literal["b"]]
    d=lcm(*(x.denominator for r in aa for x in r))
    e=lcm(*(x.denominator for x in bb))
    AZ=[[(j,int(x*d)) for j,x in enumerate(r) if x] for r in aa]
    bz=[int(x*e) for x in bb]

    def tree_key(t):
        return tuple(map(tree_key,t))

    @cache
    def size(t):
        return 1+sum(map(size,t))

    @cache
    def t_fact(t):
        return size(t)*prod(map(t_fact,t))

    @cache
    def primitive(t):
        v=phi(t)
        return tuple(sum(a*v[j] for j,a in row) for row in AZ)

    @cache
    def phi(t):
        ch=[primitive(u) for u in t]
        return tuple(prod(a[i] for a in ch) for i in range(len(bz)))

    def defects(t):
        assert size(t)==P+1
        scale=e*d**P
        val=t_fact(t)*sum(a*x for a,x in zip(bz,phi(t),strict=True))-scale
        return Q(val,scale)

    previous_shapes=[tree_key(t) for t,_ in pinned_witness]
    literal_witness=[(t,str(defects(t))) for t in previous_shapes]
    denom=lcm(*(Q(v).denominator for _,v in literal_witness))
    from_helper=module(HELPER,"rk_generic_receipt")
    g,u,v=from_helper.egcd(*(int(Q(x)*denom) for _,x in literal_witness))
    assert g!=0
    a=[Q(denom*u,g),Q(denom*v,g)]
    old_digits=from_helper.encode(a,1,PAY)

    # Preserve the published activation of the leading mode using only the
    # four named rooted grafts; this is not a tree enumeration.
    components = [
        ("CACCACCACC",136080), ("CACCACCAAC",-272160),
        ("CACCACCCCC",204120), ("CACCCCCCCC",-34020),
    ]
    def word_tree(word):
        t=()
        for op in reversed(word):
            t=(t,) if op=="A" else t+((),)
        return t
    grafts=[((word_tree(word),)+((),)*9,coeff) for word,coeff in components]
    graft_combination=[(t,str(Q(coeff,t_fact(t))),str(defects(t))) for t,coeff in grafts]
    assert sum(Q(coeff,t_fact(t)) for t,coeff in grafts)==0
    assert sum(Q(c)*Q(v) for _,c,v in graft_combination)==1
    from_helper.encode([Q(c) for _,c,_ in graft_combination],1,PAY)
    return {
      "literal_witness":literal_witness, "blend":old_digits,
      "balanced_graft":graft_combination,
    }


def structural_receipt(rk,st,literal,witness,h):
    fo,fr,ff=st["fo"],st["fr"],st["fo_prefix"]
    rev,beta_reverse,taps=st["l"],st["beta"],st["weighted_columns"]
    fwd,clocks,merged=st["fwd"],st["x"],st["mergers"]
    assert st["fgrade"]==M and st["top"]==G and not st["split"]
    nf,ns=len(ff),len(rev)
    n=nf+ns
    z=Q(0)
    pad=lambda rows,n: [r+[z]*(n-len(r)) for r in rows]
    a=pad(fwd,n)
    af=[row[:nf] for row in a[:nf]]
    t=[row[nf:] for row in a[nf:]]
    l=[r[::-1] for r in pad(rev,ns)[::-1]]
    beta=beta_reverse[::-1]
    n_rev=[[r[j] if j<len(r) and j<st["base_n"] else taps.get((i,j),z)
              for j in range(ns)] for i,r in enumerate(rev)]
    norm=[v[::-1] for v in n_rev[::-1]]
    df=pad([rk.read(fo,fr,lambda k,j=j: int(k==j))[0] for j in range(M)],nf)
    df += [[z]*nf for _ in range(P-M)]
    alias={i-1:j-1 for i,j in merged}
    rep=[i for i in range(n) if i not in alias]
    pos={v:i for i,v in enumerate(rep)}
    owner=[pos[alias.get(i,i)] for i in range(n)]

    ds=lcm(*(x.denominator for x in clocks),*(x.denominator for r in l for x in r))
    c0=[int(ds*x) for x in clocks]
    l0=[[int(ds*x) for x in r] for r in l]
    dual=[{"cols":[["1"]*ns]}]
    ub=[[1]*ns]
    for _ in range(G):
        ci=[[x*y for x,y in zip(c0,b,strict=True)] for b in ub]
        li=[h.matvec(l0,b) for b in ub]
        vn,coords=h.modular_bilattice(ci+li,PAY)
        dual[-1]["C_scale_cols"]=h.ints(coords[:len(ub)])
        dual[-1]["L_scale_cols"]=h.ints(coords[len(ub):])
        dual.append({"cols":h.ints(vn)})
        ub=vn

    fs=lcm(*(x.denominator for row in af for x in row))
    af0=[[int(fs*x) for x in row] for row in af]
    local={1:[[1]*(nf+1)]}
    forward=[{"cols":[["1"]*(nf+1)]}]
    for n0 in range(2,M+2):
        options=[h.native_attach(af0,fs,n0-k,v,w)
                 for k in range(1,n0) for v in local[k] for w in local[n0-k]]
        basis,coords=h.modular_bilattice(options,PAY)
        local[n0]=basis
        forward.append({"cols":h.ints(basis),"attach_coords":h.ints(coords)})

    pay=lambda d: h.require_paid(d,PAY)
    enc=lambda x,i: h.encode(x,i,PAY)
    return {
        "schema":"rk-weighted-upper-structural-localized-v1","p":P,"m":M,"g":G,
        "nf":nf,"ns":ns,"final":len(rep),"extra_inversions":EXTRA,
        "source_hashes":SOURCE_PINS,
        "A_unfolded":enc(a,2),"beta":enc(beta,1),"clocks":enc(clocks,1),
        "N":enc(norm,2),"L":enc(l,2),"T":enc(t,2),"DF":enc(df,2),
        "weighted_receivers":[ns-1-(st["base_n"]+k) for k in range(len(st["early"]))],
        "interpolation_sites":[str(x) for x in SELECTED],
        "selected_masses":[str(st["weight"][x]) for x in SELECTED],
        "measurement":enc(st["entries"],2),"left_inverse":enc(st["rows"],2),
        "rep":rep,"owner":owner,
        "dual_scale":pay(ds),"dual":dual,"forward_scale":pay(fs),"forward":forward,
        "next":witness,
    }


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("out",type=Path)
    args=cli.parse_args()
    assert digest(HELPER)==HELPER_PIN
    rk,st,literal=construct(args.source)
    w=next_receipts(literal,json.loads((args.source/"witness-20-weighted.json").read_bytes()))
    h=module(HELPER,"rk_generic_receipt")
    out=structural_receipt(rk,st,literal,w,h)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/"tableau-20-localized-71.json").write_text(json.dumps(literal,indent=2)+"\n")
    (args.out/"receipt-20-localized-71.json").write_text(json.dumps(out,separators=(",",":"),sort_keys=True)+"\n")
    print(f"order {P}: {out['nf']} + {out['ns']} virtual, {out['final']} physical; "
          f"dual widths {[len(x['cols']) for x in out['dual']]}; "
          f"forward widths {[len(x['cols']) for x in out['forward']]}")
    print("exact next defects",[v for _,v in w["literal_witness"]])
    print("selected masses",out["selected_masses"])


if __name__=="__main__":
    main()
