"""Exact localized 59-stage order-18 upper tableau from the fixed public charts."""
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

P=18
M=8
G=P-M-2
EXTRA=(59,739,2137,8179)
PAY=factorial(P)*prod(EXTRA)
SELECTED=tuple(map(Q,("-5","-3/2","-2/3","1/5","2/3","3/2")))
SOURCE_PINS = {
    "construct.py": "74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
    "weighted_regular.py": "f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571",
    "tableau-18-weighted.json": "adec0df152d14550aeb54fa8a095d6f3ad9974120f6a5f6f49b903affd389b61",
    "witness-18-weighted.json": "2837187821c0a812b5119e5ad69e105feb5fdc19a5e907d50fafab26dd901147",
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


def small_det(a):
    if not a: return 1
    return sum((-1)**j*a[0][j]*small_det([r[:j]+r[j+1:] for r in a[1:]])
               for j in range(len(a)))


def paid_matrix_inverse(entries):
    # The public six sites are fixed. The selected five-row minors are
    # certified explicitly, with no assumptions on residue-field weights.
    assert len(entries)==6 and all(len(r)==5 for r in entries)
    D=lcm(*(q.denominator for r in entries for q in r))
    M=[[int(D*q) for q in r] for r in entries]
    util=module(HELPER,"rk_rational_finite_59")
    g=0
    blocks=[]
    coeff=[]
    fixed=((0,1,2,3,4),(0,1,2,3,5),(0,1,2,4,5),(1,2,3,4,5))
    for ix in fixed:
        block=[M[k] for k in ix]
        d=small_det(block)
        if not d: continue
        unpaid=abs(d)
        while (p:=gcd(unpaid,PAY))>1: unpaid//=p
        g,u,v=util.egcd(g,unpaid)
        coeff=[u*q for q in coeff]+[Q(v*unpaid,d)]
        blocks.append((ix,block,d,unpaid))
    assert g==1 and len(blocks)==4, (g,[(x,e) for x,_,_,e in blocks])
    assert sum(c*d for c,(_,_,d,_) in zip(coeff,blocks,strict=True))==1
    ret=[[Q(0)]*6 for _ in range(5)]
    for alpha,(ix,block,d,_) in zip(coeff,blocks,strict=True):
        for j in range(5):
            for i,k in enumerate(ix):
                sub=[r[:j]+r[j+1:] for h,r in enumerate(block) if h!=i]
                ret[j][k]+=D*alpha*(-1)**(i+j)*small_det(sub)
    info={"scale":str(D),
          "rows":[list(ix) for ix,_,_,_ in blocks],
          "signed_determinants":[str(d) for _,_,d,_ in blocks],
          "unpaid_cores":[str(d) for _,_,_,d in blocks],
          "blend":[str(c) for c in coeff]}
    return ret,info


def variant_text(src):
    s=patch_once(src,
       "def build(rk, seed, order, verify_reads=False):\n    rk.PAID = factorial(order)",
       "def build(rk, seed, order, payment, capture, paid_matrix_inverse):\n"
       "    assert order==18\n    rk.PAID = payment\n    verify_reads=False")
    s=patch_once(s,"            split = [F(-1,3)] if order==18 else []","            split = []")
    s=patch_once(s,
       "        basis = [mul([z]*j+h,rk.nodal(split_nodes)) for j in range(6)]",
       "        basis = [[z]*j+h for j in range(7)]")
    s=patch_once(s,
       "        axes = [adjust(poly) for k,poly in enumerate(basis) if k not in (pivot_a,pivot_b)]\n"
       "        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]\n"
       "        rows = paid_left_inverse(entries)",
       "        axes = [adjust(poly) for k,poly in enumerate(basis) if k not in (pivot_a,pivot_b)]\n"
       "        entries = [[weight[a]*vv(q,a) for q in axes] for a in early]\n"
       "        rows,minor_cert = paid_matrix_inverse(entries)")
    s=patch_once(s,"    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])",
                   "    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])\n"
                   "    capture(locals())")
    s=patch_once(s,
       "    assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]",
       "    assert len(out)==59")
    return s


def construct(source):
    for name,sha in SOURCE_PINS.items():
        assert digest(source/name)==sha, name
    rk=module(source/"construct.py","rk_order18_published_upper")
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    private=variant_text((source/"weighted_regular.py").read_text())
    state={}
    with tempfile.TemporaryDirectory(prefix="rk-order18-localized-upper-",dir="/tmp") as d:
        target=Path(d)/"weighted_localized_candidate.py"
        target.write_text(private)
        upper=module(target,"rk_localized59_constructor")
        literal=upper.build(rk,seed,P,PAY,state.update,paid_matrix_inverse)
    assert tuple(state["early"])==SELECTED and not state["split"]
    assert (len(state["fo_prefix"]),len(state["reverse"]),len(state["l"]))==(22,22,75)
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
    assert all(x.denominator==1 for x in a)

    # The published homogeneous grade-seven expression, followed by
    # w=C³V and its next graft C⁸Aw. Only these fixed trees are evaluated.
    alpha=(136080,-272160,204120,-34020)
    def word_tree(word):
        t=()
        for op in reversed(word):
            t=(t,) if op=="A" else t+((),)
        return t
    ts=[word_tree("CCCCCCCCACCC"+w) for w in ("ACCACC","ACCAAC","ACCCCC","CCCCCC")]
    graft=[]
    for t,v in zip(ts,alpha,strict=True):
        assert size(t)==19 and t_fact(t)%19==0
        q=Q(v,t_fact(t)//19)
        graft.append([t,str(q),str(defects(t))])
    assert sum(Q(q) for _,q,_ in graft)==0
    assert sum(Q(q)*Q(z) for _,q,z in graft)==19
    bush=((),)*18
    clock_sum=Q(sum(a*x for a,x in zip(bz,phi(bush),strict=True)),e*d**18)
    assert 19*clock_sum-defects(bush)==1
    return {
      "literal_witness":literal_witness,"blend":old_digits,
      "balanced_graft":graft,"bush_defect":str(defects(bush)),"bush_raw":str(clock_sum)
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
    assert (nf,ns,len(rep))==(22,75,59)
    D_R=pad([rk.read(st["ro"],st["rr"],lambda k,j=j:int(k==j))[0]
             for j in range(G)],st["base_n"])
    mu_poly=[st["mean"]([Q(0)]*j+[Q(1)]) for j in range(G+1)]
    ell_poly=[st["ell_value"]([Q(0)]*j+[Q(1)]) for j in range(G+1)]
    return {
        "schema":"rk-weighted-upper-structural-localized-59-v1","p":P,"m":M,"g":G,
        "nf":nf,"ns":ns,"final":len(rep),"extra_inversions":EXTRA,
        "source_hashes":SOURCE_PINS,
        "A_unfolded":enc(a,2),"beta":enc(beta,1),"clocks":enc(clocks,1),
        "N":enc(norm,2),"L":enc(l,2),"T":enc(t,2),"DF":enc(df,2),
        "weighted_receivers":[ns-1-(st["base_n"]+k) for k in range(len(st["early"]))],
        "interpolation_sites":[str(x) for x in SELECTED],
        "selected_masses":[str(st["weight"][x]) for x in SELECTED],
        "measurement":enc(st["entries"],2),"left_inverse":enc(st["rows"],2),
        "receive_axes":enc(pad([q for q,_ in st["rules"]],G+1),2),
        "minor_certificate":st["minor_cert"],
        "reverse_decoder":enc(D_R,2),
        "mu_poly":enc(mu_poly,1),"ell_poly":enc(ell_poly,1),
        "constraint_pivots":[st["pivot_a"],st["pivot_b"]],
        "constraint_determinant":str(st["det"]),
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
    w=next_receipts(literal,json.loads((args.source/"witness-18-weighted.json").read_bytes()))
    h=module(HELPER,"rk_generic_receipt")
    out=structural_receipt(rk,st,literal,w,h)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/"tableau-18-localized-59.json").write_text(json.dumps(literal,indent=2)+"\n")
    (args.out/"receipt-18-localized-59.json").write_text(json.dumps(out,separators=(",",":"),sort_keys=True)+"\n")
    print(f"order {P}: {out['nf']} + {out['ns']} virtual, {out['final']} physical; "
          f"dual widths {[len(x['cols']) for x in out['dual']]}; "
          f"forward widths {[len(x['cols']) for x in out['forward']]}")
    print("exact next defects",[v for _,v in w["literal_witness"]])
    print("selected masses",out["selected_masses"])


if __name__=="__main__":
    main()
