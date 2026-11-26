"""Exact factorial-unit ERK12/25 from the fixed public grade-five charts."""
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

P=12
M=5
G=P-M-2
PAY=factorial(P)
SELECTED=tuple(map(Q,("-2/3","-1/6","1/6","1/3","1/2","2/3")))
SOURCE_PINS = {
    "construct.py": "74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
    "weighted_regular.py": "f0ab1a5026113602e6402ccf5bd5e6c1cd199e918ea285a74ebd16eb06d91571",
    "weighted_middle.py": "54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
    "tableau-11-weighted.json":"5e674b8cff3abc9d9a20f59a080be13665f8bddd3d58774949dc059cc993cce6",
    "tableau-12-weighted.json":"55f54bc0b997aaa06464b62642e477fed1db1d24d1fe14e382c2bf2bde1e0869",
    "tableau-13-weighted.json":"13c87f00e46c7e9615ff5fb2d1fc269cce4f99c64d9313601e4ea66024d0f369",
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
    # The public six sites are fixed. The two selected four-row minors are
    # certified explicitly, with no assumptions on residue-field weights.
    assert len(entries)==6 and all(len(r)==4 for r in entries)
    D=lcm(*(q.denominator for r in entries for q in r))
    M=[[int(D*q) for q in r] for r in entries]
    util=module(HELPER,"rk_rational_finite_59")
    g=0
    blocks=[]
    coeff=[]
    fixed=((0,1,2,5),(1,2,3,4))
    for ix in fixed:
        block=[M[k] for k in ix]
        d=small_det(block)
        if not d: continue
        unpaid=abs(d)
        while (p:=gcd(unpaid,PAY))>1: unpaid//=p
        g,u,v=util.egcd(g,unpaid)
        coeff=[u*q for q in coeff]+[Q(v*unpaid,d)]
        blocks.append((ix,block,d,unpaid))
    assert g==1 and len(blocks)==2, (g,[(x,e) for x,_,_,e in blocks])
    assert sum(c*d for c,(_,_,d,_) in zip(coeff,blocks,strict=True))==1
    ret=[[Q(0)]*6 for _ in range(4)]
    for alpha,(ix,block,d,_) in zip(coeff,blocks,strict=True):
        for j in range(4):
            for i,k in enumerate(ix):
                sub=[r[:j]+r[j+1:] for h,r in enumerate(block) if h!=i]
                ret[j][k]+=D*alpha*(-1)**(i+j)*small_det(sub)
    info={"scale":str(D),
          "rows":[list(ix) for ix,_,_,_ in blocks],
          "signed_determinants":[str(d) for _,_,d,_ in blocks],
          "unpaid_cores":[str(d) for _,_,_,d in blocks],
          "blend":[str(c) for c in coeff]}
    return ret,info


def prepare_both(rk,mid,p,vv,mul,add,scale,cardinal):
    assert p==12
    f=mid.prepare(rk,11,vv,mul,add,scale,cardinal)
    r=mid.prepare(rk,13,vv,mul,add,scale,cardinal)
    grid=sorted([Q(0)]+[s*Q(a) for a in ("1/6","1/3","1/2","2/3","1") for s in (-1,1)])
    old={2*sum(row)-1 for row in r[7]}
    early=[a for a in grid if a not in old]
    late=sorted(old-{Q(1),Q(-1)})
    assert tuple(early)==SELECTED and late==list(map(Q,("-1/2","-1/3","0")))
    return f[:7]+r[7:14]+(grid,[],early,late,0)


def left_cardinal(rk,site,a):
    assert site==list(map(Q,("-1/2","-1/3","0")))
    H=lambda a:1-a*a
    old=[x for x in site if x!=a]
    d=H(a)*prod(a-v for v in old)
    assert rk.unit(d)
    q=[x/d for x in rk.nodal(old)]+[Q(0)]
    hull=rk.nodal(site)
    assert len(hull)==4 and hull[2]==Q(5,6) and rk.unit(hull[2])
    r=[x-y*q[2]/hull[2] for x,y in zip(q,hull,strict=True)]
    return [x-y for x,y in zip(r+[Q(0)]*2,[Q(0)]*2+r,strict=True)]


def variant_text(src):
    s=patch_once(src,
       "def build(rk, seed, order, verify_reads=False):\n    rk.PAID = factorial(order)",
       "def build(rk, seed, order, capture, prepare_both, paid_matrix_inverse, left_cardinal):\n"
       "    assert order==12\n    rk.PAID = factorial(order)\n    verify_reads=False")
    s=patch_once(s,"        from weighted_middle import prepare\n","        prepare = prepare_both\n")
    s=patch_once(s,
       "    assert len(late)==(fgrade if order in (15,16) else fgrade-1)",
       "    assert len(late)==3")
    before="""    if order<17:
        axes = [[z]*j+boundary for j in range(top-len(boundary)+2)]
        rows = [[pin(q) for q in axes] for pin in old_pins]
        rows += [[vv(q,a) for q in axes] for a in split]
        rows += [[weight[a]*vv(q,a) for q in axes] for a in early]
        inverse = paid_left_inverse(rows)
        for i,row in enumerate(inverse):
            for j in range(len(axes)):
                assert sum(x*r[j] for x,r in zip(row,rows))==F(i==j)
        middle_rules = list(zip(axes,(dict(zip(split+early,row[len(old_pins):])) for row in inverse)))
        split_nodes = split"""
    after="""    if order<17:
        assert not split and len(old_pins)==1 and top==5
        p0=old_pins[0](boundary)
        assert p0==F(20,81) and rk.unit(p0)
        seeds=[[z]*j+boundary for j in range(1,5)]
        axes=[add(q,scale(boundary,-old_pins[0](q)/p0)) for q in seeds]
        entries=[[weight[a]*vv(q,a) for q in axes] for a in early]
        inverse,minor_cert=paid_matrix_inverse(entries)
        for i,row in enumerate(inverse):
            for j in range(len(axes)):
                assert sum(x*r[j] for x,r in zip(row,entries))==F(i==j)
        middle_rules = list(zip(axes,(dict(zip(early,row)) for row in inverse)))
        split_nodes = []"""
    s=patch_once(s,before,after)
    s=patch_once(s,"        e = mul(forward_factor,scale(cardinal(late,a),o/vv(forward_factor,a)))",
                   "        e = left_cardinal(rk,late,a)")
    s=patch_once(s,"    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])",
                   "    out,b,mergers = rk.merge(fwd,[z]*len(fo_prefix)+beta[::-1])\n"
                   "    capture(locals())")
    s=patch_once(s,"    if order==11:\n        assert (raw_stage(z),9) in mergers",
                   "    if order==12:\n        assert (raw_stage(z),9) in mergers")
    s=patch_once(s,
       "    assert len(out)=={11:23,12:26,13:30,14:33,15:40,16:45,17:53,18:60,19:66,20:72}[order]",
       "    assert len(out)==25")
    return s


def construct(source):
    for name,sha in SOURCE_PINS.items():
        assert digest(source/name)==sha, name
    rk=module(source/"construct.py","rk_order12_published_upper")
    mid=module(source/"weighted_middle.py","rk_order12_two_published_charts")
    private=variant_text((source/"weighted_regular.py").read_text())
    state={}
    prep=lambda rk,*args:prepare_both(rk,mid,*args)
    with tempfile.TemporaryDirectory(prefix="rk-order12-paired-upper-",dir="/tmp") as d:
        target=Path(d)/"weighted_paired_candidate.py"
        target.write_text(private)
        upper=module(target,"rk_paired25_constructor")
        literal=upper.build(rk,None,P,state.update,prep,paid_matrix_inverse,left_cardinal)
    assert tuple(state["early"])==SELECTED and not state["split"]
    assert (len(state["fo_prefix"]),len(state["reverse"]),len(state["l"]))==(9,8,33)
    return rk,state,json.loads(literal)


def next_receipts(literal):
    aa=[[Q(v) for v in r] for r in literal["A"]]
    bb=[Q(v) for v in literal["b"]]
    d=lcm(*(x.denominator for r in aa for x in r))
    e=lcm(*(x.denominator for x in bb))
    AZ=[[(j,int(x*d)) for j,x in enumerate(r) if x] for r in aa]
    bz=[int(x*e) for x in bb]

    @cache
    def size(t): return 1+sum(map(size,t))
    @cache
    def factorial_t(t): return size(t)*prod(map(factorial_t,t))
    @cache
    def primitive(t):
        v=phi(t)
        return tuple(sum(a*v[j] for j,a in row) for row in AZ)
    @cache
    def phi(t):
        ch=[primitive(u) for u in t]
        return tuple(prod(a[i] for a in ch) for i in range(len(bz)))
    def raw(t):
        assert size(t)==13
        return Q(sum(a*x for a,x in zip(bz,phi(t),strict=True)),e*d**12)
    def word(w):
        root=()
        for s in reversed(w): root=(root,) if s=="A" else root+((),)
        return root
    ts=[word("CCCCCACCCACC"),word("CCCCCACCCAAC")]
    zz=[raw(t) for t in ts]
    assert zz[0]-2*zz[1]==-Q(1,622080)
    fact=[factorial_t(t) for t in ts]
    assert all(n%13==0 for n in fact)
    z0,z1=[n*r-1 for n,r in zip(fact,zz,strict=True)]
    coeff=[Q(-622080,fact[0]//13),Q(1244160,fact[1]//13)]
    assert sum(coeff)==0 and sum(c*x for c,x in zip(coeff,[z0,z1],strict=True))==13
    bush=((),)*12
    bu=raw(bush); zd=13*bu-1
    vals=[z0,z1,zd]
    blend=[bu*w for w in coeff]+[Q(-1)]
    assert sum(x*u for x,u in zip(vals,blend,strict=True))==1
    util=module(HELPER,"rk_order12_pay")
    a=lcm(z0.denominator,z1.denominator)
    q,u,v=util.egcd(int(a*z0),int(a*z1))
    assert q==1 and a*(u*z0+v*z1)==1
    return {"graft":[[t,k,str(r),str(z)] for t,k,r,z in zip(ts,[1,-2],zz,vals[:2],strict=True)],
            "raw_output":str(zz[0]-2*zz[1]),"bush_raw":str(bu),"bush_defect":str(zd),
            "literal_witness":[[t,str(z)] for t,z in zip(ts,vals[:2],strict=True)],
            "blend":util.encode([u*a,v*a],1,PAY),
            "paid_graft_and_bush_blend":util.encode(blend,1,PAY)}


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
    assert (nf,ns,len(rep))==(9,33,25)
    D_R=pad([rk.read(st["ro"],st["rr"],lambda k,j=j:int(k==j))[0]
             for j in range(G)],st["base_n"])
    return {
        "schema":"rk-weighted-upper-structural-paired25-v1","p":P,"m":M,"g":G,
        "nf":nf,"ns":ns,"final":len(rep),
        "source_hashes":SOURCE_PINS,
        "A_unfolded":enc(a,2),"beta":enc(beta,1),"clocks":enc(clocks,1),
        "N":enc(norm,2),"L":enc(l,2),"T":enc(t,2),"DF":enc(df,2),
        "weighted_receivers":[ns-1-(st["base_n"]+k) for k in range(len(st["early"]))],
        "interpolation_sites":[str(x) for x in SELECTED],
        "selected_masses":[str(st["weight"][x]) for x in SELECTED],
        "measurement":enc(st["entries"],2),"left_inverse":enc(st["inverse"],2),
        "receive_axes":enc(pad(st["axes"],G+1),2),
        "minor_certificate":st["minor_cert"],"reverse_decoder":enc(D_R,2),
        "left_sites":list(map(str,st["late"])),
        "left_axes":enc([left_cardinal(rk,st["late"],x) for x in st["late"]],2),
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
    w=next_receipts(literal)
    h=module(HELPER,"rk_generic_receipt")
    out=structural_receipt(rk,st,literal,w,h)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/"tableau-12-factorial-25.json").write_text(json.dumps(literal,indent=2)+"\n")
    (args.out/"receipt-12-factorial-25.json").write_text(json.dumps(out,separators=(",",":"),sort_keys=True)+"\n")
    print(f"order {P}: {out['nf']} + {out['ns']} virtual, {out['final']} physical; "
          f"dual widths {[len(x['cols']) for x in out['dual']]}; "
          f"forward widths {[len(x['cols']) for x in out['forward']]}")
    print("exact next defects",[v for _,v in w["literal_witness"]])
    print("selected masses",out["selected_masses"])


if __name__=="__main__":
    main()
