"""Select a paid asymmetric 19-site quadrature and a one-donor compression."""
from design17 import *
import design17 as common
P,M,G=19,9,8;PAY=factorial(P);common.PAY=PAY
BOUND=[O,O]
LEFT=[O,-O]
S=tuple(map(Q,("-2","-1/2","-1/3","0","1/3","1/2","2")))
S1=(-O,)+S
OLD=set(S)|{-O,O}
ELL=(-2487,-6632,1473,3928,5433,14488,9393,25048)
SOURCES={
 "construct.py":"74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
 "weighted_middle.py":"54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
 "../erk-eleven-twelve-moment-splice/paid9-seed.json":"8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
 "order-19-factorial-65/tableau-19-factorial-65.json":"e7b11babf332b7ac23e2ec9d12dd7552eaa5921492411915cf2128640eec4df5",
}

def chart_inputs(source):
    for f,sha in SOURCES.items():assert sha256((source/f).read_bytes()).hexdigest()==sha,f
    rk=mod(source/"construct.py","rk_new_ctr_19_64")
    mid=mod(source/"weighted_middle.py","rk_new_mid_19_64");rk.PAID=PAY
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    FA,fo,fr=rk.long(9,False,seed)
    FD=[pad(rk.read(fo,fr,lambda j,i=i:Q(i==j))[0],len(FA)) for i in range(M)]
    raw,rops,rrows,g,pin7,pin7_row,*_=mid.prepare(rk,15,peval,mul,add,sc,card)
    assert (len(FA),len(raw),g)==(27,15,7)
    old_sites=[v for v in S if v!=Q(-1,3)]
    assert len(old_sites)==6
    # Retain five of the six added old p19 reads, in the same order.
    last2=list(reversed(old_sites))
    for drop in last2:
        RA=[r.copy() for r in raw]
        sites=[v for v in old_sites if v!=drop]
        aims=rk.prepend((rops,rrows),[(O+x)/2 for x in sites],RA)
        RO=[rk.eval_at(Z)]+aims[0]+[lambda n:pin7([Q(comb(n,j),2**n) for j in range(n+1)])]
        RR=[rk.basis(0,len(RA))]+aims[1]+[pad(pin7_row,len(RA))]
        assert len(RA)==20 and {2*sum(r,Z)-O for r in RA}<=OLD
        q=hull([-O]+sites)
        dp=pin7(q)
        if not unit(dp):continue
        q=mul(q,[-pin7([Z]+q)/dp,O])
        y=[Z]*G
        for j,a in enumerate(q):y=add(y,[a*comb(j,i)*2**i*(-1)**(j-i) for i in range(j+1)])
        assert all(sum(op(i)*c for i,c in enumerate(y))==0 for op in RO)
        D0=[pad(rk.read(RO,RR,lambda j,i=i:Q(i==j))[0],len(RA)) for i in range(G-1)]
        yield rk,FA,FD,RA,D0,q,drop

def geom(style):
    old={z for n in (1,2,3,4,5,6,7,8,12) for z in (-n,n)}|{0}
    a,b=map(set,style);assert a<=old and not(b&old) and len(a)==len(b)
    G=sorted(Q(v,6) for v in (old-a)|b)
    assert len(G)==19 and OLD<=set(G)
    if not all(unit(b-a) for a,b in combinations(G,2)):return
    L=tuple(x for x in G if x not in OLD)
    return G,L

def design(source,show=False):
    for layout in (((8,-7),(9,-9)),((8,-7),(9,-10)),((8,-5),(9,-9)),((8,-4),(9,-10)),((7,-5),(9,-9)),((5,-1),(10,-9)),((8,7),(9,10)),((5,4),(9,10))):
        gg=geom(layout)
        if gg is None:continue
        GRID,LIVE=gg
        E=tuple(x for x in LIVE if x<Z); T=tuple(x for x in LIVE if x>Z)
        assert len(E)==len(T)==5
        w={a:mean(card(GRID,a)) for a in GRID}
        assert all(sum(w[a]*a**j for a in GRID)==mean([Z]*j+[O]) for j in range(P))
        cores=[abs(strip(w[a].numerator)) if w[a] else 0 for a in LIVE]
        if show:print("layout",layout,"masses pairwise-coprime unpaid cores?",all(gcd(a,b)==1 for a,b in combinations(cores,2)),cores,flush=True)
        if not all(cores):continue
        if any(gcd(a,b)>1 for a,b in combinations(cores,2)):continue
        for rk,FA,FD,RA,D0,q,drop in chart_inputs(source):
            k=prim(q)
            C=mul(LEFT,hull(S1))
            promote=[[w[a]*peval(q,a)] for a in E]
            jp,rp=paid_inv(promote)
            if jp is None:continue
            body=[[Z]*j+BOUND for j in range(8)]
            lead=[Z]*8+BOUND
            D=[[peval(f,a) for f in body] for a in E]
            D += [[sum(w[a]*peval(C,a)*a**j*peval(f,a) for a in LIVE) for f in body] for j in range(2)]
            b=[-peval(k,a)-peval(lead,a) for a in E]
            b += [-sum(w[a]*peval(C,a)*a**j*peval(lead,a) for a in LIVE) for j in range(2)]
            U=[list(col) for col in zip(*D,strict=True)]
            t,tr=paid_inv(U)
            coh=None
            if t:
                coeff=[dot(b,v) for v in zip(*t,strict=True)]
                assert [dot(a,coeff) for a in D]==b
                coh=add(lead,mul(BOUND,coeff))
                mask={a:peval(coh,a) for a in LIVE}
                assert all(mask[a]==-peval(k,a) for a in E)
                MT=[[w[a]*peval(f,a) for f in body]+[w[a]*mask[a]] for a in LIVE]
                j,rt=paid_inv(MT)
                assert j is not None
                info=("coherent monic mask",tr)
            else:
                W=[[w[a]*peval(C,a)*a**j for j in range(2)] for a in T]
                K,cert=paid_inv(W)
                if K is None:continue
                target=[sum(w[a]*peval(C,a)*a**j*peval(k,a) for a in E) for j in range(2)]
                Kt=list(zip(*K,strict=True));gs0=[dot(r,target) for r in Kt]
                Ker=[[Q(i==j)-dot(r,u) for j,u in enumerate(W)] for i,r in enumerate(Kt)]
                tries=[None]+[(i,t) for t in (1,-1,2,-2,3,-3) for i in range(len(T))]
                for trial in tries:
                    gs=gs0 if trial is None else [r+trial[1]*v[trial[0]] for r,v in zip(gs0,Ker,strict=True)]
                    mask={a:-peval(k,a) for a in E};mask.update(zip(T,gs,strict=True))
                    MT=[[w[a]*peval(f,a) for f in body]+[w[a]*mask[a]] for a in LIVE]
                    j,rt=paid_inv(MT)
                    if j:break
                if j is None:
                    if show:print("drop",drop,"failure",rt,flush=True)
                    continue
                info=(f"normal mask kernel adjustment {trial}",cert)
            assert all(sum(w[a]*peval(C,a)*a**r*mask[a] for a in LIVE)==0 for r in range(2))
            if show:
                print("PASS order19 geometry",layout,"drop",drop,"old gaps Q",q)
                print("grid",GRID,"pure top",S,"pure lower",S1)
                print("method",info[0],"promote cores",[(x,c) for x,_,c,_ in rp["terms"]],
                      "augmented cores",[(x,c) for x,_,c,_ in rt["terms"]])
                print("new weight denomin support",lcm(*(v.denominator for v in w.values())))
                print("coherent",coh)
            return dict(rk=rk,FA=FA,FD=FD,RA=RA,D0=D0,q=q,k=k,weight=w,mask=mask,X=promote,jp=jp,rp=rp,
                        V=body,MT=MT,jt=j,rt=rt,C=C,grid=GRID,live=LIVE,early=E,high=T,layout=layout,drop=drop,
                        coherent=coh,mask_proof=info)
    return None
if __name__=="__main__":
    z=design(REPO if len(sys.argv)==1 else Path(sys.argv[1]),True)
    assert z
