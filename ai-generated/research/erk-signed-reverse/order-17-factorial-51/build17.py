"""Exact construction of the factorial-unit, 51-stage order-17 upper tableau."""
import argparse
from functools import cache
from design17 import *
from design17 import T as HIGH
EARLY=E
FILENAME="tableau-17-factorial-51.json"
RFILE="receipt-17-factorial-51.json"

def row_for_x(D,x):
    return [sum(a*x**(j+1)/(j+1) for j,a in enumerate(v)) for v in zip(*D,strict=True)]
def eval_chart(D,x):
    return [peval(col,x) for col in zip(*D,strict=True)]
def word(w,t):
    for s in reversed(w):
        t=(t,) if s=="A" else t+((),)
    return t
def next_data(A,b):
    @cache
    def phi(t):
        kids=[[dot(r,phi(c)) for r in A] for c in t]
        return tuple(prod(v[i] for v in kids) for i in range(len(b)))
    def size(t):return 1+sum(map(size,t))
    def fact(t):return size(t)*prod(map(fact,t))
    cand=("CCCCCCCA","CCCCCCAA","AAAAAAAA","CAAAAAAA","CCCCACAA","AACCCCCA","CCCCCAAA","ACCCCCAA")
    suffix=("CCCACCACC","CCCACCAAC","CCCACCCCC","CCCCCCCCC")
    graft=[]
    for prefix in cand:
        terms=[];raw=[]
        for u,k in zip(suffix,(136080,-272160,204120,-34020),strict=True):
            t=word(prefix+u,())
            assert size(t)==P+1
            v=dot(b,phi(t)); r=fact(t)*v-1
            terms.append([t,k,str(v),str(r)])
            raw.append(k*v)
        assert sum(Q(k,fact(t)) for t,k,_,_ in terms)==0
        graft.append(dict(prefix=prefix,terms=terms,raw=str(sum(raw))))
    def blend(v):
        den=lcm(*(x.denominator for x in v));g=0; C=[]
        for x in v:
            g,a,b0=ar.egcd(g,int(x*den));C=[a*y for y in C]+[b0]
        if unit(Q(g,den)):
            # Fractions are allowed since p+1=16 is paid, even when the gcd is not 1.
            r=[Q(den*x,g) for x in C]
            assert dot(r,v)==1 and all(unit(x.denominator) for x in r)
            return list(map(str,r))
    for i,j in combinations(range(len(graft)),2):
        m=[graft[i],graft[j]]
        raw=[Q(o["raw"]) for o in m]
        z=blend(raw)
        if z is None:continue
        for (g0,n0,x),(g1,n1,y) in combinations([(i0,j0,Q(e[3])) for i0,o in enumerate(m) for j0,e in enumerate(o["terms"])],2):
            t=blend([x,y])
            if t is not None:
                bush=((),)*P;brow=dot(b,phi(bush))
                return dict(grafts=m,raw_blend=z,picked=[[g0,n0,str(x)],[g1,n1,str(y)]],
                            blend=t,bush_output=str(brow),bush_defect=str((P+1)*brow-1))
    raise AssertionError(("No next pair",[(o["prefix"],o["raw"]) for o in graft]))

def build(source):
    des=design(source,False)
    rk,FA,fd,RA,d0=[des[k] for k in ("rk","FA","FD","RA","D0")]
    q,K,w,mask=[des[k] for k in ("q","k","weight","mask")]
    J,Jrec=des["jt"],des["rt"]
    assert J is not None,Jrec
    nf,k=len(FA),len(RA)
    assert nf==22 and k==14
    X0=lambda a:eval_chart(d0,(O+a)/2)
    I0=lambda a:row_for_x(d0,(O+a)/2)
    U0,eta0,elo=des["X"],des["jp"][0],des["rp"]
    lo=k+len(EARLY)
    EE=[[Z]*lo,[Z]*lo]
    for j,(a,h) in enumerate(zip(EARLY,eta0,strict=True)):
        ca=w[a]*h
        for e in EE:
            for i,v in enumerate(X0(a)):
                e[i]-=ca*v
        EE[0][k+j]=ca;EE[1][k+j]=h
    eta,etaN=EE;assert sum(eta)==0
    D=lambda a:add(pad(X0(a),lo),sc(eta,peval(q,a)))
    DN=lambda a:add(pad(X0(a),lo),sc(etaN,peval(q,a)))
    lift=lambda a,coef:add(pad(I0(a),lo),sc(eta,peval(K,a)+coef))
    liftN=lambda a,coef:add(pad(I0(a),lo),sc(etaN,peval(K,a)+coef))
    ll=hull(S); C=mul(H,ll)
    assert all(sum(w[a]*peval(C,a)*a**j*mask[a] for a in LIVE)==0 for j in range(3))
    cs={a:sc(card(S,a),O/peval(H,a)) for a in S}
    phiS={a:-sum(w[b]*peval(mul(H,cs[a]),b)*mask[b] for b in LIVE) for a in S}
    q0=ll+[Z];q1=[Z]+ll
    (a,b),(c,d)=[[dot(r,z) for z in (q0,q1)] for r in PINS]
    assert (a,b,c,d)==(Q(10,3),Q(12),Q(0),Q(7,3))
    U=a*d-b*c;assert U==Q(70,9) and unit(U)
    ES={}
    for u,p in cs.items():
        p=pad(p,7)
        e,f=[-dot(r,p) for r in PINS]
        out=add(p,add(sc(q0,(d*e-b*f)/U),sc(q1,(a*f-c*e)/U)))
        assert all(dot(i,out)==0 for i in PINS)
        ES[u]=mul(H,out)
    QG=q
    V,X=des["V"],des["MT"]
    lr=[list(r) for r in RA]+[I0(a) for a in EARLY]
    nr=[list(r) for r in lr]
    beta=[O]*k+[w[a] for a in EARLY]; lab=[2*sum(r,Z)-O for r in RA]+list(EARLY)
    lr.extend(lift(a,mask[a]) for a in HIGH); nr.extend(liftN(a,mask[a]) for a in HIGH)
    beta.extend(w[a] for a in HIGH);lab.extend(HIGH)
    for row in RA: lr.append(list(row));nr.append(list(row));beta.append(-O);lab.append(2*sum(row,Z)-O)
    for a in GRID:
        if a not in LIVE:lr.append(lift(a,0));nr.append(liftN(a,0));beta.append(w[a]);lab.append(a)
    for a in S:
        Gs=[mean(mul(ES[a],prim(v))) for v in V]+[Z]
        taps=[dot(Gs,u) for u in zip(*J,strict=True)]
        rr,NN=pad(lift(a,phiS[a]),k+len(LIVE)),pad(liftN(a,phiS[a]),k+len(LIVE))
        for j,(x,t) in enumerate(zip(LIVE,taps,strict=True)):
            ca=w[x]*t;rr[k+j]+=ca;NN[k+j]+=t
            for i,(u,v) in enumerate(zip(D(x),DN(x),strict=True)):
                rr[i]-=ca*u; NN[i]-=ca*v
        lr.extend((rr,lift(a,0))); nr.extend((NN,liftN(a,0)))
        beta.extend((O,-O));lab.extend((a,a))
    ns=len(lr);assert ns==55
    L=[pad(r,ns) for r in lr]; N=[pad(r,ns) for r in nr]
    assert all(sum(r)==(O+a)/2 for r,a in zip(L,lab,strict=True))
    assert all(L[i][j]==beta[j]*N[i][j] for i in range(ns) for j in range(ns))
    xx=[(O-a)/2 for a in reversed(lab)]
    bb=beta[::-1];L=[r[::-1] for r in reversed(L)];N=[r[::-1] for r in reversed(N)]
    T=[[bb[j]*N[j][i] for j in range(ns)] for i in range(ns)]
    A=[pad(r,nf+ns) for r in FA]
    Ef=[eval_chart(fd,x) for x in xx]
    for i,(x,t) in enumerate(zip(xx,T,strict=True)):
        af=[a-dot(t,u) for a,u in zip(row_for_x(fd,x),zip(*Ef,strict=True),strict=True)]
        assert not any(t[i:]); A.append(af+t)
    W,B,merges=rk.merge([a[:i] for i,a in enumerate(A)],[Z]*nf+bb)
    mp={i-1:j-1 for i,j in merges}; rep=[i for i in range(nf+ns) if i not in mp]
    pos={i:j for j,i in enumerate(rep)}; own=[pos[mp.get(i,i)] for i in range(nf+ns)]
    B0=[[dict(v).get(j,Z) for j in range(len(W))] for v in W]
    assert len(B0)==len(B)==51,(len(B0),merges)
    den=lcm(*(x.denominator for r in B0 for x in r),*(x.denominator for x in B))
    assert unit(den)
    lit=dict(A=[[str(x) for x in r[:i]] for i,r in enumerate(B0)],b=list(map(str,B)),
             coefficient_common_denominator=str(den))
    nexts=next_data(B0,B)
    AF=[row[:nf] for row in A[:nf]]
    df=lcm(*(x.denominator for row in AF for x in row))
    dd=lcm(*(x.denominator for row in L for x in row),*(x.denominator for x in xx))
    AFn=[[int(df*v) for v in row] for row in AF]
    Ln=[[int(dd*v) for v in row] for row in L]
    cc=[int(dd*v) for v in xx]
    dual=[dict(cols=ar.ints([[1]*ns]))];U=[[1]*ns]
    for _ in range(G):
        V0,loc=ar.modular_bilattice([[i*j for i,j in zip(cc,u,strict=True)] for u in U]+[ar.matvec(Ln,u) for u in U],PAY)
        dual[-1]["C_scale_cols"]=ar.ints(loc[:len(U)]); dual[-1]["L_scale_cols"]=ar.ints(loc[len(U):])
        dual.append(dict(cols=ar.ints(V0))); U=V0
    F={1:[[1]*(nf+1)]};ff=[dict(cols=ar.ints(F[1]))]
    for size in range(2,M+3):
        F[size],loc=ar.modular_bilattice([ar.native_attach(AFn,df,size-a,v,u)
                  for a in range(1,size) for v in F[a] for u in F[size-a]],PAY)
        ff.append(dict(cols=ar.ints(F[size]),attach_coords=ar.ints(loc)))
    pack=lambda x,n:ar.encode(x,n,PAY)
    rc=dict(schema="rk-weighted-upper-two-tier-v1",p=P,m=M,g=G,nf=nf,ns=ns,final=len(B),
            source_hashes=SOURCES,rep=rep,owner=own,A_unfolded=pack(A,2),N=pack(N,2),L=pack(L,2),
            T=pack(T,2),beta=pack(bb,1),clocks=pack(xx,1),DF=pack(fd+[[Z]*nf]*(P-M),2),
            old_reverse_decoder=pack(d0,2),pins=list(map(list,PINS)),
            scalar_sites=list(map(str,GRID)),pure_late_sites=list(map(str,S)),
            weighted_receivers=[ns-1-(k+i) for i in range(len(LIVE))],
            receiver_sites=list(map(str,LIVE)),receiver_masses=[str(w[v]) for v in LIVE],
            early_sites=list(map(str,EARLY)),high_sites=list(map(str,HIGH)),
            mask=pack([mask[a] for a in LIVE],1),eta=pack(eta,1),etaN=pack(etaN,1),
            Q=pack(QG,1),K=pack(K,1),compensators=pack([phiS[a] for a in S],1),
            top_left_basis=pack([pad(ES[a],M+1) for a in S],2),
            compensation_matrix=pack(des["W"],2),compensation_certificate=des["mi"],
            promotion_matrix=pack(U0,2),promotion_inverse=pack([eta0],2),promotion_minors=elo,
            measurement=pack(X,2),inverse=pack(J,2),measurement_minors=Jrec,
            dual_scale=ar.require_paid(dd,PAY),forward_scale=ar.require_paid(df,PAY),
            dual=dual,forward=ff,next=nexts)
    return lit,rc,merges

if __name__=="__main__":
    a=argparse.ArgumentParser(description=__doc__);a.add_argument("source",type=Path);a.add_argument("out",type=Path);b=a.parse_args()
    b.out.mkdir(exist_ok=True)
    lit,r,merges=build(b.source)
    for name,obj in ((FILENAME,lit),(RFILE,r)):
        path=b.out/name
        body=(json.dumps(obj,indent=2) if name==FILENAME else json.dumps(obj,separators=(",",":")))+"\n"
        path.write_text(body,encoding="utf8");print(name,sha256(body.encode()).hexdigest())
    print("raw",r["nf"],r["ns"],"final",r["final"],"prefix aliases",[(i,j) for i,j in merges if j<=r["nf"]])
    print("next",[(x["prefix"],x["raw"]) for x in r["next"]["grafts"]],r["next"]["raw_blend"])
    print("literal next",r["next"]["picked"],r["next"]["blend"],"bush",r["next"]["bush_defect"])
