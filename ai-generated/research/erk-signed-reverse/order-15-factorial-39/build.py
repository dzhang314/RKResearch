"""Exact construction of a new factorial-unit order-15 tableau and finite receipt."""
import sys,argparse,json
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,prod,lcm,gcd
from itertools import combinations
from importlib.util import spec_from_file_location,module_from_spec
from hashlib import sha256
from functools import cache
import receipt_arithmetic as ar

P,M,G=15,7,6
PAY=factorial(P)
Z=Q(0); O=Q(1)
H=[O,Z,-O]
BOUND=[O,-O]
QG=list(map(Q,(0,"1/9",0,"-10/9",0,1)))
LATE=tuple(map(Q,("-1","-1/3","-1/4","0","1/4","1/3")))
RADII=tuple(Q(n,12) for n in (1,2,3,4,6,8,12))
GRID=sorted({Z}|{s*x for s in (-1,1) for x in RADII})
LIVE=sorted(set(GRID)-set(LATE)-{O})
EARLY=tuple(v for v in LIVE if v<0)
HIGH=tuple(v for v in LIVE if v>0)
GAMMA=tuple(map(Q,("1861466503234151225967864868997375/253034496",
                   "4366027551468749673012329114405/279936",
                   "15273860333554473556291840344989/419904", "0")))
SOURCES={
 "construct.py":"74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
 "weighted_middle.py":"54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
 "tableau-15-weighted.json":"8ce24fdf663adcd88fa368eb89cef7e631d4b57762dd77512340d1f1132648eb",
}
FILENAME="tableau-15-factorial-39.json"
RFILE="receipt-15-factorial-39.json"

def mod(path,name):
    so=spec_from_file_location(name,path); m=module_from_spec(so);sys.modules[name]=m;so.loader.exec_module(m);return m
def pad(v,n):
    assert len(v)<=n; return list(v)+[Z]*(n-len(v))
def dot(a,b):return sum((x*y for x,y in zip(a,b,strict=True)),Z)
def vadd(a,b):
    n=max(len(a),len(b));return [x+y for x,y in zip(pad(a,n),pad(b,n),strict=True)]
def sc(a,b):return [x*b for x in a]
def peval(p,x):return sum((a*x**d for d,a in enumerate(p)),Z)
def mul(a,b):
    w=[Z]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):w[i+j]+=x*y
    return w
def mean(p):return sum((v/(i+1) for i,v in enumerate(p) if i%2==0),Z)
def prim(p):
    q=[Z]+[a/Q(2*(i+1)) for i,a in enumerate(p)]
    q[0]=-peval(q,-O);return q
def hull(xs):
    p=[O]
    for x in xs:p=mul(p,[-x,O])
    return p
def cardinal(xs,a):
    p=hull(x for x in xs if x!=a);d=peval(p,a)
    assert d and ar.strip_paid([d.numerator],PAY)[0] in (-1,1)
    return sc(p,O/d)
def det(rows):
    if not rows:return 1
    return sum((-1)**j*a*det([r[:j]+r[j+1:] for r in rows[1:]]) for j,a in enumerate(rows[0]) if a)
def unit(x):
    q=Q(x); n=abs(q.numerator)*q.denominator
    if not n:return False
    while (d:=gcd(n,PAY))!=1:n//=d
    return n==1
def paid_inv(MX):
    n=len(MX[0]); den=lcm(*(x.denominator for r in MX for x in r)); assert unit(den)
    MM=[[int(den*x) for x in r] for r in MX]; subs=[]
    for ids in combinations(range(len(MM)),n):
        A=[MM[i] for i in ids]; d=det(A); c=d
        if not c:continue
        while (u:=gcd(c,PAY))>1:c//=u
        subs.append((abs(c),ids,A,d,c))
    subs.sort(key=lambda a:(a[0],a[1])); chosen=[]; blend=[]; g=0
    for _,ids,A,d,c in subs:
        if gcd(g,c)==g:continue
        h,x,y=ar.egcd(g,c);chosen.append((ids,A,d,c));blend=[x*v for v in blend]+[y];g=h
        if g==1:break
    assert g==1
    rows=[[Z]*len(MM) for _ in range(n)]
    for (ids,A,d,core),alpha in zip(chosen,blend,strict=True):
        for i in range(n):
            for j in range(n):
                r=[[v for a,v in enumerate(row) if a!=i] for b,row in enumerate(A) if b!=j]
                rows[i][ids[j]]+=Q(den*alpha*core*(-1)**(i+j)*det(r),d)
    assert [[dot(r,c) for c in zip(*MX,strict=True)] for r in rows]==[[Q(i==j) for j in range(n)] for i in range(n)]
    return rows,dict(den=den,terms=[[list(ids),str(d),str(core),str(k)] for (ids,_,d,core),k in zip(chosen,blend,strict=True)])
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
    cand=("CCCCCCA","CCCCCAA","AAAAAAA","CAAAAAA","CCCACAA","AACCCCA")
    suffix=("CACCCACC","CACCCAAC")
    graft=[]
    for prefix in cand:
        terms=[];raw=[]
        for u,k in zip(suffix,(1,-2),strict=True):
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
    for file,d in SOURCES.items(): assert sha256((source/file).read_bytes()).hexdigest()==d,file
    rk=mod(source/"construct.py","rk_new_p15_tier_construct")
    mid=mod(source/"weighted_middle.py","rk_new_p15_tier_middle");rk.PAID=PAY
    ftable=mid.prepare(rk,P,peval,mul,vadd,sc,cardinal)
    FA,fo,fr,fgrade,fp,high=ftable[:6]
    RA,ro,rr,g=ftable[7:11]
    assert (len(FA),len(RA),fgrade,g)==(15,11,M,G)
    RA=RA[:-1];ro=ro[:-1]; rr=rr[:-1];nf,k=len(FA),len(RA)
    assert all(not any(v[k:]) for v in rr)
    rr=[v[:k] for v in rr]
    fd=[pad(rk.read(fo,fr,lambda j,i=i:Q(i==j))[0],nf) for i in range(M)]
    d0=[pad(rk.read(ro,rr,lambda j,i=i:Q(i==j))[0],k) for i in range(G-1)]
    X0=lambda a:eval_chart(d0,(O+a)/2)
    I0=lambda a:row_for_x(d0,(O+a)/2)
    old=sorted({2*sum(row,Z)-O for row in RA})
    assert old==[-O,-Q(1,3),Z,Q(1,3),O] and set(old)<=set(LATE)|{O}
    w={a:mean(cardinal(GRID,a)) for a in GRID}
    assert all(sum(w[a]*a**j for a in GRID)==mean([Z]*j+[O]) for j in range(P))
    U0=[[w[a]*peval(QG,a)] for a in EARLY]
    eta0,elo=paid_inv(U0); eta0=eta0[0]
    lo=k+len(EARLY)
    EE=[[Z]*lo,[Z]*lo]
    for j,(a,h) in enumerate(zip(EARLY,eta0,strict=True)):
        ca=w[a]*h
        for E in EE:
            for i,v in enumerate(X0(a)):
                E[i]-=ca*v
        EE[0][k+j]=ca;EE[1][k+j]=h
    eta,etaN=EE; assert sum(eta)==0
    K=prim(QG)
    assert K==sc(mul(mul(H,H),[O,Z,3*O]),Q(1,36))
    D=lambda a:vadd(pad(X0(a),lo),sc(eta,peval(QG,a)))
    DN=lambda a:vadd(pad(X0(a),lo),sc(etaN,peval(QG,a)))
    lift=lambda a,coef:vadd(pad(I0(a),lo),sc(eta,peval(K,a)+coef))
    liftN=lambda a,coef:vadd(pad(I0(a),lo),sc(etaN,peval(K,a)+coef))
    mask={a:-peval(K,a) for a in EARLY}
    mask.update(zip(HIGH,GAMMA,strict=True))
    qh=mul(BOUND,hull(LATE))
    assert all(sum(w[a]*peval(qh,a)*a**k0*mask[a] for a in LIVE)==0 for k0 in (0,1))
    h=lambda f:fp([Q((-1)**i)*x for i,x in enumerate(f)])
    piv=h(qh); assert piv==Q(4,3)
    cardinalS={a:mul(BOUND,sc(cardinal(LATE,a),O/(O-a))) for a in LATE}
    phiS={a:-sum(w[u]*peval(cardinalS[a],u)*mask[u] for u in LIVE) for a in LATE}
    ES={a:vadd(cardinalS[a],sc(qh,-h(cardinalS[a])/piv)) for a in LATE}
    assert all(h(f)==0 for f in ES.values())
    V=[[Z]*j+H for j in range(G-1)]
    X=[[w[a]*peval(f,a) for f in V]+[w[a]*mask[a]] for a in LIVE]
    J,Jrec=paid_inv(X)
    lr=[list(r) for r in RA]+[I0(a) for a in EARLY]
    nr=[list(r) for r in lr]
    beta=[O]*k+[w[a] for a in EARLY]; lab=[2*sum(r,Z)-O for r in RA]+list(EARLY)
    lr.extend(lift(a,mask[a]) for a in HIGH); nr.extend(liftN(a,mask[a]) for a in HIGH)
    beta.extend(w[a] for a in HIGH);lab.extend(HIGH)
    for row in RA: lr.append(list(row));nr.append(list(row));beta.append(-O);lab.append(2*sum(row,Z)-O)
    for a in GRID:
        if a not in LIVE:lr.append(lift(a,0));nr.append(liftN(a,0));beta.append(w[a]);lab.append(a)
    for a in LATE:
        Gs=[mean(mul(ES[a],prim(v))) for v in V]+[Z]
        taps=[dot(Gs,u) for u in zip(*J,strict=True)]
        rr,NN=pad(lift(a,phiS[a]),k+len(LIVE)),pad(liftN(a,phiS[a]),k+len(LIVE))
        for j,(x,t) in enumerate(zip(LIVE,taps,strict=True)):
            ca=w[x]*t;rr[k+j]+=ca;NN[k+j]+=t
            for i,(u,v) in enumerate(zip(D(x),DN(x),strict=True)):
                rr[i]-=ca*u; NN[i]-=ca*v
        lr.extend((rr,lift(a,0))); nr.extend((NN,liftN(a,0)))
        beta.extend((O,-O));lab.extend((a,a))
    ns=len(lr);assert ns==47
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
    assert len(B0)==len(B)==39,(len(B0),merges)
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
            old_reverse_decoder=pack(d0,2),high_fwd_weights=pack(high,1),
            scalar_sites=list(map(str,GRID)),pure_late_sites=list(map(str,LATE)),
            weighted_receivers=[ns-1-(k+i) for i in range(len(LIVE))],
            receiver_sites=list(map(str,LIVE)),receiver_masses=[str(w[v]) for v in LIVE],
            early_sites=list(map(str,EARLY)),high_sites=list(map(str,HIGH)),
            mask=pack([mask[a] for a in LIVE],1),eta=pack(eta,1),etaN=pack(etaN,1),
            Q=pack(QG,1),K=pack(K,1),compensators=pack([phiS[a] for a in LATE],1),
            top_left_basis=pack([pad(ES[a],M+1) for a in LATE],2),
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
