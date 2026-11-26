"""Exact construction of a new factorial-unit order-18 tableau and finite receipt."""
import sys,argparse,json
from pathlib import Path
from fractions import Fraction as Q
from math import factorial,prod,lcm,gcd
from itertools import combinations
from importlib.util import spec_from_file_location,module_from_spec
from hashlib import sha256
from functools import cache
import receipt_arithmetic as ar

P,M,G=18,9,7
PAY=factorial(P)
Z=Q(0); O=Q(1)
H=[O,Z,-O]
ONE=[O,O]
ELL=(-2487,-6632,1473,3928,5433,14488,9393,25048)
LATE=tuple(map(Q,("-3/2","-1/2","-1/3","0","1/3","1/2","3/2")))
RADII=tuple(map(Q,("1/5","1/3","1/2","2/3","1","3/2","2","5")))
GRID=sorted({Z}|{s*x for s in (-1,1) for x in RADII})
LIVE=sorted(set(GRID)-set(LATE)-{-O,O})
SOURCES={
 "construct.py":"74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
 "weighted_middle.py":"54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
 "tableau-15-weighted.json":"8ce24fdf663adcd88fa368eb89cef7e631d4b57762dd77512340d1f1132648eb",
 "tableau-18-weighted.json":"adec0df152d14550aeb54fa8a095d6f3ad9974120f6a5f6f49b903affd389b61",
 "order-18-localized-59/tableau-18-localized-59.json":"893805a7d652e00335375ce881ed7c3c98f7c06d0927a813edb59b160a20d7b4",
 "../erk-eleven-twelve-moment-splice/paid9-seed.json":"8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
}
FILENAME="tableau-18-factorial-57.json"
RFILE="receipt-18-factorial-57.json"

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
    n=len(MX[0]);den=lcm(*(x.denominator for r in MX for x in r))
    assert unit(den)
    RR=[[int(den*x) for x in r] for r in MX]
    chosen=[]; blend=[];g=0
    for radius in (Q(1,5),Q(2,3),Q(2),Q(5)):
        ids=tuple(i for i,u in enumerate(LIVE) if abs(u)!=radius)
        A=[RR[i] for i in ids];d=det(A)
        core=d
        assert core
        while (f:=gcd(abs(core),PAY))>1: core//=f
        q,x,y=ar.egcd(g,core);chosen.append((ids,A,d,core));blend=[x*v for v in blend]+[y];g=q
    assert g==1
    rows=[[Z]*len(RR) for _ in range(n)]
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
        children=[[dot(row,phi(u)) for row in A] for u in t]
        return tuple(prod(x[i] for x in children) for i in range(len(b)))
    def size(t):return 1+sum(map(size,t))
    def fact(t):return size(t)*prod(map(fact,t))
    init=("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    alpha=(136080,-272160,204120,-34020)
    prefixes=("CCCCCCAA","AAAAAAAA")
    targets=(Q(4793,259683840),Q(-41,3525120))
    E=lcm(*(x.denominator for x in targets)); c,d=map(lambda t:int(t*E),targets)
    g,k,l=ar.egcd(c,d); assert g==1
    weights=[k*E,l*E]; assert dot(weights,targets)==1
    grafts=[]; physical=[]
    for prefix,target in zip(prefixes,targets,strict=True):
        ts=[word(prefix+x,()) for x in init]
        q=[fact(t) for t in ts]
        raw=[dot(b,phi(t)) for t in ts]
        assert all(size(t)==P+1 for t in ts)
        assert sum(Q(a*(P+1),v) for a,v in zip(alpha,q,strict=True))==0
        assert dot(alpha,raw)==target
        terms=[[t,a,str(x),str(f*x-1)] for t,a,x,f in zip(ts,alpha,raw,q,strict=True)]
        physical.extend((len(grafts),j,Q(d)) for j,(_,_,_,d) in enumerate(terms))
        grafts.append(dict(prefix=prefix,terms=terms,raw=str(target)))
    bush_t=((),)*P
    bush_raw=dot(b,phi(bush_t)); bush=(P+1)*bush_raw-1
    # The explicit unit combination all in actual (not model) cleared defects.
    checks=[(i,j,v) for i,j,v in physical]+[(-1,0,bush)]
    D=lcm(*(v.denominator for _,_,v in checks))
    assert unit(D)
    for u,v in combinations(checks,2):
        ee=lcm(u[2].denominator,v[2].denominator)
        gg,x,y=ar.egcd(int(ee*u[2]),int(ee*v[2]))
        if gg==1:
            coeff=[ee*x,ee*y]
            assert dot(coeff,[u[2],v[2]])==1
            return dict(grafts=grafts,raw_blend=weights,bush_output=str(bush_raw),
                        bush_defect=str(bush),
                        picked=[[i,j,str(v)] for i,j,v in (u,v)],blend=coeff)
    raise AssertionError("No direct two-term literal unit pair")

def build(source):
    for file,d in SOURCES.items():assert sha256((source/file).read_bytes()).hexdigest()==d,file
    rk=mod(source/"construct.py","rk_new_p18_57_construct")
    middle=mod(source/"weighted_middle.py","rk_new_p18_57_middle")
    rk.PAID=PAY
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    FA,fo,fr=rk.long(M,False,seed)
    RA,ro,rr,grade,pin,high,*_=middle.prepare(rk,15,peval,mul,vadd,sc,cardinal)
    assert (len(FA),len(RA),grade)==(27,15,G)
    nf,k=len(FA),len(RA)
    FD=[pad(rk.read(fo,fr,lambda i,j=j:Q(i==j))[0],nf) for j in range(M)]
    RD=[pad(rk.read(ro,rr,lambda i,j=j:Q(i==j))[0],k) for j in range(G)]
    sites={2*sum(v,Z)-O for v in RA}
    assert sites=={Z,-O,O,-Q(1,3),Q(1,3),-Q(1,2),Q(1,2)}
    assert sites<=set(GRID)-set(LIVE)
    lam={a:mean(cardinal(GRID,a)) for a in GRID}
    assert all(sum(lam[a]*a**j for a in GRID)==mean([Z]*j+[O]) for j in range(P))
    pvals=[pin([Z]*j+ONE) for j in range(7)]
    assert pvals[0]==Q(77,8) and unit(pvals[0])
    V=[vadd([Z]*j+ONE,sc(ONE,-pvals[j]/pvals[0])) for j in range(1,7)]
    X=[[lam[a]*peval(v,a) for v in V] for a in LIVE]
    Ji,mins=paid_inv(X)
    Q_S=hull(LATE)
    pivot=dot(ELL,Q_S)
    assert pivot==Q(-27200,3) and unit(pivot)
    E={}
    for a in LATE:
        q=pad(sc(cardinal(LATE,a),O/peval(H,a)),8)
        q=vadd(q,sc(Q_S,-dot(ELL,q)/pivot))
        assert dot(ELL,q)==0
        E[a]=mul(H,q)
    es,k2=len(LIVE),k+len(LIVE)
    # Raw chronological labels: original donors, live receivers, old negative
    # copies, all unlike live scalar receivers, and a signed pair per late site.
    R0=lambda a:row_for_x(RD,(O+a)/2)
    lr=[list(v) for v in RA]+[R0(a) for a in LIVE]
    beta=[O]*k+[lam[a] for a in LIVE]
    lab=[2*sum(v,Z)-O for v in RA]+LIVE
    for row in RA:lr.append(list(row));beta.append(-O);lab.append(2*sum(row,Z)-O)
    for a in GRID:
        if a not in LIVE:lr.append(R0(a));beta.append(lam[a]);lab.append(a)
    Nextra={}
    for a in LATE:
        extra=[mean(mul(E[a],prim(v))) for v in V]
        taps=[dot(extra,column) for column in zip(*Ji,strict=True)]
        T0=pad(R0(a),k2)
        NN=pad(R0(a),k2)
        for j,(u,h) in enumerate(zip(LIVE,taps,strict=True)):
            wt=lam[u]
            T0[k+j]=wt*h; NN[k+j]=h
            for i,d in enumerate(eval_chart(RD,(O+u)/2)):
                T0[i]-=wt*h*d; NN[i]-=wt*h*d
        Nextra[len(lr)]=NN
        lr.extend((T0,R0(a))); beta.extend((O,-O)); lab.extend((a,a))
    ns=len(lr); assert ns==61
    NL=[pad(Nextra.get(i,lr[i]),ns) for i in range(ns)]
    L0=[pad(q,ns) for q in lr]
    assert all(sum(r)==(O+a)/2 for r,a in zip(L0,lab,strict=True))
    assert all(L0[i][j]==beta[j]*NL[i][j] for i in range(ns) for j in range(ns))
    xp=[(O-a)/2 for a in reversed(lab)]
    bb=beta[::-1]
    nn=[row[::-1] for row in reversed(NL)]; ll=[row[::-1] for row in reversed(L0)]
    TT=[[bb[j]*nn[j][i] for j in range(ns)] for i in range(ns)]
    FF0=[pad(list(r),nf+ns) for r in FA]
    Ef=[eval_chart(FD,v) for v in xp]
    for i,(x,t) in enumerate(zip(xp,TT,strict=True)):
        f=[a-dot(t,u) for a,u in zip(row_for_x(FD,x),zip(*Ef,strict=True),strict=True)]
        assert not any(t[i:]); FF0.append(f+t)
    s=len(FF0)
    rows,b,mergers=rk.merge([q[:i] for i,q in enumerate(FF0)],[Z]*nf+bb)
    a={i-1:j-1 for i,j in mergers}
    rep=[i for i in range(s) if i not in a]; kappa={i:j for j,i in enumerate(rep)}
    own=[kappa[a.get(i,i)] for i in range(s)]
    A=[[dict(v).get(j,Z) for j in range(57)] for v in rows]
    assert len(rows)==len(b)==57
    d=lcm(*(x.denominator for row in A for x in row),*(x.denominator for x in b))
    assert unit(d)
    lit=dict(A=[[str(x) for x in r[:i]] for i,r in enumerate(A)],b=list(map(str,b)),
             coefficient_common_denominator=str(d))
    w=next_data(A,b)
    AF=[row[:nf] for row in FF0[:nf]]
    df=lcm(*(x.denominator for row in AF for x in row))
    dd=lcm(*(x.denominator for row in ll for x in row),*(x.denominator for x in xp))
    AFn=[[int(df*v) for v in row] for row in AF]
    Ln=[[int(dd*v) for v in row] for row in ll]
    cc=[int(dd*v) for v in xp]
    dual=[dict(cols=ar.ints([[1]*ns]))]; U=[[1]*ns]
    for _ in range(G):
        V0,loc=ar.modular_bilattice([[i*j for i,j in zip(cc,u,strict=True)] for u in U]+[ar.matvec(Ln,u) for u in U],PAY)
        dual[-1]["C_scale_cols"]=ar.ints(loc[:len(U)])
        dual[-1]["L_scale_cols"]=ar.ints(loc[len(U):])
        dual.append(dict(cols=ar.ints(V0))); U=V0
    F={1:[[1]*(nf+1)]}
    ff=[dict(cols=ar.ints(F[1]))]
    for size in range(2,M+2):
        F[size],loc=ar.modular_bilattice([ar.native_attach(AFn,df,size-aa,v,u)
                  for aa in range(1,size) for v in F[aa] for u in F[size-aa]],PAY)
        ff.append(dict(cols=ar.ints(F[size]),attach_coords=ar.ints(loc)))
    pack=lambda x,n:ar.encode(x,n,PAY)
    receipt=dict(schema="rk-weighted-upper-structural-paired-oriented-v1",p=P,m=M,g=G,
                 source_hashes=SOURCES,nf=nf,ns=ns,final=len(rows),owner=own,rep=rep,
                 A_unfolded=pack(FF0,2),N=pack(nn,2),L=pack(ll,2),T=pack(TT,2),
                 DF=pack(FD+[[Z]*nf]*(P-M),2),beta=pack(bb,1),clocks=pack(xp,1),
                 measurement=pack(X,2),left_inverse=pack(Ji,2),minor_identity=mins,
                 right_axes=pack([pad(v,8) for v in V],2),high7_weights=pack(high,1),reverse_decoder=pack(RD,2),
                 receiver_sites=list(map(str,LIVE)),receiver_masses=[str(lam[a]) for a in LIVE],
                 weighted_receivers=[ns-1-(k+i) for i in range(es)],
                 scalar_sites=list(map(str,GRID)),pure_late_sites=list(map(str,LATE)),
                 pure_late_basis=pack([E[a] for a in LATE],2),pins=[list(ELL)],
                 dual_scale=ar.require_paid(dd,PAY),forward_scale=ar.require_paid(df,PAY),
                 dual=dual,forward=ff,next=w)
    return lit,receipt,mergers
if __name__=="__main__":
    a=argparse.ArgumentParser(description=__doc__);a.add_argument("source",type=Path);a.add_argument("out",type=Path);b=a.parse_args()
    b.out.mkdir(exist_ok=True)
    lit,r,merges=build(b.source)
    for name,obj in ((FILENAME,lit),(RFILE,r)):
        path=b.out/name
        body=(json.dumps(obj,indent=2) if name==FILENAME else json.dumps(obj,separators=(",",":")))+"\n"
        path.write_text(body,encoding="utf8")
        print(name,sha256(body.encode()).hexdigest())
    print("raw",r["nf"],r["ns"],"final",r["final"],"non-suffix aliases",[(i,j) for i,j in merges if j<=r["nf"]])
    print("paid right minor cores and blends",[(u,x,z) for u,_,x,z in r["minor_identity"]["terms"]])
    print("raw order-19",[(x["prefix"],x["raw"]) for x in r["next"]["grafts"]],r["next"]["raw_blend"])
    print("literal order-19",r["next"]["picked"],r["next"]["blend"],"bush",r["next"]["bush_defect"])
