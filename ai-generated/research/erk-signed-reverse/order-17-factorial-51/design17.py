"""Bounded exact p17 two-tier design, read-only prior chart inputs."""
from fractions import Fraction as Q
from math import factorial,gcd,lcm,prod,comb
from itertools import combinations
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
from hashlib import sha256
import sys,json
import receipt_arithmetic as ar

P,M,G=17,8,7
PAY=factorial(P); O=Q(1); Z=Q(0)
H=[O,Z,-O]; BOUND=[O,O]
RADII=tuple(map(Q,("1/5","1/3","1/2","2/3","1","3/2","2","5")))
GRID=sorted({Z}|{s*x for x in RADII for s in (-1,1)})
S=tuple(map(Q,("-1/2","-1/3","0","1/3","1/2")))
LIVE=tuple(a for a in GRID if a not in S and abs(a)!=1)
E=tuple(a for a in LIVE if a<0); T=tuple(a for a in LIVE if a>0)
PINS=((-1200,5,-192,5,-48,5,0),(105,0,21,0,9,0,5))
REPO=Path(__file__).resolve().parent.parent
SOURCES={
 "construct.py":"74ee0b15daa00996a506ecb2c1fc09a5ebc979e35f26c74eed368b1104dc21c7",
 "weighted_middle.py":"54e072af8ad1a3c254f627e1871ea9db0d44bee41857e57660f267ebd74788ec",
 "../erk-eleven-twelve-moment-splice/paid9-seed.json":"8d066b0962766081b81d29c5f2c8331c6f814ed137a440f04674cc71829b1c39",
 "order-17-factorial-52/tableau-17-factorial-52.json":"d46fc84dbabeb0d7f78632aa4b8b7f272a65904487061a0c1212ffeab9c9c246",
}

def pad(v,n):
    assert len(v)<=n;return list(v)+[Z]*(n-len(v))
def dot(a,b):return sum((x*y for x,y in zip(a,b,strict=True)),Z)
def add(a,b):
    n=max(len(a),len(b));return [x+y for x,y in zip(pad(a,n),pad(b,n),strict=True)]
def sc(a,k):return [k*x for x in a]
def peval(a,x):return sum((u*x**j for j,u in enumerate(a)),Z)
def mean(a):return sum((u/(j+1) for j,u in enumerate(a) if j%2==0),Z)
def mul(a,b):
    v=[Z]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):v[i+j]+=x*y
    return v
def hull(nodes):
    q=[O]
    for a in nodes:q=mul(q,[-a,O])
    return q
def prim(a):
    q=[Z]+[u/(2*(j+1)) for j,u in enumerate(a)]
    q[0]=-peval(q,-O)
    return q
def upper(a):
    q=[Z]+[-u/(2*(j+1)) for j,u in enumerate(a)]
    q[0]=-peval(q,O)
    return q
def strip(a):
    while (n:=gcd(a,PAY))>1:a//=n
    return a
def unit(a):
    a=Q(a);return bool(a) and abs(strip(a.numerator))==strip(a.denominator)==1
def card(nodes,a):
    q=hull(x for x in nodes if x!=a);d=peval(q,a);assert unit(d)
    return sc(q,O/d)
def mod(path,name):
    s=spec_from_file_location(name,path);a=module_from_spec(s);sys.modules[name]=a;s.loader.exec_module(a);return a
def det(A):
    M=[list(r) for r in A];prev=1;sgn=1
    for j in range(len(M)-1):
        i=next((i for i in range(j,len(M)) if M[i][j]),None)
        if i is None:return 0
        if i!=j:M[i],M[j]=M[j],M[i];sgn=-sgn
        b=M[j][j]
        for i in range(j+1,len(M)):
            c=M[i][j]
            for u in range(j+1,len(M)):
                v=b*M[i][u]-c*M[j][u]
                assert v%prev==0
                M[i][u]=v//prev
            M[i][j]=0
        prev=b
    return sgn*M[-1][-1] if M else 1

def paid_inv(MX,fixed=None):
    n=len(MX[0]);num=len(MX);d=lcm(*(a.denominator for r in MX for a in r))
    assert unit(d)
    M=[[int(a*d) for a in r] for r in MX]
    bags=[]
    for II in (combinations(range(num),n) if fixed is None else fixed):
        U=[M[i] for i in II]
        v=det(U)
        if not v:continue
        core=strip(v);bags.append((abs(core),II,U,v,core))
    if fixed is None: bags.sort(key=lambda a:(a[0],a[1]))
    g=0;weights=[];kept=[]
    for _,I,U,v,core in bags:
        if gcd(g,core)==g:continue
        g,x,y=ar.egcd(g,core)
        weights=[x*z for z in weights]+[y]
        kept.append((I,U,v,core))
        if g==1:break
    if g!=1:return None,g
    J=[[Z]*num for _ in range(n)]
    for (I,U,v,core),kappa in zip(kept,weights,strict=True):
        for i in range(n):
            for h in range(n):
                V=[[v for j,v in enumerate(r) if j!=i] for k,r in enumerate(U) if k!=h]
                J[i][I[h]]+=Q(d*core*kappa*(-1)**(i+h)*det(V),v)
    assert [[dot(r,v) for v in zip(*MX,strict=True)] for r in J]==[[Q(i==j) for j in range(n)] for i in range(n)]
    return J,dict(den=d,terms=[[list(I),str(v),str(core),str(m)] for (I,_,v,core),m in zip(kept,weights,strict=True)])

def chart_inputs(source):
    for f,d in SOURCES.items():assert sha256((source/f).read_bytes()).hexdigest()==d,f
    rk=mod(source/"construct.py","rk_new_ctr_17_51")
    mid=mod(source/"weighted_middle.py","rk_new_mid_17_51");rk.PAID=PAY
    seed=json.loads((source/"../erk-eleven-twelve-moment-splice/paid9-seed.json").read_bytes())
    FA,fo,fr=rk.long(8,False,seed,regular_grade8=True)
    RA,ro,rr,g,pin7,pin7_row,*_=mid.prepare(rk,15,peval,mul,add,sc,card)
    assert (len(FA),len(RA),g)==(22,15,G)
    assert {2*sum(r,Z)-O for r in RA[:-1]}==set(S)|{-O,O}
    assert 2*sum(RA[-1],Z)-O==Q(1,2)
    k=len(RA)-1
    RO=ro[:5]+ro[6:]
    RR=rr[:5]+rr[6:]
    assert all(not any(v[k:]) for v in RR)
    FD=[pad(rk.read(fo,fr,lambda j,i=i:Q(i==j))[0],len(FA)) for i in range(M)]
    D0=[pad(rk.read(RO,[v[:k] for v in RR],lambda j,i=i:Q(i==j))[0],k) for i in range(G-1)]
    # Exact old contrast on the three grade-six primitive reads, in centered clock v.
    ell_v=lambda f:dot(pad(RR[-1],len(RA)),[peval(f,2*sum(v,Z)-1) for v in RA])
    q=hull([-O,O,Q(-1,2),Q(-1,3),Q(1,3)])
    dp=ell_v(q);assert unit(dp)
    q=mul(q,[-ell_v([Z]+q)/dp,O])
    assert peval(q,Q(1,2)) and ell_v(q)==0 and q[-1]==1
    # Retained exact scalar read equations annihilate the uncentered gap.
    Qy=[Z]*G
    for j,a in enumerate(q):
        Qy=add(Qy,[a*comb(j,i)*2**i*(-1)**(j-i) for i in range(j+1)])
    assert all(sum(op(i)*q for i,q in enumerate(Qy))==0 for op in RO)
    return rk,FA,FD,RA[:-1],D0,q,pin7,pin7_row

def design(source,show=False):
    rk,FA,FD,RA,D0,q,high7,high7_row=chart_inputs(source)
    w={a:mean(card(GRID,a)) for a in GRID}
    assert all(sum(w[a]*a**j for a in GRID)==mean([Z]*j+[O]) for j in range(P))
    k=prim(q)
    C=mul(H,hull(S))
    W=[[w[a]*peval(C,a)*a**j for j in range(3)] for a in T]
    J,r=paid_inv(W)
    assert J is not None,r
    target=[sum(w[a]*peval(C,a)*a**j*peval(k,a) for a in E) for j in range(3)]
    vals0=[dot(t,target) for t in zip(*J,strict=True)]
    WT=list(zip(*W,strict=True));JT=list(zip(*J,strict=True))
    Ker=[[Q(i==j)-dot(u,v) for j,u in enumerate(W)] for i,v in enumerate(JT)]
    assert all(all(dot(w,v)==0 for v in zip(*Ker,strict=True)) for w in WT)
    promote=[[w[a]*peval(q,a)] for a in E]
    jp,rp=paid_inv(promote)
    assert jp is not None,rp
    body=[[Z]*j+BOUND for j in range(7)]
    fixed=[tuple(j for j,a in enumerate(LIVE) if abs(a)!=x) for x in T]
    tests=[None]+[(i,t) for t in (1,-1,2,-2,3,-3) for i in range(len(T))]
    for test in tests:
        vals=vals0 if test is None else [a+test[1]*r[test[0]] for a,r in zip(vals0,Ker,strict=True)]
        assert [dot(v,vals) for v in WT]==target
        mask={a:-peval(k,a) for a in E};mask.update(zip(T,vals,strict=True))
        assert all(sum(w[a]*peval(C,a)*a**j*mask[a] for a in LIVE)==0 for j in range(3))
        MT=[[w[a]*peval(f,a) for f in body]+[w[a]*mask[a]] for a in LIVE]
        jt,rt=paid_inv(MT,fixed)
        if jt is None:jt,rt=paid_inv(MT)
        if jt:break
    if show:print("kernel adjustment",test)
    if show:
        print("growth q",q,"K",k)
        print("pure",S,"early",E,"later",T)
        print("mass unpaid cores",[strip(w[a].numerator) for a in T])
        print("high mask",[(a,mask[a]) for a in T])
        print("promote",rp)
        print("compensate cores",[(a,u) for a,_,u,_ in r["terms"]])
        print("augmented",[(a,u) for a,_,u,_ in rt["terms"]] if jt else rt)
    return dict(rk=rk,FA=FA,FD=FD,RA=RA,D0=D0,q=q,k=k,weight=w,mask=mask,X=promote,jp=jp,rp=rp,
                V=body,MT=MT,jt=jt,rt=rt,W=W,mi=r,C=C,target=target,gs=vals)
if __name__=="__main__":
    z=design(REPO if len(sys.argv)==1 else Path(sys.argv[1]),True)
    assert z["jt"] is not None
