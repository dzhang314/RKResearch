"""Independent exact audit of the distinct factorial-unit 57-stage order-18 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import factorial, gcd,lcm,prod
from itertools import permutations
from pathlib import Path
import json

P=19
PAID=factorial(P)
OLD_TABLEAU="e7b11babf332b7ac23e2ec9d12dd7552eaa5921492411915cf2128640eec4df5"
OLD_RECEIPT="21c28d21e707b41cf49cd0423e01eb78e5fb19b6411fd5a898e54adb2c58e040"
Q = Fraction


def denominator(d, p):
    assert p==P
    q = int(d["den"])
    power, factor = d["pay_exp"], int(d["pay_cofactor"])
    assert q>0 and factor>0 and 0<=power<=64
    assert q*factor == PAID**power
    return q


def read_vec(obj, n, p):
    q = denominator(obj, p)
    assert len(obj["num"]) == n
    return [Q(int(x),q) for x in obj["num"]]


def read_mat(obj, m, n, p):
    q = denominator(obj, p)
    assert len(obj["num"]) == m and all(len(row)==n for row in obj["num"])
    return [[Q(int(x),q) for x in row] for row in obj["num"]]


def dot(u,v):
    if len(u)!=len(v):
        raise ValueError("different dot lengths")
    return sum((u[i]*v[i] for i in range(len(u))),0)


def tpose(a):
    return [list(col) for col in zip(*a,strict=True)]


def act(a,v):
    return [dot(row,v) for row in a]


def compose(a,b):
    return [act(tpose(b),row) for row in a]


def allzero(xs):
    return all(x==0 for x in xs)


def integers(rows,n):
    assert all(len(row)==n for row in rows)
    return [[int(x) for x in row] for row in rows]


def coordinates(columns, coords, dim):
    assert columns and len(coords)==len(columns)
    assert all(len(c)==dim for c in columns)
    return [sum(q*c[i] for q,c in zip(coords,columns,strict=True)) for i in range(dim)]


def shape(t):
    branches = [shape(u) for u in t]
    size = 1+sum(n for n,_ in branches)
    return size, size*prod(q for _,q in branches)


def phi(A, t):
    child_values = [act(A,phi(A,u)) for u in t]
    return [prod(c[i] for c in child_values) for i in range(len(A))]


def paid_remainder(n, base):
    n=abs(n)
    assert n>0
    while (g:=gcd(base,n))!=1:
        n//=g
    return n


def cardinal_mass(a,grid):
    p,den=[Q(1)],Q(1)
    for x in grid:
        if x==a:
            continue
        den*=a-x
        q=[Q(0)]*(len(p)+1)
        for j,z in enumerate(p):
            q[j]-=x*z
            q[j+1]+=z
        p=q
    return sum((v/(j+1) for j,v in enumerate(p) if j%2==0),Q(0))/den


def word(prefix):
    t=[]
    for letter in reversed(prefix):
        t=[t] if letter=="A" else t+[[]]
    return t


def pmul(a,b):
    u=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):u[i+j]+=x*y
    return u


def eval_poly(a,x): return sum(v*x**i for i,v in enumerate(a))


def div_H(w):
    d=[]
    for i,x in enumerate(w[:-2]):
        d.append(x+(d[i-2] if i>=2 else 0))
    assert pmul(d,[Q(1),Q(0),Q(-1)])==w
    return d


def nodal(sites):
    p=[Q(1)]
    for x in sites:p=pmul(p,[-x,Q(1)])
    return p


def paid(x):
    q=Q(x)
    return paid_remainder(q.denominator,PAID)==1


def direct_det(rows):
    M=[list(r) for r in rows]; q=Q(1)
    for j in range(len(M)):
        i=next((i for i in range(j,len(M)) if M[i][j]),None)
        if i is None:return Q(0)
        if i!=j:M[i],M[j]=M[j],M[i];q=-q
        t=M[j][j];q*=t
        for i in range(j+1,len(M)):
            u=M[i][j]/t
            for k in range(j+1,len(M)):M[i][k]-=u*M[j][k]
            M[i][j]=0
    return q

def run(obj, archive, prior):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-two-tier-v1"
    assert p==P and m==9 and g==8 and p==m+g+2 and p<=2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(27,75,64)
    nr = nf+ns
    A = read_mat(obj["A_unfolded"],nr,nr,p)
    beta = read_vec(obj["beta"],ns,p)
    c = read_vec(obj["clocks"],ns,p)
    N = read_mat(obj["N"],ns,ns,p)
    L = read_mat(obj["L"],ns,ns,p)
    T = read_mat(obj["T"],ns,ns,p)
    DF = read_mat(obj["DF"],p,nf,p)
    assert all(allzero(row) for row in DF[m:])
    assert all(allzero(A[i][i:]) for i in range(nr))
    assert all(c[i] == 1-sum(L[i]) == sum(A[nf+i]) for i in range(ns))
    assert all(A[nf+i][nf:]==T[i] for i in range(ns))
    for i in range(ns):
        for j in range(ns):
            assert i>j or T[i][j]==0
            assert i<j or N[i][j]==0
            assert L[i][j]==N[i][j]*beta[j]
            assert T[i][j]==beta[j]*N[j][i]
            assert beta[i]*T[i][j]==beta[j]*L[j][i]
    h=paired(obj,A,L,DF,beta,c,prior)

    E = [[x**k for k in range(p)] for x in c]
    J = [[x**(k+1)/(k+1) for k in range(p)] for x in c]
    TE = compose(T,E)
    K = [[TE[i][k]-J[i][k] for k in range(p)] for i in range(ns)]
    KD = compose(K,DF)
    assert all(A[nf+i][:nf]==[-x for x in KD[i]] for i in range(ns))
    assert all(allzero(r[nf:]) for r in A[:nf])
    assert all((k+1)*sum(b*x**k for b,x in zip(beta,c,strict=True))==1 for k in range(p))

    reps,owner = obj["rep"],obj["owner"]
    assert len(reps)==count and len(owner)==nr
    assert reps==sorted(set(reps)) and all(0<=j<nr for j in reps)
    assert set(owner)==set(range(count))
    assert all(owner[r]==i for i,r in enumerate(reps))
    assert all(reps[o]<=i for i,o in enumerate(owner))
    fibers = [[i for i,o in enumerate(owner) if o==j] for j in range(count)]
    def fold(v):
        return [sum(v[i] for i in indices) for indices in fibers]
    vrows = [fold(row) for row in A]
    B = [vrows[i] for i in reps]
    assert all(vrows[i]==B[o] for i,o in enumerate(owner))
    b = fold([Q(0)]*nf+beta)
    archived = [[Q(v) for v in row]+[Q(0)]*(count-len(row)) for row in archive["A"]]
    assert B==archived and b==list(map(Q,archive["b"]))
    assert all(allzero(row[i:]) for i,row in enumerate(B))
    assert len({tuple(row) for row in B})==count

    dual = obj["dual"]
    assert len(dual)==g+1
    U = [integers(step["cols"],ns) for step in dual]
    ds = denominator(obj["dual_scale"],p)
    assert U[0]==[[1]*ns]
    transition_count = 0
    for k,srcs in enumerate(U[:-1]):
        dc = integers(dual[k]["C_scale_cols"],len(U[k+1]))
        dl = integers(dual[k]["L_scale_cols"],len(U[k+1]))
        assert len(dc)==len(dl)==len(srcs)
        for v,u,w in zip(srcs,dc,dl,strict=True):
            assert coordinates(U[k+1],u,ns)==[ds*x*y for x,y in zip(c,v,strict=True)]
            assert coordinates(U[k+1],w,ns)==[ds*x for x in act(L,v)]
            transition_count+=2

    source_rows = [[act(tpose(K),[beta[i]*u[i] for i in range(ns)])
                    for u in Ud] for Ud in U]
    low_count=0
    for d,source in enumerate(source_rows[:-2]):
        for a,row in enumerate(source):
            for k,value in enumerate(row[:p-d-1]):
                assert value==0, ("low_source",d,a,k,str(value))
                low_count+=1

    fs = denominator(obj["forward_scale"],p)
    A0 = [[int(x*fs) for x in row[:nf]] for row in A[:nf]]
    assert all(Q(a,fs)==x for raw,row in zip(A[:nf],A0,strict=True) for a,x in zip(row,raw[:nf],strict=True))
    fdat = obj["forward"]
    assert len(fdat)==m+2
    F = {n:integers(row["cols"],nf+1) for n,row in enumerate(fdat,start=1)}
    assert F[1]==[[1]*(nf+1)]
    f_count=0
    for n in range(2,m+3):
        pairs = [(k,v,w) for k in range(1,n) for v in F[k] for w in F[n-k]]
        coords = integers(fdat[n-1]["attach_coords"],len(F[n]))
        assert len(coords)==len(pairs)
        for (k,v,w),coeff in zip(pairs,coords,strict=True):
            aw=act(A0,w[:nf])
            expected=[(n-k)*v[i]*aw[i] for i in range(nf)]+[fs*v[-1]*w[-1]]
            assert coordinates(F[n],coeff,nf+1)==expected
            f_count+=1
    chart_count=0; mid_count=0; high_count=0
    for n in range(1,m+3):
        for vx in F[n]:
            residual=[(vx[-1] if k==n-1 else 0)-v for k,v in enumerate(act(DF,vx[:nf]))]
            if n<=m:
                assert allzero(residual)
                chart_count+=p
            else:
                xx=[Q(1)]; w=[Q(0)]*n
                for j,a in enumerate(residual[:n]):
                    for i,v in enumerate(xx):w[i]+=a*v
                    xx=pmul(xx,[Q(1,2),Q(-1,2)])
                assert not any(residual[n:]) and eval_poly(w,1)==0
                mid=act(source_rows[g-1],residual); assert allzero(mid)
                mid_count+=len(mid)
                if n==m+1:
                    assert all(dot(r,div_H(w))==0 for r in h)
                    hh=act(source_rows[g],residual); assert allzero(hh)
                    high_count+=len(hh)

    common=lcm(*(x.denominator for row in B for x in row),*(x.denominator for x in b))
    assert common==int(archive["coefficient_common_denominator"])
    assert paid_remainder(common,PAID)==1 and PAID**5%common==0
    wt=lcm(*(x.denominator for x in b))
    assert wt==2127745531711800000 and PAID**2%wt==0
    next_audit(B,b,obj["next"])
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all factorial-paid denominators and {nr*count} fold identities")
    print(f"PASS signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+2}, {chart_count} low, {mid_count} intermediate, and {high_count} high chart entries")
    print("literal common denominator:",common,"divides 19!^5")



def pad(a,n):
    assert len(a)<=n
    return list(a)+[Q(0)]*(n-len(a))

def sc(q,a):return [q*x for x in a]

def add(a,b):
    n=max(len(a),len(b))
    return [x+y for x,y in zip(pad(a,n),pad(b,n),strict=True)]

def pmean(q):return sum(v/(j+1) for j,v in enumerate(q) if j%2==0)

def primitive(q):
    v=[Q(0)]+[t/(2*(j+1)) for j,t in enumerate(q)]
    v[0]=-eval_poly(v,-1)
    return v

def chk_inv(rec,M,J):
    n=len(M[0]);k=len(M)
    assert compose(J,M)==[[Q(i==l) for l in range(n)] for i in range(n)]
    d=int(rec["den"]);assert paid(Q(1,d))
    total=0
    for ids,di,core,coef in rec["terms"]:
        assert len(ids)==n and len(set(ids))==n and all(0<=i<k for i in ids)
        r=[[a*d for a in M[i]] for i in ids]
        assert all(x.denominator==1 for row in r for x in row)
        x=direct_det(r);assert x and x==int(di)
        u=int(core);assert u==(1 if x>0 else -1)*paid_remainder(x.numerator,PAID)
        total+=u*int(coef)
    assert total==1

def paired(o,A,L,DF,beta,c,prior):
    assert prior["p"]==P and prior["nf"]==27
    block=lambda a:read_mat(prior[a],len(prior[a]["num"]),len(prior[a]["num"][0]),P)
    assert [row[:27] for row in A[:27]]==[r[:27] for r in block("A_unfolded")[:27]]
    assert DF==block("DF")
    R=[r[-21:][::-1][:20] for r in block("L")[-21:][::-1][:20]]
    assert R==[r[-20:][::-1] for r in L[-20:][::-1]]
    assert all(not any(r[:-20]) for r in L[-20:])
    assert c[17]==0 and A[44]==A[0] and o["owner"][44]==o["owner"][0]
    assert c[23]==1 and A[50]==A[16] and o["owner"][50]==o["owner"][16]
    h=((-2487,-6632,1473,3928,5433,14488,9393,25048),)
    assert tuple(map(tuple,o["pins"]))==h
    D=read_mat(o["old_reverse_decoder"],7,20,P)
    QG=read_vec(o["Q"],8,P)
    assert QG==list(map(Q,(0,"-26/153","43/102","679/612","-107/51","-1205/612","28/17",1)))
    assert o["removed_reverse_clock"]=="2"
    from functools import cache
    @cache
    def forests(k,lo=None):
        if not k:return ((),)
        return tuple((t,)+r for i in range(1,k+1) for t in forests(i-1)
                     if lo is None or lo<=t for r in forests(k-i,t))
    Qx=[Q(0)]*8
    for i,x in enumerate(QG):
        q=[Q(1)]
        for _ in range(i):q=pmul(q,[Q(-1),Q(2)])
        Qx=add(Qx,sc(x/128,q))
    n_reverse=0
    for i in range(1,9):
        scalar=[Q(j==i-1) for j in range(8)]
        if i==8:scalar=add(scalar,sc(-1,Qx))
        assert scalar[-1]==0
        for t in forests(i-1):
            n,f=shape(t);assert n==i
            assert act(D,sc(Q(f,i),phi(R,t)))==scalar[:-1];n_reverse+=1

    oldlabel={0}|{j*s for s in (-1,1) for j in (1,2,3,4,5,6,7,8,12)}
    assert o["node_replacements"]==[[8,-7],[9,-10]]
    grid=sorted(Q(j,6) for j in (oldlabel-{8,-7})|{9,-10})
    assert all(paid(1/(b-a)) for a,b in zip(grid,grid[1:],strict=False))
    S=[Q(v) for v in ("-2","-1/2","-1/3","0","1/3","1/2","2")]
    S1=[Q(-1)]+S
    E=[a for a in grid if a<0 and a not in S1]
    H=[a for a in grid if a>0 and a not in S and a!=1]; B=E+H
    for k,u in (("scalar_sites",grid),("pure_late_sites",S1),("top_pure_sites",S),("early_sites",E),("high_sites",H),("receiver_sites",B)):
        assert list(map(Q,o[k]))==u
    w={a:cardinal_mass(a,grid) for a in grid}
    assert [w[a] for a in B]==list(map(Q,o["receiver_masses"]))
    cores=[paid_remainder(w[a].numerator,PAID) for a in B]
    assert cores==[13163989,339843953,19015120457,1011113,2373593,138920867,1496962133,860332399,130380079,1419181]
    assert all(gcd(a,b)==1 for i,a in enumerate(cores) for b in cores[i+1:])
    assert o["weighted_receivers"]==list(range(54,44,-1))
    mask=dict(zip(B,read_vec(o["mask"],10,P),strict=True))
    K=read_vec(o["K"],9,P)
    assert K==primitive(QG) and all(mask[a]==-eval_poly(K,a) for a in E)
    maskp=read_vec(o["mask_polynomial"],10,P)
    assert eval_poly(maskp,-1)==0 and maskp[-1]==1
    assert all(mask[a]==eval_poly(maskp,a) for a in B)
    P0=read_mat(o["promotion_matrix"],5,1,P);I0=read_mat(o["promotion_inverse"],1,5,P)
    assert P0==[[w[u]*eval_poly(QG,u)] for u in E]
    chk_inv(o["promotion_minors"],P0,I0)
    V=[list(map(Q,([0]*j+[1,1]))) for j in range(8)]
    M=[[w[a]*eval_poly(v,a) for v in V]+[w[a]*mask[a]] for a in B]
    assert M==read_mat(o["measurement"],10,9,P)
    J=read_mat(o["inverse"],9,10,P);chk_inv(o["measurement_minors"],M,J)
    HH=[Q(1),Q(0),Q(-1)]
    LEFT=[Q(1),Q(-1)]
    Qs=nodal(S);amb=pmul(LEFT,nodal(S1))
    assert dot(h[0],Qs)==-31616 and paid(Q(-1,31616))
    assert all(sum(w[a]*eval_poly(amb,a)*a**j*mask[a] for a in B)==0 for j in (0,1))
    top=read_mat(o["top_left_basis"],8,10,P);comp=read_vec(o["compensators"],8,P)
    assert not any(top[0])
    for a,v in zip(S,top[1:],strict=True):
        assert all(dot(r,div_H(v))==0 for r in h)
        assert [eval_poly(v,b) for b in S]==[Q(a==b) for b in S]
    for j in range(10):
        f=[Q(0)]*j+LEFT
        assert sum(w[a]*mask[a]*eval_poly(f,a) for a in B)+dot(comp,[eval_poly(f,a) for a in S1])==0
    # Verify the actual independent row formulas of both live tiers and all late pairs.
    L0=[r[::-1] for r in L[::-1]];b=beta[::-1];labels=[1-2*x for x in c[::-1]]
    y=lambda a:(Q(1)+a)/2
    f0=lambda a:[eval_poly(v,y(a)) for v in tpose(D)]
    z0=lambda a:[sum(v*y(a)**(j+1)/(j+1) for j,v in enumerate(col)) for col in tpose(D)]
    eta=read_vec(o["eta"],25,P);etan=read_vec(o["etaN"],25,P)
    assert eta==[v*u for v,u in zip(etan,b[:25],strict=True)]
    et=[Q(0)]*25
    for j,(a,u) in enumerate(zip(E,I0[0],strict=True)):
        et=add(et,sc(-w[a]*u,f0(a)));et[20+j]=w[a]*u
    assert eta==et and sum(eta)==0
    d=lambda a:add(f0(a),sc(eval_poly(QG,a),eta))
    z=lambda a,e:add(z0(a),sc(eval_poly(K,a)+e,eta))
    reg=[a for a in grid if a not in B]
    out=R+[z0(a) for a in E]+[z(a,mask[a]) for a in H]+R+[z(a,Q(0)) for a in reg]
    a0=[2*sum(v)-1 for v in R]
    xs=a0+B+a0+reg
    bs=[Q(1)]*20+[w[a] for a in B]+[Q(-1)]*20+[w[a] for a in reg]
    for a,f,e in zip(S1,comp,top,strict=True):
        coefs=[sum(u/(i+1) for i,u in enumerate(pmul(e,primitive(v))) if i%2==0) for v in V]+[Q(0)]
        taps=act(tpose(J),coefs);outrow=pad(z(a,f),30)
        for j,(x,t) in enumerate(zip(B,taps,strict=True)):
            outrow=add(outrow,sc(-t*w[x],d(x)));outrow[20+j]+=t*w[x]
        out.extend((outrow,z(a,Q(0))));xs.extend((a,a));bs.extend((Q(1),Q(-1)))
    assert [pad(v,75) for v in out]==L0 and xs==labels and bs==b
    print("PASS eight pure compensation clocks, asymmetric 5+5 live tiers, two compensated left equations, and all 75 chronological reverse rows")
    print("PASS paid 5→1 promotion and 10→9 augmented recovery with the paid monic mask; unchanged charts and two literal endpoint aliases", n_reverse, "old projected reverse reads")
    return h

def next_audit(B,b,data):
    WW=("CCCCCCCCA","CCCCCCCAA")
    V=("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    AA=(136080,-272160,204120,-34020)
    rr=[]; es=[]
    for branch,pre in zip(data["grafts"],WW,strict=True):
        assert branch["prefix"]==pre
        vals=[]; ds=[]; ex=[]
        for (t,k,r,d),post,a in zip(branch["terms"],V,AA,strict=True):
            assert t==word(pre+post) and k==a
            n,F=shape(t);assert n==20
            x=dot(b,phi(B,t));e=F*x-1
            assert x==Q(r) and e==Q(d)
            vals.append(x);ds.append(e);ex.append(Q(a,F))
        assert Q(branch["raw"])==dot(AA,vals) and sum(ex)==0
        rr.append(Q(branch["raw"]));es.append(ds)
    assert rr==[Q(-1552399572022214961505,55515199094784),Q(21660214453692068872891429459,174406549476173414400)]
    bc=list(map(Q,data["raw_blend"]));assert dot(bc,rr)==1 and all(paid(x) for x in bc)
    du=dot(b,phi(B,[[] for _ in range(P)]))
    assert du==Q(data["bush_output"]) and 20*du-1==Q(data["bush_defect"])==Q(-213309881,15119477335130112)
    pick=[]
    for i,j,z in data["picked"]:
        assert es[i][j]==Q(z);pick.append(Q(z))
    assert pick==[Q(1123774196317537919294796223,3021803317127282688),Q(3204088976399915389469032543,3021803317127282688)]
    uu=list(map(Q,data["blend"]));assert dot(uu,pick)==1 and all(x.denominator==1 for x in uu)
    d=lcm(*(x.denominator for r in B for x in r));e=lcm(*(x.denominator for x in b));scale=e*d**P
    counts=[x*scale for x in pick]
    assert all(x.denominator==1 for x in counts) and dot(uu,counts)==scale
    print("PASS two actual raw next grafts and unit blend",list(map(str,rr)),list(map(str,bc)))
    print("PASS actual two cleared size-20 defects and integer unit blend",list(map(str,pick)),list(map(str,uu)))

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path);cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path);cli.add_argument("old_receipt",type=Path)
    u=cli.parse_args()
    assert sha256((u.source/"order-19-factorial-65/tableau-19-factorial-65.json").read_bytes()).hexdigest()==OLD_TABLEAU
    assert sha256(u.candidate.read_bytes()).hexdigest()!=OLD_TABLEAU
    r=u.old_receipt.read_bytes();assert sha256(r).hexdigest()==OLD_RECEIPT
    run(json.loads(u.receipt.read_bytes()),json.loads(u.candidate.read_bytes()),json.loads(r))
