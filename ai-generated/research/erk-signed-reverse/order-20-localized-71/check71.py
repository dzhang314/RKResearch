"""Independent exact audit of the localized 71-stage order-20 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import factorial, gcd,lcm,prod
from pathlib import Path
import json

P=20
EXTRA=(37,911,15901,1120673,86775809,1034700137)
PAID=factorial(P)*prod(EXTRA)
OLD_TABLEAU="a08c3229cd058edf41eb91241852166fcdf2f0712d10a850539c07b278bb9cb3"
OLD_WITNESS="85fe4ade0371313977dbeb5c5adf2c990871e25ef4beb9103684989c3830a841"
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


def next_audit(B,b,claimed,previous):
    raw=claimed["literal_witness"]
    assert len(raw)==len(previous)==2 and raw==previous
    vals=[]
    for t,expected in raw:
        n,fact=shape(t)
        assert n==21
        actual=fact*dot(b,phi(B,t))-1
        assert actual==Q(expected), ("actual next",str(actual),expected)
        vals.append(actual)
    blend=read_vec(claimed["blend"],2,P)
    assert dot(blend,vals)==1
    grafts=claimed["balanced_graft"]
    terms=(("CACCACCACC",136080),("CACCACCAAC",-272160),
           ("CACCACCCCC",204120),("CACCCCCCCC",-34020))
    assert len(grafts)==len(terms)==4
    correction=Q(0)
    balanced=Q(0)
    for (t,coef,expected),(word,mult) in zip(grafts,terms,strict=True):
        child=[]
        for op in reversed(word):
            child=[child] if op=="A" else child+[[]]
        assert t==[child]+[[] for _ in range(9)]
        size,tk=shape(t)
        assert size==21 and Q(coef)==Q(mult,tk)
        assert paid_remainder(Q(coef).denominator,PAID)==1
        val=tk*dot(b,phi(B,t))-1
        assert val==Q(expected)
        balanced+=Q(coef)
        correction+=Q(coef)*val
    assert balanced==0 and correction==1
    print(f"PASS both actual size-21 defects, paid unit blend {list(map(str,blend))}, and four balanced grafts with exact raw output +1")


def run(obj, archive, witness):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-localized-v1"
    assert p==P and m==9 and g==9 and p==2*m+2 and tuple(obj["extra_inversions"])==EXTRA
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(27,89,71), ("shape",nf,ns,count)
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

    rec = obj["weighted_receivers"]
    assert len(rec)==9 and len(set(rec))==len(rec) and all(0<=i<ns for i in rec)
    selected=tuple(sorted(Q(sign*j,6) for sign in (-1,1) for j in (4,5,7,8)))
    assert list(map(Q,obj["interpolation_sites"]))==list(selected)
    sites=sorted({Q(0)}|{Q(sign*j,6) for sign in (-1,1) for j in (1,2,3,4,5,6,7,8,12)})
    actual_weights=dict(zip(selected,map(Q,obj["selected_masses"]),strict=True))
    obs={1-2*c[i]:i for i in rec}
    assert len(obs)==len(rec) and set(obs)-set(selected)=={Q(-1,6)}
    for site in selected:
        mass=cardinal_mass(site,sites)
        assert mass==actual_weights[site]==beta[obs[site]]
        assert paid_remainder((mass*(1-site**2)).numerator,PAID)==1
        assert paid_remainder((mass*(1-site**2)).denominator,PAID)==1
        for other in selected:
            if site!=other:
                diff=site-other
                assert paid_remainder(diff.numerator,PAID)==1
                assert paid_remainder(diff.denominator,PAID)==1
    meas=read_mat(obj["measurement"],9,8,p)
    inv=read_mat(obj["left_inverse"],8,9,p)
    for i,row in zip(rec,meas,strict=True):
        u=1-2*c[i]
        assert row==[beta[i]*(1-u*u)*u**k for k in range(8)], ("measurement",i)
    assert compose(inv,meas)==[[Q(i==j) for j in range(8)] for i in range(8)]
    for i,r in enumerate(rec):
        if (1-2*c[r]) not in selected:
            assert all(row[i]==0 for row in inv)

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
    for d,source in enumerate(source_rows[:-1]):
        for a,row in enumerate(source):
            for k,value in enumerate(row[:p-d-1]):
                assert value==0, ("low_source",d,a,k,str(value))
                low_count+=1

    fs = denominator(obj["forward_scale"],p)
    A0 = [[int(x*fs) for x in row[:nf]] for row in A[:nf]]
    assert all(Q(a,fs)==x for raw,row in zip(A[:nf],A0,strict=True) for a,x in zip(row,raw[:nf],strict=True))
    fdat = obj["forward"]
    assert len(fdat)==m+1
    F = {n:integers(row["cols"],nf+1) for n,row in enumerate(fdat,start=1)}
    assert F[1]==[[1]*(nf+1)]
    f_count=0
    for n in range(2,m+2):
        pairs = [(k,v,w) for k in range(1,n) for v in F[k] for w in F[n-k]]
        coords = integers(fdat[n-1]["attach_coords"],len(F[n]))
        assert len(coords)==len(pairs)
        for (k,v,w),coeff in zip(pairs,coords,strict=True):
            aw=act(A0,w[:nf])
            expected=[(n-k)*v[i]*aw[i] for i in range(nf)]+[fs*v[-1]*w[-1]]
            assert coordinates(F[n],coeff,nf+1)==expected
            f_count+=1
    chart_count = 0
    high_count = 0
    for n in range(1,m+2):
        for basis_index,vx in enumerate(F[n]):
            z=vx[-1]
            v=act(DF,vx[:nf])
            residual=[(z if k==n-1 else 0)-v[k] for k in range(p)]
            if n<=m:
                for k,value in enumerate(residual):
                    assert value==0, ("forward_chart",n,basis_index,k,str(value))
                    chart_count+=1
            else:
                for a,value in enumerate(act(source_rows[g],residual)):
                    assert value==0, ("high_source",g,a,n,basis_index,str(value))
                    high_count+=1

    common=lcm(*(x.denominator for row in B for x in row),*(x.denominator for x in b))
    assert common==int(archive["coefficient_common_denominator"])
    assert paid_remainder(common,PAID)==1
    extra=paid_remainder(common,factorial(P))
    assert extra!=1, "this literal must not be reported as factorial-unit"
    next_audit(B,b,obj["next"],witness)
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all paid denominators and {nr*count} fold identities")
    print(f"PASS weighted inverse 8×8, actual selected masses, signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print("literal common denominator:",common)
    print("literal denominator part outside 20 factorial:",extra)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path)
    args=cli.parse_args()
    assert sha256((args.source/"tableau-20-weighted.json").read_bytes()).hexdigest()==OLD_TABLEAU
    witness=(args.source/"witness-20-weighted.json").read_bytes()
    assert sha256(witness).hexdigest()==OLD_WITNESS
    run(json.loads(args.receipt.read_text()),json.loads(args.candidate.read_text()),json.loads(witness))
