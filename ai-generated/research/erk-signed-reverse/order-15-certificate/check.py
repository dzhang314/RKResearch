"""Independent verifier for the order-15 weighted structural arithmetic receipt."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import json

ARCHIVE = "8ce24fdf663adcd88fa368eb89cef7e631d4b57762dd77512340d1f1132648eb"
NEXT = "a0c5e75230a38a4dfdf25e13dd047736fdbcba9d805b9fb81dcbe33378e51d7e"
Q = Fraction
P = 15


def denominator(d):
    q = int(d["den"])
    power, factor = d["pay_exp"], int(d["pay_cofactor"])
    assert q>0 and factor>0 and 0<=power<=64
    assert q*factor == factorial(P)**power
    return q


def read_vec(obj, n):
    q = denominator(obj)
    assert len(obj["num"]) == n
    return [Q(int(x),q) for x in obj["num"]]


def read_mat(obj, m, n):
    q = denominator(obj)
    assert len(obj["num"]) == m and all(len(row)==n for row in obj["num"])
    return [[Q(int(x),q) for x in row] for row in obj["num"]]


def arbitrary_matrix(obj, col_n):
    return read_mat(obj,len(obj["num"]),col_n)


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


def run(obj, archive, witness):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-v1"
    assert p==P and m==7 and g==p-m-2 and p<=2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(15,51,40)
    nr = nf+ns
    A = read_mat(obj["A_unfolded"],nr,nr)
    beta = read_vec(obj["beta"],ns)
    c = read_vec(obj["clocks"],ns)
    N = read_mat(obj["N"],ns,ns)
    L = read_mat(obj["L"],ns,ns)
    T = read_mat(obj["T"],ns,ns)
    DF = read_mat(obj["DF"],p,nf)
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
    assert len(rec)==7 and len(set(rec))==len(rec) and all(0<=i<ns for i in rec)
    meas = read_mat(obj["measurement"],7,5)
    for i,row in zip(rec,meas,strict=True):
        u=1-2*c[i]
        assert row==[beta[i]*(1-u*u)*u**k for k in range(5)]
    inv = read_mat(obj["left_inverse"],5,7)
    assert compose(inv,meas)==[[Q(i==j) for j in range(5)] for i in range(5)]

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
    ds = denominator(obj["dual_scale"])
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
        for row in source:
            must_zero=row[:p-d-1]
            assert allzero(must_zero)
            low_count+=len(must_zero)

    fs = denominator(obj["forward_scale"])
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
        for vx in F[n]:
            z=vx[-1]
            v=act(DF,vx[:nf])
            residual=[(z if k==n-1 else 0)-v[k] for k in range(p)]
            if n<=m:
                assert allzero(residual)
                chart_count+=len(residual)
            else:
                assert allzero(act(source_rows[g],residual))
                high_count+=len(source_rows[g])

    assert obj["next"]["literal_witness"]==witness and len(witness)==2
    blend=read_vec(obj["next"]["blend"],len(witness))
    ds_explicit=[]
    for tree,d_expected in witness:
        size,tree_factorial=shape(tree)
        assert size==p+1
        d=tree_factorial*dot(b,phi(B,tree))-1
        assert d==Q(d_expected)
        ds_explicit.append(d)
    assert dot(blend,ds_explicit)==1
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all paid denominators and 66×40 fold identities")
    print(f"PASS weighted left inverse (5×7 times 7×5), normalized transpose, real chronology, all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print(f"PASS both literal size-{p+1} defects and unit blend; no larger tree or dual-word enumeration")
    print(f"Next defect blend: {[str(x) for x in blend]}")


if __name__ == "__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("receipt",type=Path)
    arg.add_argument("source",type=Path)
    opt=arg.parse_args()
    a=(opt.source/"tableau-15-weighted.json").read_bytes()
    w=(opt.source/"witness-15-weighted.json").read_bytes()
    assert sha256(a).hexdigest()==ARCHIVE
    assert sha256(w).hexdigest()==NEXT
    run(json.loads(opt.receipt.read_text()),json.loads(a),json.loads(w))
