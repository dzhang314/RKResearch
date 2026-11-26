"""Independent verifier for the weighted structural receipts at orders 15, 17 and 19."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import json

PIN = {
    15: ("-weighted", "8ce24fdf663adcd88fa368eb89cef7e631d4b57762dd77512340d1f1132648eb",
         "a0c5e75230a38a4dfdf25e13dd047736fdbcba9d805b9fb81dcbe33378e51d7e", 7, (15,51,40)),
    17: ("", "778722276184e24a25a5a1aa3df54a54b48bbd843586d88bfa400b4e48300985",
         "0b45dc1d2837000c4274504036459cbe9a742ceddf4665104305173bfd32fdc4", 9, (27,55,53)),
    19: ("-weighted", "8deda596099f055738100295b68e6898f4dffb6666234ace5ecbceeb7b8b931d",
         "ee3b7654ba1e0fddf8bb70a120650025fcc63f4b404b8e7f988110fdb48b8c8e", 9, (27,79,66)),
}
Q = Fraction


def denominator(d, p):
    q = int(d["den"])
    power, factor = d["pay_exp"], int(d["pay_cofactor"])
    assert q>0 and factor>0 and 0<=power<=64
    assert q*factor == factorial(p)**power
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


def check_mean_projection(shadow, p, g, L, c, U):
    """Reuse the existing actual dual spans with a fixed polynomial projection."""
    s = shadow["old_rows"]
    ns = len(L)
    assert s==22 and g==8 and p==19
    old = list(range(ns-1,ns-s-1,-1))
    assert all(L[i][j]==0 for i in old for j in range(ns-s))
    chart = read_mat(shadow["chart"],g+1,s,p)
    pins = read_mat(shadow["pins"],3,s,p)
    assert allzero(chart[-1])
    for j in range(s):
        col = [row[j] for row in chart]
        assert [r[j] for r in pins]==[col[0],sum(col),sum(v/(k+1) for k,v in enumerate(col))]
    probe = shadow["probe_indices"]
    assert len(probe)==g+1 and len(set(probe))==len(probe)
    assert all(0<=i<ns-s for i in probe)
    y = [1-c[i] for i in probe]
    assert len(set(y))==len(y)
    model = read_mat(shadow["coefficient_projection"],g+1,g+1,p)
    V = [[z**k for k in range(g+1)] for z in y]
    assert compose(V,model)==[[Q(i==j) for j in range(g+1)] for i in range(g+1)]

    def project(u):
        return act(model,[u[i] for i in probe])

    assert project(U[0][0])==[1]+[0]*g
    n_trans=0
    for d,columns in enumerate(U):
        for a,u in enumerate(columns):
            f = project(u)
            assert allzero(f[d+1:]), ("mean_projection_degree",d,a)
            if d<g:
                # Check that the model shift and primitive commute on this
                # generator of the same actual test span.
                c_actual = project([c[i]*u[i] for i in range(ns)])
                l_actual = project(act(L,u))
                c_model = [f[0]]+[f[j]-f[j-1] for j in range(1,g+1)]
                l_model = [0]+[f[j-1]/j for j in range(1,g+1)]
                if c_actual!=c_model:
                    raise AssertionError(("mean_projection_clock",d,a,[str(z-w) for z,w in zip(c_actual,c_model,strict=True)]))
                if l_actual!=l_model:
                    raise AssertionError(("mean_projection_lift",d,a,[str(z-w) for z,w in zip(l_actual,l_model,strict=True)]))
                n_trans+=2
                read = act(chart,[u[i] for i in old])
                assert read==f, ("mean_projection_short",d,a,[str(z-w) for z,w in zip(read,f,strict=True)])
            else:
                read = act(pins,[u[i] for i in old])
                expected = [f[0],sum(f),sum(v/(k+1) for k,v in enumerate(f))]
                assert read==expected, ("mean_projection_final",d,a,[str(z-w) for z,w in zip(read,expected,strict=True)])
    print(f"PASS old reverse mean and both endpoints using the SAME dual bases: {n_trans} projected transitions, {len(U[-1])} top columns, no extra basis")


def run(obj, archive, witness, p0):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-v1"
    assert p==p0 and m==PIN[p0][3] and g==p-m-2 and p<=2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==PIN[p][4], ("shape",nf,ns,count)
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
    with_mean = p==19
    nrx, ncoef = (9,6) if with_mean else (7,5)
    assert len(rec)==nrx and len(set(rec))==len(rec) and all(0<=i<ns for i in rec)
    meas = read_mat(obj["measurement"],nrx,ncoef,p)
    for i,row in zip(rec,meas,strict=True):
        u = 1-2*c[i]
        if with_mean:
            values = [u**k-(0 if k%2 else Q(3,(k+1)*(k+3))) for k in range(1,ncoef+1)]
        else:
            values = [u**k for k in range(ncoef)]
        assert row==[beta[i]*(1-u*u)*v for v in values], ("measurement",i)
    inv = read_mat(obj["left_inverse"],ncoef,nrx,p)
    assert compose(inv,meas)==[[Q(i==j) for j in range(ncoef)] for i in range(ncoef)]

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

    if with_mean:
        check_mean_projection(obj["reverse_mean_projection"],p,g,L,c,U)

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

    assert obj["next"]["literal_witness"]==witness and len(witness)==2
    blend=read_vec(obj["next"]["blend"],len(witness),p)
    ds_explicit=[]
    for tree,d_expected in witness:
        size,tree_factorial=shape(tree)
        assert size==p+1
        d=tree_factorial*dot(b,phi(B,tree))-1
        assert d==Q(d_expected)
        ds_explicit.append(d)
    assert dot(blend,ds_explicit)==1
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all paid denominators and {nr*count} fold identities")
    print(f"PASS weighted inverse {ncoef}×{ncoef}, normalized transpose, real chronology, all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print(f"PASS both literal size-{p+1} defects and unit blend; no larger tree or dual-word enumeration")
    print(f"Next defect blend: {[str(x) for x in blend]}")


if __name__ == "__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("order",type=int,choices=tuple(PIN))
    arg.add_argument("receipt",type=Path)
    arg.add_argument("source",type=Path)
    opt=arg.parse_args()
    suffix, archive_hash, next_hash, _, _ = PIN[opt.order]
    a=(opt.source/f"tableau-{opt.order}{suffix}.json").read_bytes()
    w=(opt.source/f"witness-{opt.order}{suffix}.json").read_bytes()
    assert sha256(a).hexdigest()==archive_hash
    assert sha256(w).hexdigest()==next_hash
    run(json.loads(opt.receipt.read_text()),json.loads(a),json.loads(w),opt.order)
