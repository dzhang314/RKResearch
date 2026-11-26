"""Independent exact audit of the localized 59-stage order-18 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
from math import comb, factorial, gcd,lcm,prod
from pathlib import Path
import json

P=18
EXTRA=(59,739,2137,8179)
PAID=factorial(P)*prod(EXTRA)
OLD_TABLEAU="adec0df152d14550aeb54fa8a095d6f3ad9974120f6a5f6f49b903affd389b61"
OLD_WITNESS="2837187821c0a812b5119e5ad69e105feb5fdc19a5e907d50fafab26dd901147"
OLD_FINITE="5cb49914769651b66c5650a2ef35eab0c6925faadc32451657345fac85cd21b4"
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


def word_tree(word):
    t=[]
    for op in reversed(word):
        t=[t] if op=="A" else t+[[]]
    return t


def next_audit(B,b,claimed,previous):
    # These are the same two fixed shapes as in the 60-stage archive.
    raw=claimed["literal_witness"]
    assert len(raw)==len(previous)==2 and raw==previous
    values=[]
    d=lcm(*(x.denominator for row in B for x in row))
    e=lcm(*(x.denominator for x in b))
    scale=e*d**18
    for t,expected in raw:
        n,q=shape(t)
        assert n==19
        result=q*dot(b,phi(B,t))-1
        assert result==Q(expected)
        assert paid_remainder(result.denominator,PAID)==1 and result.denominator%19!=0
        values.append(result)
    blend=read_vec(claimed["blend"],2,P)
    assert all(x.denominator==1 for x in blend)
    assert dot(blend,values)==1
    nums=[x*scale for x in values]
    assert all(x.denominator==1 for x in nums) and dot(blend,nums)==scale
    assert PAID%19!=0 and d%19!=0 and e%19!=0 and scale%19!=0
    assert all(int(x)%19==(-scale)%19 for x in nums)

    coeff=(136080,-272160,204120,-34020)
    words=("ACCACC","ACCAAC","ACCCCC","CCCCCC")
    balanced,combination=Q(0),Q(0)
    for (t,a,z),coef,word in zip(claimed["balanced_graft"],coeff,words,strict=True):
        assert t==word_tree("CCCCCCCCACCC"+word)
        size,q=shape(t)
        assert size==19 and q%19==0
        assert Q(a)==Q(coef,q//19)
        assert paid_remainder(Q(a).denominator,PAID)==1
        v=q*dot(b,phi(B,t))-1
        assert v==Q(z)
        balanced+=Q(a)
        combination+=Q(a)*v
    assert balanced==0 and combination==19
    bush=dot(b,phi(B,[[] for _ in range(18)]))
    Bdef=19*bush-1
    assert bush==Q(claimed["bush_raw"]) and Bdef==Q(claimed["bush_defect"])
    assert paid_remainder(bush.denominator,PAID)==1
    assert bush*combination-Bdef==1
    print("PASS both actual size-19 defects and integer unit blend",list(map(str,values)),list(map(str,blend)))
    print("PASS formal next graft yields 19, and the actual bush gives the joint unit identity without inversion")
    print("PASS no payment of 19; mod 19 base, d, e, scale, both numerators:",
          PAID%19,d%19,e%19,scale%19,[int(x)%19 for x in nums])


def poly_mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c


def ev(a,v):
    return sum(x*v**i for i,x in enumerate(a))


def mean(a):
    return sum(x/(i+1) for i,x in enumerate(a) if i%2==0)


def old_pins(obj,p):
    nodes=tuple(map(Q,("-1/3","1/3","-1/5","5")))
    H=list(map(Q,(1,0,-1)))
    omega=poly_mul(H,H)
    weights=[]
    for a in nodes:
        card=[Q(1)]
        for z in nodes:
            if z!=a:
                card=poly_mul(card,[-z/(a-z),Q(1)/(a-z)])
        weights.append(mean(poly_mul(omega,card))/ev(omega,a))
    m=[mean([Q(0)]*j+[Q(1)]) for j in range(9)]
    ell=[sum(z*x**j for x,z in zip(nodes,weights,strict=True)) for j in range(9)]
    assert m==read_vec(obj["mu_poly"],9,p) and ell==read_vec(obj["ell_poly"],9,p)
    return H,m,ell


def determinant(a):
    n=len(a)
    return sum(((-1)**sum(s[i]>s[j] for i in range(n) for j in range(i+1,n)))*
               prod(r[j] for r,j in zip(a,s,strict=True)) for s in permutations(range(n)))


def check_geometry(obj,beta,c,N,p):
    selected=tuple(map(Q,("-5","-3/2","-2/3","1/5","2/3","3/2")))
    grid=sorted([Q(0)]+[s*Q(x) for x in ("1/5","1/3","1/2","2/3","1","3/2","2","5") for s in (-1,1)])
    weights={a:cardinal_mass(a,grid) for a in grid}
    assert list(map(Q,obj["selected_masses"]))==[weights[a] for a in selected]
    assert tuple(map(Q,obj["interpolation_sites"]))==selected
    rec=obj["weighted_receivers"]
    assert rec==list(range(52,46,-1))
    assert tuple(1-2*c[i] for i in rec)==selected
    assert all(beta[i]==weights[a] for i,a in zip(rec,selected,strict=True))
    assert all(any(row[i] for row in N) for i in rec)
    assert Q(-1,3) not in selected
    agg={}
    for x,b in zip(c,beta,strict=True):
        a=1-2*x
        agg[a]=agg.get(a,0)+b
    assert all(agg.get(a,0)==b for a,b in weights.items())
    assert all(a in weights or b==0 for a,b in agg.items())
    H,mu,ell=old_pins(obj,p)
    i,j=obj["constraint_pivots"]
    assert (i,j)==(0,1)
    a=H+[Q(0)]*6
    b=[Q(0)]+H+[Q(0)]*5
    assert dot(mu,a)*dot(ell,b)-dot(mu,b)*dot(ell,a)==Q(obj["constraint_determinant"])==Q(-1,378)
    axes=read_mat(obj["receive_axes"],5,9,p)
    for u in axes:
        assert ev(u,Q(-1))==ev(u,Q(1))==dot(mu,u)==dot(ell,u)==0
    meas=read_mat(obj["measurement"],6,5,p)
    assert meas==[[weights[a]*ev(u,a) for u in axes] for a in selected]
    inv=read_mat(obj["left_inverse"],5,6,p)
    assert compose(inv,meas)==[[Q(i==j) for j in range(5)] for i in range(5)]
    cert=obj["minor_certificate"]
    k=int(cert["scale"])
    assert k>0 and paid_remainder(k,PAID)==1
    M=[[k*v for v in r] for r in meas]
    assert all(v.denominator==1 for r in M for v in r)
    matrices=[[[int(x) for x in M[j]] for j in ix] for ix in cert["rows"]]
    assert [tuple(ix) for ix in cert["rows"]]==[(0,1,2,3,4),(0,1,2,3,5),(0,1,2,4,5),(1,2,3,4,5)]
    ds=[determinant(B) for B in matrices]
    assert ds==list(map(int,cert["signed_determinants"]))
    core=[paid_remainder(d,PAID) for d in ds]
    assert core==list(map(int,cert["unpaid_cores"])) and gcd(*core)==1
    ba=list(map(Q,cert["blend"]))
    assert all(paid_remainder(x.denominator,PAID)==1 for x in ba)
    assert dot(ba,ds)==1
    print("PASS six actual weighted live probes, four exact minors with paid stripped gcd 1, and 5-by-6 left inverse")
    return mu,ell


def row_basis(A):
    rows=[r[:] for r in A]
    n=0
    for j in range(len(rows[0])):
        k=next((i for i in range(n,len(rows)) if rows[i][j]),None)
        if k is None: continue
        rows[k],rows[n]=rows[n],rows[k]
        q=rows[n][j]
        rows[n]=[x/q for x in rows[n]]
        for i in range(n+1,len(rows)):
            u=rows[i][j]
            if u: rows[i]=[x-u*y for x,y in zip(rows[i],rows[n],strict=True)]
        n+=1
        if n==len(rows): break
    return rows[:n]


def check_anchors(obj,A,L,p,old,mu,ell):
    # Compare both base banks to the published 60-row finite receipt.
    def qM(name):
        m=old[name]
        q=int(m["den"])
        assert q*int(m["pay_cofactor"])==factorial(18)**m["pay_exp"]
        return [[Q(int(x),q) for x in row] for row in m["num"]]
    pr=qM("A_unfolded")
    old_reverse=[row[-22:] for row in qM("L")[-22:]]
    assert old["p"]==p and old["final"]==60
    assert [row[:22] for row in A[:22]]==[row[:22] for row in pr[:22]]
    assert [row[-22:] for row in L[-22:]]==old_reverse
    assert not any(x for row in L[-22:] for x in row[:-22])
    R=[row[::-1] for row in old_reverse[::-1]]
    clock=[1-sum(row) for row in R]
    raw=read_mat(obj["reverse_decoder"],8,22,p)
    # The decoder uses physical reverse y, while the two pin tests use v.
    D=[[sum(Q(comb(j,k),2**j)*raw[j][i] for j in range(k,8)) for i in range(22)] for k in range(8)]
    U=[[Q(1)]*22+[Q(1)]+[Q(0)]*8]
    counts=[]
    for k in range(9):
        counts.append(len(U))
        for col in U:
            f=col[-9:]
            r=[x-y for x,y in zip(f,act(D,col[:22])+[Q(0)],strict=True)]
            if k<8: assert not any(r)
            else: assert ev(r,Q(-1))==ev(r,Q(1))==dot(mu,r)==dot(ell,r)==0
        if k==8: break
        arr=[]
        for u in U:
            f=u[-9:]
            c=[(f[j]-(f[j-1] if j else 0))/2 for j in range(9)]
            v=[Q(0)]+[f[j-1]/(2*j) for j in range(1,9)]
            v[0]=-ev(v,Q(-1))
            arr.extend([[x*y for x,y in zip(clock,u[:22],strict=True)]+c,
                        act(R,u[:22])+v])
        U=row_basis(arr)
    print("PASS old forward/reverse banks unchanged; actual reverse endpoint, mean, promoted ell4 pins at the first missing length",counts)


def run(obj, archive, witness, old):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-localized-59-v1"
    assert p==P and m==g==8 and p==2*m+2 and tuple(obj["extra_inversions"])==EXTRA
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(22,75,59)
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
    mu,ell=check_geometry(obj,beta,c,N,p)
    check_anchors(obj,A,L,p,old,mu,ell)

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
    assert extra==59**2*739*2137*8179
    d=lcm(*(x.denominator for row in B for x in row))
    e=lcm(*(x.denominator for x in b))
    assert d==2570857282896634592100013488102355968000000000000
    assert e==10170998716342464000
    assert PAID**6%d==0 and PAID**4%e==0
    next_audit(B,b,obj["next"],witness)
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all paid denominators and {nr*count} fold identities")
    print(f"PASS signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print("literal common denominator:",common)
    print("literal denominator part outside 18 factorial:",extra)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path)
    cli.add_argument("old_finite",type=Path)
    args=cli.parse_args()
    assert sha256((args.source/"tableau-18-weighted.json").read_bytes()).hexdigest()==OLD_TABLEAU
    assert sha256(args.candidate.read_bytes()).hexdigest()!=OLD_TABLEAU
    old=args.old_finite.read_bytes()
    assert sha256(old).hexdigest()==OLD_FINITE
    witness=(args.source/"witness-18-weighted.json").read_bytes()
    assert sha256(witness).hexdigest()==OLD_WITNESS
    run(json.loads(args.receipt.read_text()),json.loads(args.candidate.read_text()),json.loads(witness),json.loads(old))
