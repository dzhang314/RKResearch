"""Independent exact audit of the 25-stage factorial-unit order-12 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
from math import comb, factorial, gcd,lcm,prod
from pathlib import Path
import json

P=12
PAID=factorial(P)
OLD_TABLEAU="55f54bc0b997aaa06464b62642e477fed1db1d24d1fe14e382c2bf2bde1e0869"
OLD_FWD="943498153cdd98b18ea558e1c494c18743acbd31fbdbe6e3436eff4af3210365"
OLD_REV="cb9af145968ac79fd97e2677ff2235aa8a2cae9ea55660bda99de2a4ec634998"
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


def next_audit(B,b,claimed):
    raw=claimed["literal_witness"]
    assert len(raw)==2
    vals=[]
    d=lcm(*(x.denominator for row in B for x in row))
    e=lcm(*(x.denominator for x in b))
    scale=e*d**12
    for (t,z), word in zip(raw,("CCCCCACCCACC","CCCCCACCCAAC"),strict=True):
        assert t==word_tree(word)
        n,q=shape(t)
        assert n==13
        val=q*dot(b,phi(B,t))-1
        assert val==Q(z) and paid_remainder(val.denominator,PAID)==1
        vals.append(val)
    assert vals==[Q(1789,6842880),Q(599,855360)]
    bb=read_vec(claimed["blend"],2,P)
    assert all(x.denominator==1 for x in bb) and dot(bb,vals)==1
    nums=[x*scale for x in vals]
    assert all(x.denominator==1 for x in nums) and dot(bb,nums)==scale
    assert PAID%13 and d%13 and e%13 and scale%13
    assert all(int(x)%13==(-scale)%13 for x in nums)

    raw_values=[]
    factor_paid=[]
    for (t,k,v,z), (tree,_), target in zip(claimed["graft"],raw,(1,-2),strict=True):
        assert t==tree and k==target
        n,q=shape(t)
        assert n==13 and q%13==0
        a=dot(b,phi(B,t))
        assert a==Q(v) and q*a-1==Q(z)
        raw_values.append(a)
        factor_paid.append(Q(-622080*k,q//13))
    assert raw_values[0]-2*raw_values[1]==Q(claimed["raw_output"])==-Q(1,622080)
    assert sum(factor_paid)==0 and dot(factor_paid,vals)==13
    u=dot(b,phi(B,[[] for _ in range(12)]))
    assert u==Q(claimed["bush_raw"]) and 13*u-1==Q(claimed["bush_defect"])
    choice=read_vec(claimed["paid_graft_and_bush_blend"],3,P)
    assert choice==[x*u for x in factor_paid]+[Q(-1)]
    assert dot(choice,vals+[13*u-1])==1
    print("PASS two actual size-13 defects and exact integer blend +1",list(map(str,vals)),list(map(str,bb)))
    print("PASS two-tree graft raw -1/622080 and paid graft-plus-bush unit identity")
    print("PASS no inverse of 13; mod 13 base, d, e, scale, both numerators:",
          PAID%13,d%13,e%13,scale%13,[int(x)%13 for x in nums])


def poly_mul(a,b):
    c=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c


def ev(a,v):
    return sum(x*v**i for i,x in enumerate(a))


def mean(a):
    return sum(x/(i+1) for i,x in enumerate(a) if i%2==0)


def pin(f): return ev(f,Q(-1,3))-Q(17,81)*ev(f,Q(1))


def h_div(f):
    z=[]
    for j,c in enumerate(f[:-2]):z.append(c+(z[j-2] if j>=2 else Q(0)))
    assert poly_mul(z,list(map(Q,(1,0,-1))))==f
    return z


def nodal(sites):
    q=[Q(1)]
    for s in sites:q=poly_mul(q,[-s,Q(1)])
    return q


def determinant(a):
    n=len(a)
    return sum(((-1)**sum(s[i]>s[j] for i in range(n) for j in range(i+1,n)))*
               prod(r[j] for r,j in zip(a,s,strict=True)) for s in permutations(range(n)))


def check_geometry(obj,beta,c,N,p):
    selected=tuple(map(Q,("-2/3","-1/6","1/6","1/3","1/2","2/3")))
    grid=sorted([Q(0)]+[s*Q(x) for x in ("1/6","1/3","1/2","2/3","1") for s in (-1,1)])
    weights={a:cardinal_mass(a,grid) for a in grid}
    assert list(map(Q,obj["selected_masses"]))==[weights[a] for a in selected]
    assert tuple(map(Q,obj["interpolation_sites"]))==selected
    rec=obj["weighted_receivers"]
    assert rec==list(range(24,18,-1))
    assert tuple(1-2*c[i] for i in rec)==selected
    assert all(beta[i]==weights[a] for i,a in zip(rec,selected,strict=True))
    assert all(sum(bool(row[i]) for row in N)==3 for i in rec)
    agg={}
    for x,b in zip(c,beta,strict=True):
        a=1-2*x
        agg[a]=agg.get(a,0)+b
    assert all(agg.get(a,0)==b for a,b in weights.items())
    assert all(a in weights or b==0 for a,b in agg.items())
    Hplus=[Q(1),Q(1)]
    assert pin(Hplus)==Q(20,81)
    axes=read_mat(obj["receive_axes"],4,6,p)
    for u in axes: assert ev(u,Q(-1))==pin(u)==0
    meas=read_mat(obj["measurement"],6,4,p)
    assert meas==[[weights[a]*ev(u,a) for u in axes] for a in selected]
    inv=read_mat(obj["left_inverse"],4,6,p)
    assert compose(inv,meas)==[[Q(i==j) for j in range(4)] for i in range(4)]

    cert=obj["minor_certificate"]
    k=int(cert["scale"])
    assert k==86625 and paid_remainder(k,PAID)==1
    M=[[k*v for v in r] for r in meas]
    assert all(v.denominator==1 for r in M for v in r)
    matrices=[[[int(x) for x in M[j]] for j in ix] for ix in cert["rows"]]
    assert [tuple(ix) for ix in cert["rows"]]==[(0,1,2,5),(1,2,3,4)]
    ds=[determinant(B) for B in matrices]
    assert ds==list(map(int,cert["signed_determinants"]))
    core=[paid_remainder(d,PAID) for d in ds]
    assert core==list(map(int,cert["unpaid_cores"]))==[4519681,23245571] and gcd(*core)==1
    ba=list(map(Q,cert["blend"]))
    assert all(paid_remainder(x.denominator,PAID)==1 for x in ba)
    assert dot(ba,ds)==1

    left=tuple(map(Q,obj["left_sites"]))
    assert left==tuple(map(Q,("-1/2","-1/3","0")))
    assert {1-2*x for x in c[-8:]}==set(left)|{Q(-1),Q(1)}
    assert nodal(left)[2]==Q(5,6)
    ls=read_mat(obj["left_axes"],3,6,p)
    for a,u in zip(left,ls,strict=True):
        assert [ev(u,b) for b in left]==[int(a==b) for b in left]
        assert ev(u,-1)==ev(u,1)==h_div(u)[2]==0
    print("PASS six actual weighted observations, both paid minors, actual 4-by-6 inverse, and three-site left projector")


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


def check_anchors(obj,A,L,DF,p,old_f,old_r):
    # Compare both actual banks and the forward decoder to sealed published inputs.
    def qM(old,name):
        m=old[name]
        q=int(m["den"])
        assert q*int(m["pay_cofactor"])==factorial(old["p"])**m["pay_exp"]
        return [[Q(int(x),q) for x in row] for row in m["num"]]
    assert old_f["p"]==11 and old_r["p"]==13
    assert [r[:9] for r in A[:9]]==[r[:9] for r in qM(old_f,"A_unfolded")[:9]]
    assert DF[:11]==qM(old_f,"DF") and allzero(DF[11])
    old_reverse=[row[-8:] for row in qM(old_r,"L")[-8:]]
    assert [row[-8:] for row in L[-8:]]==old_reverse
    assert not any(x for row in L[-8:] for x in row[:-8])
    R=[row[::-1] for row in old_reverse[::-1]]
    clock=[1-sum(row) for row in R]
    raw=read_mat(obj["reverse_decoder"],5,8,p)
    D=[[sum(Q(comb(j,k),2**j)*raw[j][i] for j in range(k,5)) for i in range(8)] for k in range(5)]
    U=[[Q(1)]*8+[Q(1)]+[Q(0)]*5]
    counts=[]
    for k in range(6):
        counts.append(len(U))
        for u in U:
            f=u[-6:]
            r=[x-y for x,y in zip(f,act(D,u[:8])+[Q(0)],strict=True)]
            if k<5: assert not any(r)
            else: assert ev(r,Q(-1))==pin(r)==0
        if k==5: break
        arr=[]
        for u in U:
            f=u[-6:]
            c=[(f[j]-(f[j-1] if j else 0))/2 for j in range(6)]
            v=[Q(0)]+[f[j-1]/(2*j) for j in range(1,6)]
            v[0]=-ev(v,Q(-1))
            arr.extend([[x*y for x,y in zip(clock,u[:8],strict=True)]+c,
                        act(R,u[:8])+v])
        U=row_basis(arr)

    assert A[15]==A[0] and A[16]==A[8] and A[19]==A[7]
    assert [obj["owner"][i] for i in (15,16,19)]==[obj["owner"][i] for i in (0,8,7)]
    print("PASS unchanged 9/8 published banks, full actual reverse pin tests",counts,
          "and unfolded origin, midpoint, endpoint aliases 15→0,16→8,19→7")


def run(obj, archive, old_f, old_r):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-paired25-v1"
    assert p==P and m==g==5 and p==2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(9,33,25)
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
    check_geometry(obj,beta,c,N,p)
    check_anchors(obj,A,L,DF,p,old_f,old_r)

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
                power=[Q(1)]
                w=[Q(0)]*(m+1)
                for j,a in enumerate(residual[:m+1]):
                    for i,v0 in enumerate(power):w[i]+=a*v0
                    power=poly_mul(power,[Q(1,2),Q(-1,2)])
                assert not any(residual[m+1:]) and h_div(w)[2]==0
                for a,value in enumerate(act(source_rows[g],residual)):
                    assert value==0, ("high_source",g,a,n,basis_index,str(value))
                    high_count+=1

    common=lcm(*(x.denominator for row in B for x in row),*(x.denominator for x in b))
    assert common==int(archive["coefficient_common_denominator"])
    assert paid_remainder(common,PAID)==1
    d=lcm(*(x.denominator for row in B for x in row))
    e=lcm(*(x.denominator for x in b))
    assert d==33530112000 and e==138600
    assert PAID**2%d==0 and PAID%e==0
    next_audit(B,b,obj["next"])
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all paid denominators and {nr*count} fold identities")
    print(f"PASS signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print("literal stage and weight denominators:",d,e,"divide 12!^2 and 12! respectively")


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path)
    cli.add_argument("old_forward",type=Path)
    cli.add_argument("old_reverse",type=Path)
    args=cli.parse_args()
    assert sha256((args.source/"tableau-12-weighted.json").read_bytes()).hexdigest()==OLD_TABLEAU
    assert sha256(args.candidate.read_bytes()).hexdigest()!=OLD_TABLEAU
    f,r=args.old_forward.read_bytes(),args.old_reverse.read_bytes()
    assert sha256(f).hexdigest()==OLD_FWD and sha256(r).hexdigest()==OLD_REV
    run(json.loads(args.receipt.read_bytes()),json.loads(args.candidate.read_bytes()),json.loads(f),json.loads(r))
