"""Independent exact audit of the distinct factorial-only 65-stage order-19 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import comb, factorial, gcd,lcm,prod
from pathlib import Path
import json

P=19
PAID=factorial(P)
OLD_TABLEAU="8deda596099f055738100295b68e6898f4dffb6666234ace5ecbceeb7b8b931d"
EARLY_CHART="6e30391531df8dec51c5a6252001ddbfce4a5f9dbbc7c19cdb05379c16d14a93"
ELL=(-2487,-6632,1473,3928,5433,14488,9393,25048)
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


def next_audit(B,b,data):
    blend=data["raw_blend"]
    assert len(blend)==2 and all(type(x) is int for x in blend)
    coeff=(136080,-272160,204120,-34020)
    word_suffixes=("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    initial=("CCCCCCCCA","CCCCCCCAA")
    target=(Q(-714545927,172051236864000),Q(1827349,1290384276480))
    readouts=[]
    row0=[]
    for k,(entry,pref,expected) in enumerate(zip(data["grafts"],initial,target,strict=True)):
        assert entry["prefix"]==pref
        actual=[]
        nominal_coefficients=[]
        for (t,a,raw_txt,def_txt),alpha,post in zip(entry["terms"],coeff,word_suffixes,strict=True):
            assert a==alpha and t==word(pref+post)
            order,tk=shape(t)
            assert order==20 and tk%20==0
            paid_coeff=Q(a,tk//20)
            assert paid_remainder(paid_coeff.denominator,PAID)==1
            nominal_coefficients.append(paid_coeff)
            raw=dot(b,phi(B,t))
            assert raw==Q(raw_txt) and tk*raw-1==Q(def_txt)
            if k==0: row0.append([t,def_txt])
            actual.append(raw)
        assert sum(nominal_coefficients)==0
        assert dot(coeff,actual)==expected==Q(entry["raw"])
        readouts.append(expected)
    assert dot(blend,readouts)==1

    # The first two already included trees also give an independent
    # integer blend of their individual cleared defects.
    ws=data["literal_witness"]
    assert ws==row0[:2]
    a=read_vec(data["blend"],2,P)
    assert all(c.denominator==1 for c in a)
    v=list(map(Q,(val for _,val in ws)))
    assert v==[Q(1511360952889,27528197898240000),
               Q(90845819092109,578092155863040000)]
    assert dot(a,v)==1
    d=lcm(*(x.denominator for row in B for x in row))
    e=lcm(*(x.denominator for x in b))
    scale=e*d**19
    zv=[x*scale for x in v]
    assert all(x.denominator==1 for x in zv) and dot(a,zv)==scale
    bush=dot(b,phi(B,[[] for _ in range(19)]))
    assert bush==Q(data["bush_output"]) and 20*bush-1==Q(data["bush_defect"])
    print("PASS both actual four-tree next grafts, integer raw blend +1:",list(map(str,readouts)),blend)
    print("PASS independent two literal size-20 defects, integer blend +1:",list(map(str,v)),list(map(str,a)))


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


def shape_and_pairing(obj,ns,p,c,beta,N):
    radii=tuple(Q(i,6) for i in (1,4,5,7,8))
    chosen=sorted(sign*v for v in radii for sign in (-1,1))
    grid=sorted([Q(0)]+[Q(sign*i,6) for i in (1,2,3,4,5,6,7,8,12) for sign in (-1,1)])
    pure=tuple(map(Q,("-2","-1/2","-1/3","0","1/3","1/2","2")))
    assert list(map(Q,obj["scalar_sites"]))==grid
    assert list(map(Q,obj["receiver_sites"]))==chosen
    assert tuple(map(Q,obj["pure_late_sites"]))==pure
    assert tuple(obj["ell"])==ELL
    assert {1-2*x for x in c[-21:]}==set(pure)|{Q(-1),Q(1)}
    weights={a:cardinal_mass(a,grid) for a in grid}
    assert list(map(Q,obj["receiver_masses"]))==[weights[a] for a in chosen]
    aggregate={}
    for x,b in zip(c,beta,strict=True):
        a=1-2*x
        aggregate[a]=aggregate.get(a,0)+b
    assert all(aggregate.get(k,0)==v for k,v in weights.items())
    assert all(a in weights or b==0 for a,b in aggregate.items())
    rec=obj["weighted_receivers"]
    assert rec==list(range(ns-22,ns-32,-1))
    assert [1-2*c[i] for i in rec]==chosen and all(beta[i]==weights[a] for i,a in zip(rec,chosen,strict=True))
    assert all(any(row[j] for row in N) for j in rec), "all 10 site rows are actual live inputs"
    meas=read_mat(obj["measurement"],10,8,p)
    assert meas==[[weights[x]*(1+x)*x**j for j in range(8)] for x in chosen]
    inv=read_mat(obj["left_inverse"],8,10,p)
    assert compose(inv,meas)==[[Q(i==j) for j in range(8)] for i in range(8)]
    rem=[paid_remainder(weights[r].numerator,PAID) for r in radii]
    from math import gcd
    assert all(gcd(a,b)==1 for i,a in enumerate(rem) for b in rem[i+1:])
    prod_groups=[prod(weights[x] for x in chosen if abs(x)!=a) for a in radii]
    bl=read_vec(obj["omission_blend"],5,p)
    assert dot(bl,prod_groups)==1

    nodal_hull=nodal(pure)
    assert dot(ELL,nodal_hull)==-31616 and paid_remainder(31616,PAID)==1
    basis=read_mat(obj["pure_late_basis"],7,10,p)
    for a,u in zip(pure,basis,strict=True):
        assert [eval_poly(u,x) for x in pure]==[int(a==x) for x in pure]
        assert dot(ELL,div_H(u))==0 and eval_poly(u,-1)==eval_poly(u,1)==0
    print("PASS ten actual weighted sites, 8-column left inverse, five omission covers; paid parts",rem)
    print("PASS seven existing pure sites, paid latent hull pivot -31616")


def verify_promoted_chart(obj,L,early,p):
    aux=obj["reverse_chart"]
    assert early["p"]==15 and early["nf"]==15 and early["m"]==7
    sites=tuple(map(Q,aux["new_sites"]))
    assert sites==tuple(map(Q,("-2","-1/2","0","1/3","1/2","2")))
    n=len(L)
    # Reverse chronology from the actual signed suffix, not a separately
    # claimed reference array. The first 21 donor rows use no later input.
    assert not any(x for row in L[-21:] for x in row[:-21])
    R=[[L[n-1-i][n-1-j] for j in range(21)] for i in range(21)]
    A=read_mat(aux["old_array"],15,15,p)
    assert all(row[:15]==old and not any(row[15:]) for row,old in zip(R[:15],A,strict=True))
    packed=early["A_unfolded"]
    d=int(packed["den"])
    assert d*int(packed["pay_cofactor"])==factorial(15)**packed["pay_exp"]
    assert [[Q(int(x),d) for x in row[:15]] for row in packed["num"][:15]]==A
    D7=read_mat(aux["old_decoder"],7,15,p)
    D8=read_mat(aux["new_decoder"],8,21,p)
    old=read_vec(aux["old_read"],15,p)
    scalar=read_vec(aux["scalar_read"],8,p)
    pol=nodal((Q(-1),)+sites)
    assert dot(scalar,pol)==Q(aux["pivot"])==-150
    assert paid_remainder(150,PAID)==1
    for i,v in enumerate(sites,15):
        x=(1+v)/2
        target=[sum(x**(k+1)*D7[k][j]/(k+1) for k in range(7)) for j in range(15)]
        assert R[i][:15]==target and not any(R[i][15:])
        assert sum(R[i])==x

    old_feature_checks=0
    for k,sect in enumerate(early["forward"],1):
        for row in sect["cols"]:
            a,z=list(map(int,row[:-1])),int(row[-1])
            if k<=7:
                assert act(D7,a)==[z*int(j==k-1) for j in range(7)]
            # y=(1+v)/2. Normalize with the same forest scalar.
            e=dot(scalar,[Q(comb(k-1,j),2**(k-1)) if j<k else Q(0) for j in range(8)])
            assert dot(old,a)==z*e
            old_feature_checks+=1

    # Verify the arbitrary-data decoder identity on all 21 coefficient
    # columns. The scalar reads are independent by their paid hull pivot.
    def center_poly(y):
        return [sum(Q(comb(j,k),2**j)*y[j] for j in range(k,8)) for k in range(8)]
    for i,coeff in enumerate(tpose(D8)):
        pols=center_poly(coeff)
        assert eval_poly(pols,-1)==int(i==0)
        assert [eval_poly(pols,x) for x in sites]==[int(i==j) for j in range(15,21)]
        assert dot(scalar,pols)==(old[i] if i<15 else 0)
    print("PASS actual 15+6 reverse donor bank, old feature reads",old_feature_checks,
          "and all 21 independent decoder columns; paid hull pivot -150")


def run(obj, archive, early):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-promoted-paired-v1"
    assert p==P and m==9 and g==8 and p==m+g+2 and p<=2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(27,75,65)
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
    shape_and_pairing(obj,ns,p,c,beta,N)
    verify_promoted_chart(obj,L,early,p)

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
                # x=(1-v)/2, using a composed product rather than a basis
                # returned by either the constructor or the receipt generator.
                xp=[Q(1)]
                w=[Q(0)]*(m+1)
                for j,a in enumerate(residual[:m+1]):
                    for i,v in enumerate(xp):
                        w[i]+=a*v
                    xp=pmul(xp,[Q(1,2),Q(-1,2)])
                assert not any(residual[m+1:])
                assert dot(ELL,div_H(w))==0
                for a,value in enumerate(act(source_rows[g],residual)):
                    assert value==0, ("high_source",g,a,n,basis_index,str(value))
                    high_count+=1

    common=lcm(*(x.denominator for row in B for x in row),*(x.denominator for x in b))
    assert common==int(archive["coefficient_common_denominator"])
    assert common==745421537905789863848970240000000000
    assert paid_remainder(common,PAID)==1 and PAID**4%common==0
    next_audit(B,b,obj["next"])
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all factorial-paid denominators and {nr*count} fold identities")
    print(f"PASS signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print("literal common denominator:",common,"divides 19!^4")


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path)
    cli.add_argument("old_grade_seven_receipt",type=Path)
    args=cli.parse_args()
    assert sha256((args.source/"tableau-19-weighted.json").read_bytes()).hexdigest()==OLD_TABLEAU
    early=args.old_grade_seven_receipt.read_bytes()
    assert sha256(early).hexdigest()==EARLY_CHART
    assert sha256(args.candidate.read_bytes()).hexdigest()!=OLD_TABLEAU
    run(json.loads(args.receipt.read_bytes()),json.loads(args.candidate.read_bytes()),json.loads(early))
