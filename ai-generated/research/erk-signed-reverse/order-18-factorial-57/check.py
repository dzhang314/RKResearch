"""Independent exact audit of the distinct factorial-unit 57-stage order-18 upper literal."""
import argparse
from fractions import Fraction
from hashlib import sha256
from math import factorial, gcd,lcm,prod
from itertools import permutations
from pathlib import Path
import json

P=18
PAID=factorial(P)
OLD_TABLEAU="adec0df152d14550aeb54fa8a095d6f3ad9974120f6a5f6f49b903affd389b61"
OLD_LOCALIZED="893805a7d652e00335375ce881ed7c3c98f7c06d0927a813edb59b160a20d7b4"
OLD_F="0ae5e7485fd9e2f9de0c8567322bfcc2c6660234e0de7511030727e89d17b40d"
OLD_R="6e30391531df8dec51c5a6252001ddbfce4a5f9dbbc7c19cdb05379c16d14a93"
PINS=((-2487,-6632,1473,3928,5433,14488,9393,25048),)
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
    alpha=(136080,-272160,204120,-34020)
    suffix=("CACCACCACC","CACCACCAAC","CACCACCCCC","CACCCCCCCC")
    prefixes=("CCCCCCAA","AAAAAAAA")
    target=(Q(4793,259683840),Q(-41,3525120))
    defects=[]; paid_terms=[]; observed=[]
    for entry,prefix,expect in zip(data["grafts"],prefixes,target,strict=True):
        assert entry["prefix"]==prefix
        dr=[]; ws=[]; rr=[]
        for (t,k,txt,flag),a,u in zip(entry["terms"],alpha,suffix,strict=True):
            assert t==word(prefix+u) and k==a
            n,f=shape(t)
            assert n==P+1 and f%(P+1)==0
            r=dot(b,phi(B,t)); e=f*r-1
            assert r==Q(txt) and e==Q(flag)
            dr.append(e); rr.append(r); ws.append(Q(a,f//(P+1)))
        assert dot(alpha,rr)==expect==Q(entry["raw"])
        assert sum(ws)==0 and dot(ws,dr)==(P+1)*expect
        assert all(paid(a) for a in ws)
        defects.append(dr); paid_terms.append(ws); observed.append(expect)
    kappa=data["raw_blend"]
    assert all(type(x) is int for x in kappa) and dot(kappa,observed)==1
    proof19=sum(k*dot(w,e) for k,w,e in zip(kappa,paid_terms,defects,strict=True))
    assert proof19==19
    bush=dot(b,phi(B,[[] for _ in range(P)])); bushq=(P+1)*bush-1
    assert bush==Q(data["bush_output"]) and bushq==Q(data["bush_defect"])
    assert bush*proof19-bushq==1 and paid(bush)
    d=lcm(*(v.denominator for r in B for v in r))
    e=lcm(*(v.denominator for v in b)); scale=e*d**P
    es=[]
    for i,j,z in data["picked"]:
        q=bushq if i==-1 else defects[i][j]
        assert q==Q(z) and paid(q)
        es.append(q)
    w=data["blend"]
    assert len(w)==len(es)==2 and all(type(x) is int for x in w)
    assert dot(w,es)==1
    num=[v*scale for v in es]
    assert all(v.denominator==1 for v in num) and dot(w,num)==scale
    assert PAID%19 and d%19 and e%19 and scale%19
    assert all(int(v)%19==(-scale)%19 for v in num)
    print("PASS two actual four-tree next grafts, integer raw blend +1:",list(map(str,observed)),kappa)
    print("PASS cleared graft/bush identity without inverse 19 and independent actual two-defect blend:",
          list(map(str,es)),w)
    print("PASS next numerators modulo 19:",PAID%19,d%19,e%19,scale%19,[int(v)%19 for v in num])

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
    k=len(rows)
    return sum(((-1)**sum(p[i]>p[j] for i in range(k) for j in range(i+1,k)))*
               prod(rows[i][p[i]] for i in range(k)) for p in permutations(range(k)))

def shape_and_pairing(obj,ns,p,c,beta,N,rev):
    radii=tuple(map(Q,("1/5","2/3","2","5")))
    chosen=sorted(sign*v for v in radii for sign in (-1,1))
    grid=sorted([Q(0)]+[sign*Q(v) for v in ("1/5","1/3","1/2","2/3","1","3/2","2","5") for sign in (-1,1)])
    pure=tuple(map(Q,("-3/2","-1/2","-1/3","0","1/3","1/2","3/2")))
    assert list(map(Q,obj["scalar_sites"]))==grid
    assert list(map(Q,obj["receiver_sites"]))==chosen
    assert tuple(map(Q,obj["pure_late_sites"]))==pure
    assert tuple(map(tuple,obj["pins"]))==PINS
    assert {1-2*x for x in c[-15:]}==set(pure)-{Q(-3,2),Q(3,2)}|{Q(-1),Q(1)}
    weights={a:cardinal_mass(a,grid) for a in grid}
    assert list(map(Q,obj["receiver_masses"]))==[weights[a] for a in chosen]
    aggregate={}
    for x,b in zip(c,beta,strict=True): a=1-2*x; aggregate[a]=aggregate.get(a,0)+b
    assert all(aggregate.get(k,0)==v for k,v in weights.items())
    assert all(a in weights or b==0 for a,b in aggregate.items())
    rec=obj["weighted_receivers"]
    assert rec==list(range(45,37,-1))
    assert [1-2*c[i] for i in rec]==chosen and all(beta[i]==weights[a] for i,a in zip(rec,chosen,strict=True))
    taps=[sum(bool(row[i]) for row in N) for i in rec]
    assert all(taps)
    H=read_vec(obj["high7_weights"],15,P)
    clk=[2*sum(x)-1 for x in rev]
    pin=lambda f:dot(H,[eval_poly(f,x) for x in clk])
    assert pin([1,1])==Q(77,8) and paid(1/pin([1,1]))
    axes=read_mat(obj["right_axes"],6,8,P)
    expected=[]
    for j in range(1,7):
        q=[Q(0)]*j+[Q(1),Q(1)]+[Q(0)]*(6-j)
        t=pin(q)/pin([1,1]);q[0]-=t;q[1]-=t
        expected.append(q)
    assert axes==expected
    meas=read_mat(obj["measurement"],8,6,p)
    assert meas==[[weights[x]*eval_poly(q,x) for q in axes] for x in chosen]
    inv=read_mat(obj["left_inverse"],6,8,p)
    assert compose(inv,meas)==[[Q(i==j) for j in range(6)] for i in range(6)]
    m=obj["minor_identity"];d=m["den"]
    assert paid(Q(1,d))
    ints=[]
    f=[]
    for (ids,num,core,k),r,y in zip(m["terms"],radii,[Q(8184,5),Q(200232,125),Q(-192984,125),Q(-24746,125)],strict=True):
        assert ids==[i for i,a in enumerate(chosen) if abs(a)!=r]
        rr=[[x*d for x in meas[i]] for i in ids]
        assert all(x.denominator==1 for u in rr for x in u)
        z=direct_det(rr); assert z==int(num) and z.denominator==1
        assert int(core)==(1 if z>0 else -1)*paid_remainder(z.numerator,PAID)
        ints.append(int(core)); f.append(int(k))
        assert pin(pmul([Q(1),Q(1)],nodal([chosen[i] for i in ids])))==y
    assert dot(ints,f)==1
    q=nodal(pure)
    piv=dot(PINS[0],q)
    assert piv==Q(-27200,3) and paid(1/piv)
    basis=read_mat(obj["pure_late_basis"],7,10,p)
    for a,u in zip(pure,basis,strict=True):
        assert [eval_poly(u,x) for x in pure]==[int(a==x) for x in pure]
        assert all(dot(r,div_H(u))==0 for r in PINS)
        assert eval_poly(u,-1)==eval_poly(u,1)==0
    print("PASS eight weighted receivers with normalized taps",taps,
          "and a paid 6-by-8 inverse; four symmetric deletion determinants")
    print("PASS left pin on seven pure clocks with pivot -27200/3")

def check_charts(obj,A,L,DF,c,prior_f,prior_r):
    assert prior_f["p"]==20 and prior_f["nf"]==27 and prior_f["m"]==9
    assert prior_r["p"]==15 and prior_r["nf"]==15 and prior_r["m"]==7
    def old_block(o,key):
        b=o[key]; d=int(b["den"])
        assert d*int(b["pay_cofactor"])==factorial(o["p"])**b["pay_exp"]
        return [[Q(int(x),d) for x in row] for row in b["num"]]
    assert [row[:27] for row in A[:27]]==[r[:27] for r in old_block(prior_f,"A_unfolded")[:27]]
    assert DF==old_block(prior_f,"DF")[:18]
    assert not any(x for row in L[-15:] for x in row[:-15])
    R=[row[-15:][::-1] for row in L[-15:][::-1]]
    assert R==[r[:15] for r in old_block(prior_r,"A_unfolded")[:15]]
    D=read_mat(obj["reverse_decoder"],7,15,P)
    H=read_vec(obj["high7_weights"],15,P)
    time=[sum(x) for x in R]
    count=0
    for k,item in enumerate(prior_r["forward"][:8]):
        for v in item["cols"]:
            z,y=list(map(int,v[:-1])),int(v[-1])
            if k<7: assert act(D,z)==[int(j==k)*y for j in range(7)]
            assert dot(H,z)==y*dot(H,[x**k for x in time])
            count+=1
    assert c[15]==0 and c[21]==1 and A[27+15]==A[0] and A[27+21]==A[16]
    assert sum(L[15])==1 and not any(L[21])
    assert (obj["owner"][42],obj["owner"][48])==(obj["owner"][0],obj["owner"][16])
    assert [sum(v/(k+1) for k,v in enumerate(col)) for col in tpose(DF)]==A[16][:27]
    print("PASS unchanged prior 27/15 chart entries and exact lower/high reverse tests",count,
          "with unfolded literal aliases 42→0 and 48→16")
    return R

def run(obj, archive, prior_f, prior_r):
    p,m,g = obj["p"],obj["m"],obj["g"]
    assert obj["schema"]=="rk-weighted-upper-structural-paired-oriented-v1"
    assert p==P and m==9 and g==7 and p==m+g+2 and p<=2*m+2
    nf,ns,count = obj["nf"],obj["ns"],obj["final"]
    assert (nf,ns,count)==(27,61,57)
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
    R=check_charts(obj,A,L,DF,c,prior_f,prior_r)
    shape_and_pairing(obj,ns,p,c,beta,N,R)

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
                assert all(dot(s,div_H(w))==0 for s in PINS)
                for a,value in enumerate(act(source_rows[g],residual)):
                    assert value==0, ("high_source",g,a,n,basis_index,str(value))
                    high_count+=1

    common=lcm(*(x.denominator for row in B for x in row),*(x.denominator for x in b))
    assert common==int(archive["coefficient_common_denominator"])
    assert paid_remainder(common,PAID)==1 and PAID**5%common==0
    wt=lcm(*(x.denominator for x in b))
    assert wt==10170998716342464000 and PAID**4%wt==0
    next_audit(B,b,obj["next"])
    print(f"PASS p={p}: original {nf}+{ns}, final={count}, all factorial-paid denominators and {nr*count} fold identities")
    print(f"PASS signed normalized transpose and all {p} scalar moments")
    print(f"PASS {transition_count} dual column transitions, {low_count} scalar low-source zeros")
    print(f"PASS {f_count} forward attachments through size {m+1}, {chart_count} low and {high_count} high chart entries")
    print("literal common denominator:",common,"divides 18!^5")


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("candidate",type=Path)
    cli.add_argument("receipt",type=Path)
    cli.add_argument("old_forward_receipt",type=Path)
    cli.add_argument("old_reverse_receipt",type=Path)
    args=cli.parse_args()
    assert sha256((args.source/"tableau-18-weighted.json").read_bytes()).hexdigest()==OLD_TABLEAU
    assert sha256((args.source/"order-18-localized-59/tableau-18-localized-59.json").read_bytes()).hexdigest()==OLD_LOCALIZED
    assert sha256(args.candidate.read_bytes()).hexdigest() not in (OLD_TABLEAU,OLD_LOCALIZED)
    f,r=args.old_forward_receipt.read_bytes(),args.old_reverse_receipt.read_bytes()
    assert sha256(f).hexdigest()==OLD_F and sha256(r).hexdigest()==OLD_R
    run(json.loads(args.receipt.read_bytes()),json.loads(args.candidate.read_bytes()),json.loads(f),json.loads(r))
