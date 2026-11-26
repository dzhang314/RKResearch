"""Independent exact checker of the shared paid ERK18/60 and ERK20/72 proof inputs."""
import argparse
import json
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial, gcd, lcm, prod
from pathlib import Path

CASES = {
    18:(8,22,77,60,"adec0df152d14550aeb54fa8a095d6f3ad9974120f6a5f6f49b903affd389b61",
                  "2837187821c0a812b5119e5ad69e105feb5fdc19a5e907d50fafab26dd901147"),
    20:(9,27,91,72,"a08c3229cd058edf41eb91241852166fcdf2f0712d10a850539c07b278bb9cb3",
                  "85fe4ade0371313977dbeb5c5adf2c990871e25ef4beb9103684989c3830a841"),
}



def bound(path,h):
    raw=path.read_bytes()
    assert sha256(raw).hexdigest()==h, path
    return json.loads(raw)


def denominator(p,packed):
    d,e,k=int(packed["den"]),int(packed["pay_cofactor"]),packed["pay_exp"]
    assert d>0 and e>0 and type(k) is int and 0<=k<=64
    assert d*e==factorial(p)**k
    return d


def packed_matrix(p,v,rows,cols):
    d=denominator(p,v)
    assert len(v["num"])==rows and all(len(x)==cols for x in v["num"])
    return [[Q(int(x),d) for x in row] for row in v["num"]]


def packed_vector(p,v,n):
    d=denominator(p,v)
    assert len(v["num"])==n
    return [Q(int(x),d) for x in v["num"]]


def dot(v,w):
    return sum(x*y for x,y in zip(v,w,strict=True))


def mv(a,v):
    return [dot(row,v) for row in a]


def cols(x):
    return list(zip(*x,strict=True))


def product(a,b):
    return [[dot(row,col) for col in cols(b)] for row in a]


def eval_poly(q,v):
    r=Q(0)
    for x in reversed(q):
        r=r*v+x
    return r


def mul_poly(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            r[i+j]+=x*y
    return r


def mean(q):
    return sum(a/(i+1) for i,a in enumerate(q) if i%2==0)


def cardinal(nodes,a):
    num,den=[Q(1)],Q(1)
    for v in nodes:
        if v!=a:
            num=mul_poly(num,[-v,Q(1)])
            den*=a-v
    return [v/den for v in num]


def split_check(receipt,p,g,c,beta,N,L,mget):
    split=receipt["split"]
    v=Q(split["center"])
    live,negative,grid=(split[k] for k in ("live","negative","quadrature"))
    assert (v,live,negative,grid)==((-Q(1,3),54,25,21) if p==18 else (Q(0),63,26,21))
    assert 1-2*c[live]==1-2*c[negative]==1-2*c[grid]==v
    assert L[live]==L[negative]==L[grid], "actual reverse split/pure rows"
    assert beta[live]==1 and beta[negative]==-1
    assert any(row[live] for row in N), "actual live taps"
    assert not any(row[negative] or row[grid] for row in N)
    sites=list(map(Q,split["scalar_grid"]))
    core=(Q(1,5),Q(1,3),Q(1,2),Q(2,3),Q(1),Q(3,2),Q(2),Q(5)) if p==18 else tuple(Q(i,6) for i in (1,2,3,4,5,6,7,8,12))
    assert sites==sorted([Q(0)]+[sgn*z for z in core for sgn in (-1,1)])
    weight={a:mean(cardinal(sites,a)) for a in sites}
    observed={}
    for x,b in zip(c,beta,strict=True):
        a=1-2*x
        observed[a]=observed.get(a,Q(0))+b
    assert beta[grid]==weight[v]
    assert all(observed.get(a,0)==b for a,b in weight.items())
    assert all(a in weight or b==0 for a,b in observed.items())

    rec=receipt["weighted_receivers"]
    rows,modes=(6,4) if p==18 else (9,7)
    assert len(rec)==len(set(rec))==rows and all(0<=i<len(c) for i in rec)
    assert not {live,negative,grid}.intersection(rec)
    assert all(beta[i]==weight[1-2*c[i]] for i in rec)
    axes=mget("axes",modes,g+1)
    for a in axes:
        assert all(eval_poly(a,u)==0 for u in (Q(-1),Q(1),v))
    if p==20:
        # H*v^j (j=1,...,7) after the unit observation at v=0.
        assert axes==[[Q(i==j)-Q(i==j+2) for i in range(g+1)] for j in range(1,8)]
    else:
        # The retaining projection removes the old mean and the ell4 pin,
        # independently of choosing a particular pair of paid pivots.
        nodes=tuple(map(Q,("-1/3","1/3","-1/5","5")))
        omega=list(map(Q,(1,0,-2,0,1)))
        ell=[mean(mul_poly(omega,cardinal(nodes,u)))/eval_poly(omega,u) for u in nodes]
        assert all(mean(a)==0 and dot(ell,[eval_poly(a,u) for u in nodes])==0 for a in axes)
    M=[[beta[i]*eval_poly(a,1-2*c[i]) for a in axes] for i in rec]
    assert M==mget("measurement",rows,modes)
    assert product(mget("left_inverse",modes,rows),M)==[[Q(i==j) for j in range(modes)] for i in range(modes)]
    return dict(centered_split=str(v),live=live,negative=negative,grid_row=grid,
                grid_mass=str(beta[grid]),split_live_taps=sum(bool(row[live]) for row in N),
                weighted_measurement_shape=[rows,modes])


def tree_factorial_and_value(A,t):
    out=[Q(1)]*len(A)
    n,fact=1,1
    for child in t:
        k,den,y=tree_factorial_and_value(A,child)
        n+=k
        fact*=den
        out=[u*w for u,w in zip(out,mv(A,y),strict=True)]
    return n,n*fact,out


def check(source,receipt,p):
    m,f,s,n,ta,tw=CASES[p]
    g=p-m-2
    Aname,Wname=f"tableau-{p}-weighted.json",f"witness-{p}-weighted.json"
    literal,witness=bound(source/Aname,ta),bound(source/Wname,tw)
    assert receipt["inputs"][Aname]==ta and receipt["inputs"][Wname]==tw
    assert receipt["schema"]=="rk-weighted-upper-structural-v1"
    assert tuple(receipt[x] for x in ("p","m","g","nf","ns","final"))==(p,m,g,f,s,n)
    assert p==m+g+2 and p<=2*m+2
    mget=lambda name,r,c:packed_matrix(p,receipt[name],r,c)
    vget=lambda name,r:packed_vector(p,receipt[name],r)
    A, c, beta=mget("A_unfolded",f+s,f+s),vget("clocks",s),vget("beta",s)
    N,L,T=mget("N",s,s),mget("L",s,s),mget("T",s,s)
    DF=mget("DF",p,f)
    assert not any(x for row in DF[m:] for x in row), "DF support"
    assert all(not any(row[i:]) for i,row in enumerate(A)), "unfolded chronology"
    AF=[row[:f] for row in A[:f]]
    for i in range(s):
        assert sum(A[f+i])==c[i]==1-sum(L[i]), ("clock",i)
        for j in range(s):
            assert i<j or N[i][j]==0
            assert L[i][j]==N[i][j]*beta[j]
            assert A[f+i][f+j]==T[i][j]==beta[j]*N[j][i]
            assert beta[i]*T[i][j]==beta[j]*L[j][i]

    E=[[x**j for j in range(p)] for x in c]
    K=[[y-x**(j+1)/(j+1) for j,y in enumerate(row)] for x,row in zip(c,product(T,E),strict=True)]
    assert all(not any(row[f:]) for row in A[:f])
    assert all(row[:f]==[-x for x in a] for row,a in zip(A[f:],product(K,DF),strict=True))
    assert [(j+1)*dot(beta,monomial) for j,monomial in enumerate(cols(E))]==[1]*p

    geometry=split_check(receipt,p,g,c,beta,N,L,mget)

    owner,rep=receipt["owner"],receipt["rep"]
    assert len(owner)==f+s and len(rep)==n
    assert set(owner)==set(range(n)) and rep==sorted(set(rep)) and all(0<=i<f+s for i in rep)
    assert all(owner[i]==j for j,i in enumerate(rep)) and all(rep[o]<=i for i,o in enumerate(owner))
    def fold(v):
        acc=[Q(0)]*n
        for i,x in zip(owner,v,strict=True):
            acc[i]+=x
        return acc
    rows=list(map(fold,A))
    active=owner[f+geometry["live"]]
    passive=owner[f+geometry["negative"]]
    pure=owner[f+geometry["grid_row"]]
    assert passive==pure and active!=pure, "primal literal split owners"
    geometry.update(physical_split=active,physical_plain=pure)
    folded=[rows[i] for i in rep]
    assert all(row==folded[i] for i,row in zip(owner,rows,strict=True))
    b=fold([Q(0)]*f+beta)
    assert all(not any(r[i:]) for i,r in enumerate(folded))
    assert len({tuple(row) for row in folded})==n
    assert len(literal["A"])==len(literal["b"])==n
    assert all(len(r)<=n for r in literal["A"])
    assert folded==[[Q(x) for x in r]+[Q(0)]*(n-len(r)) for r in literal["A"]]
    assert b==list(map(Q,literal["b"]))
    def paid_value(x):
        q=x.denominator
        while q!=1:
            w=gcd(q,factorial(p))
            assert w>1
            q//=w
    for row in folded+[b]:
        for x in row:
            paid_value(x)
    assert lcm(*(x.denominator for row in folded+[b] for x in row))==int(literal["coefficient_common_denominator"])

    packed=receipt["dual"]
    h=denominator(p,receipt["dual_scale"])
    assert len(packed)==g+1
    U=[[[int(x) for x in col] for col in step["cols"]] for step in packed]
    assert U[0]==[[1]*s]
    assert all(us and all(len(u)==s for u in us) for us in U)
    dcount=0
    for d,(r,es) in enumerate(zip(packed[:-1],U[:-1],strict=True)):
        B=cols(U[d+1])
        for which,sub in (("C_scale_cols",lambda u:[x*y for x,y in zip(c,u,strict=True)]),
                          ("L_scale_cols",lambda u:mv(L,u))):
            for u,a in zip(es,r[which],strict=True):
                assert mv(B,list(map(int,a)))==[h*x for x in sub(u)], (which,d)
                dcount+=1
    source_rows=[[mv(cols(K),[x*y for x,y in zip(beta,u,strict=True)]) for u in level] for level in U]
    early=0
    for d,vv in enumerate(source_rows[:-1]):
        for v in vv:
            assert not any(v[:p-d-1]), ("early monomial",d)
            early+=p-d-1

    h=denominator(p,receipt["forward_scale"])
    AF0=[[h*x for x in row] for row in AF]
    assert all(x.denominator==1 for row in AF0 for x in row)
    Fs=receipt["forward"]
    assert len(Fs)==m+1
    F=[None]+[[[int(x) for x in col] for col in step["cols"]] for step in Fs]
    assert F[1]==[[1]*(f+1)]
    assert all(level and all(len(v)==f+1 for v in level) for level in F[1:])
    attach=0
    for k in range(2,m+2):
        basis=cols(F[k])
        pairs=((l,v,w) for l in range(1,k) for v in F[l] for w in F[k-l])
        for (l,v,w),weights in zip(pairs,Fs[k-1]["attach_coords"],strict=True):
            aw=mv(AF0,w[:-1])
            target=[(k-l)*x*y for x,y in zip(v[:-1],aw,strict=True)]+[h*v[-1]*w[-1]]
            assert mv(basis,list(map(int,weights)))==target, ("forward closure",k,l)
            attach+=1
    lower=high=0
    for k in range(1,m+2):
        for v in F[k]:
            r=[(v[-1] if j+1==k else 0)-x for j,x in enumerate(mv(DF,v[:-1]))]
            if k<=m:
                assert not any(r), ("chart below cap",k)
                lower+=p
            else:
                assert not any(mv(source_rows[g],r)), "top chart residual"
                high+=len(source_rows[g])

    next_=receipt["next"]
    assert len(witness)==2 and witness==next_["literal_witness"]
    a=packed_vector(p,next_["blend"],2)
    assert all(x.denominator==1 for x in a)
    next_values=[]
    denA=lcm(*(x.denominator for row in folded for x in row))
    denb=lcm(*(x.denominator for x in b))
    scale=denb*denA**p
    for tree,text in witness:
        size,fac,phi=tree_factorial_and_value(folded,tree)
        val=fac*dot(b,phi)-1
        assert size==p+1 and val==Q(text)
        next_values.append(val)
    assert dot(a,next_values)==1
    numerators=[x*scale for x in next_values]
    assert all(x.denominator==1 for x in numerators)
    assert dot(a,numerators)==scale
    char19=None
    if p==18:
        assert factorial(18)%19==18 and denA%19!=0 and denb%19!=0
        assert all(x.denominator%19!=0 for x in next_values)
        assert scale%19!=0
        assert all(int(z)%19==(-scale)%19 for z in numerators)
        char19={"factorial":factorial(18)%19,"stage_den":denA%19,"weight_den":denb%19,
                "scale":scale%19,"next_numerators":[int(z)%19 for z in numerators]}
    return dict(p=p,m=m,g=g,forward=f,suffix=s,stages=n,alias_rows=f+s-n,
                fold_equalities=(f+s)*n,scalar_moments=p,dual_steps=dcount,
                attachments=attach,early_tests=early,low_chart_entries=lower,top_tests=high,
                split=geometry,next_values=list(map(str,next_values)),
                integer_next_blend=[int(x) for x in a],char19=char19)


def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("source",type=Path)
    cli.add_argument("receipts",type=Path)
    cli.add_argument("orders",type=int,nargs="+",choices=tuple(CASES))
    args=cli.parse_args()
    data=[]
    for p in args.orders:
        data.append(check(args.source,json.loads((args.receipts/f"receipt-{p}.json").read_bytes()),p))
    print(json.dumps(data,indent=2,sort_keys=True))

if __name__=="__main__":
    main()
