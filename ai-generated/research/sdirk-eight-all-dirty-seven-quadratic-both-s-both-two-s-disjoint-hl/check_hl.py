from projection_hl import *
from number_field import field,spec,gcd,trim
from sympy.polys.rings import ring

B=ip(b.n)
def classify(rank,mode,gg,eq,guards,note=''):
    fs=gg.factor()[1]
    print(mode,rank,'factor degrees + powers',[(f.total_degree(),s) for f,s in fs],note,flush=True)
    ret=[]
    for f,power in fs:

        P,K,u=field(f)
        R,av=ring('a',K)
        E=[spec(j,R,u) for j in eq];E.sort(key=lambda e:e.degree() if e else 10**9)
        G=R.zero
        for e in E:
            if not e:continue
            G=gcd(G,e%G if G else e)
            if G.degree()==0:break
        assert G
        before=int(G.degree());removed=[]
        for name,gs in guards.items():
            for j,g in enumerate(gs):
                assert not g.degrees()[2]
                v=spec(g,R,u)
                dv=int(G.degree())
                G=trim(G,v) if v else R.one
                if G.degree()!=dv:removed.append((name,j,int(G.degree())))
                if G.degree()==0:break
            if G.degree()==0:break
        print(mode,rank,'H-degree',f.total_degree(),'gcd',before,'reduced',G.degree(),'removed',removed,flush=True)
        ret.append((f,G,removed))
    return ret

def r0(mode):
    gg,eq,masks=rankzero(mode)
    expected=[(2,1),(2,1),(6,1),(6,1),(2,3)]
    assert [(f.total_degree(),e) for f,e in gg.factor()[1]]==expected
    fibers=classify('R-rankzero',mode,gg,eq,masks)
    assert [info for _,g,info in fibers]==[
        [('front',1,0)],[('front',1,0)],[('front',3,0)],
        [('base',3,0)],[('front',2,0)]]
    assert all(g.degree()==0 for _,g,_ in fibers)
def b_fibres(mode,C,eq,masks,name):
    out=[]
    for f,Ga,_ in C:
        if Ga.degree()==0:continue
        P,K,hh=field(f)
        assert Ga.degree()==1
        a0=-Ga.get((0,),K.zero)
        R,bb=ring('b',K)
        def sp(p):
            return R.from_dict({(j,):ev_a(q) for j,q in enumerate(coeffs(p))})
        def ev_a(q):
            rr=ring('a',K)[0]
            return spec(q,rr,hh).evaluate(0,a0)

        G=R.zero
        es=[sp(x) for x in eq];es.sort(key=lambda e:e.degree() if e else 10**9)
        for e in es:
            if not e:continue
            G=gcd(G,e%G if G else e)
            if G.degree()==0:break
        assert G
        before=G.degree();removed=[]
        for key,gs in masks.items():
            for i,g in enumerate(gs):
                if G.degree()==0:break
                v=sp(g);dv=G.degree()
                G=trim(G,v) if v else R.one
                if G.degree()!=dv:removed.append((key,i,G.degree()))
            if G.degree()==0:break
        print(mode,name,'H-degree',f.total_degree(),'b gcd',before,'reduced',G.degree(),'removed',removed,flush=True)
        out.append((f.total_degree(),int(before),int(G.degree()),removed))
    return out

def regular(mode):
    eq,masks=frame(mode,'regular')
    gam,E,G,Y=eq
    base={key:[z for z in gs if not z.degrees()[2]] for key,gs in masks.items()}
    pure=[z for z in sum(base.values(),[]) if not z.degrees()[1]]
    bg=sum(base.values(),[])
    P=[strip(gam.resultant(z,'b'),bg) for z in (E,G,Y)]
    pp=P[0].gcd(P[1]).gcd(P[2]);assert pp
    (Q,kpow),=pp.factor()[1]
    assert Q.degrees()==(2,4,0) and kpow==2
    phi=N(a/2)/D(a/2)
    n=ip((a+b-2*H-H*(phi-1)*(H-b)/a).n)
    m=ip((a+b-2*H-H*(k(b)-1)*(H-a)/b).n)
    H0=ip(H.n);a0=ip(a.n)
    # H and H-a are always nonzero.
    assert (Q*H0*(H0-a0)).gcd(n.resultant(m,'b'))==Q*H0*(H0-a0)
    J,K=coeffs(m)
    c0,c1,c2=coeffs(gam)
    assert not (c0*K*K-c1*J*K+c2*J*J)%Q
    L=K*c2*B+K*c1-J*c2
    # Exact identity: on Q=0 and when m != 0, a root gamma forces L=0.
    assert (K*K*gam-(K*B+J)*L).degrees()[2]==0
    assert not (K*K*gam-(K*B+J)*L)%Q
    vs=[z.resultant(L,'b')%Q for z in (E,G,Y)]
    hp=[strip(Q.resultant(v,'a'),pure) for v in vs]
    gg=hp[0].gcd(hp[1]).gcd(hp[2]);assert gg
    assert all(v for v in vs)
    assert [(g.total_degree(),e) for g,e in gg.factor()[1]]==[(28,2),(2,5),(7,10)]
    print(mode,'regular projection degree (H,a) schemas:',[z.degrees() for z in P],[(v.degrees()) for v in vs],flush=True)
    C=classify('R regular / K != 0',mode,gg,[Q,*vs],base|{'R slope':[K]})
    # K zero exceptional fibers are handled separately with the original equations.
    leading_drop=strip(Q.resultant(K,'a'),pure)
    D0=classify('R regular / K=0',mode,leading_drop,[Q,K],base|{'R constant coefficient':[J]})
    assert [(f.total_degree(),e) for f,e in leading_drop.factor()[1]]==[(2,1),(7,1)]
    assert [info for _,_,info in C]==[[],[('R slope',0,0)],[('R slope',0,0)]]
    assert [info for _,_,info in D0]==[[('R constant coefficient',0,0)],[]]
    assert b_fibres(mode,C,[*eq,L],masks,'K !=0 lifted')==[(28,1,0,[('R_scale',0,0)])]
    assert b_fibres(mode,D0,eq,masks,'K=0 lifted')==[(7,0,0,[])]
def main():
    for mode in CASES:
        r0(mode)
        regular(mode)
    print('complete paid high/low disjoint chart excluded in characteristic zero',flush=True)

if __name__=='__main__':main()
