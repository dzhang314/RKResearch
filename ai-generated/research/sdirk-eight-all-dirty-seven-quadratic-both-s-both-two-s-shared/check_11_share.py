"""Complete exact six-phase replay: rank/physical guard and fixed-place cases."""
from projection import CASES,project,frame
from number_field import field,spec,gcd,trim,U
from paid_fibre import sp,finite
from sympy.polys.rings import ring
from sympy import isprime,QQ,Poly
RANK={
 'A2A2':[15,21,24,27,9],'A2A3':[29,27,20,20,11],
 'A2S':[25,22,17,13,14],'A3A3':[19,22,19,21,4],
 'A3S':[19,21,19,19,5],'SS':[11,17,13,11,3]}
PROFILE={
 'A2A2':[252,182],'A2A3':[185,151],'A2S':[95,91],
 'A3A3':[191,98],'A3S':[101,55],'SS':[38,25]}
H0=('clocks',1)
t0=('clocks',4)
st=('clocks',10)
N0=('rear_taps',4)
du=('duplicate',0)
af=('affine',0)
GUARD={
 'A2A2':{(2,1):H0,(5,1):t0,(6,1):H0,(7,1):t0,(3,2):t0},
 'A2A3':{(15,1):N0,(12,1):N0,(9,1):st},
 'A2S':{(10,1):st},
 'A3A3':{(8,1):H0,(11,1):du,(12,1):N0,(15,1):N0},
 'A3S':{(10,1):st},
 'SS':{(5,1):du,(8,1):af}}
SITE={
 'A2A2':{(138,1):(19,3,15,'R determinant')},
 'A2A3':{(104,1):(47,24,18,'R determinant')},
 'A2S':{(68,1):(29,22,11,'R determinant')},
 'A3A3':{(48,1):(19,8,1,'R determinant')},
 'A3S':{(8,1):(11,8,9,'R determinant'),(33,1):(31,15,25,'R determinant')},
 'SS':{(10,1):(41,39,16,'fourth')}}
def joint(rows,R,u):
    rr=[r for x in rows if (r:=spec(x,R,u))]
    assert rr
    rr.sort(key=lambda r:r.degree())
    g=rr[0].monic()
    for r in rr[1:]:
        g=gcd(g,r%g)
        if g.degree()==0:break
    return g
def exact_value(a,K,u,v):
    def ev(P):
        return sum(((K.convert(int(c.numerator))/K.convert(int(c.denominator)))
                    *u**int(i)*v**int(j) for (i,j),c in P.to_dict().items()),K.zero)
    return ev(a.n)/ev(a.d)
def rank_zero(mode):
    fs,rows,G,ds=project(mode,'rank')
    assert ds==RANK[mode]
    if mode!='A2A2':
        assert not fs
        return
    assert len(fs)==1
    Q,n=fs[0]
    q,K,u=field(Q)
    assert n==3 and q.monic()==Poly(U**3-3*U**2+1,U,domain=QQ)
    R,_=ring('v',K)
    assert joint(rows,R,u)==R.one
    print('rank-zero cubic has no exact v root',flush=True)
def exact_guard(mode,q,rows,G,key):
    _,K,u=field(q);R,_=ring('v',K)
    d=joint(rows,R,u)
    assert d.degree()==1
    name,i=GUARD[mode][key]
    if name not in ('duplicate','affine'):
        assert trim(d,spec(G[name][i],R,u))==R.one
        print(mode,key,'linear v removed by exact',name,i,flush=True)
        return
    v=-d[(0,)]/d[(1,)]
    lines,r,_,_,data=frame(mode)
    a=lambda x:exact_value(x,K,u,v)
    ll=[tuple(map(a,L)) for L in lines]
    ss=[-x/y for x,y in ll if y]
    assert ss
    lam=ss[0]
    assert lam and all(not (x+lam*y) for x,y in ll)
    if name=='affine':
        assert not (a(r[2][0])+lam*a(r[2][1]))
    else:
        fp,fs,rp,rt=data[7:11]
        assert not (a(fp)-lam*a(rp))
    print(mode,key,'exact forbidden',name,flush=True)
def place(mode,q,rows,key):
    p,u,v,expect=SITE[mode][key]
    assert isprime(p)
    U0=sp(q,p,0,0)
    assert U0.degree()==q.total_degree() and not U0(u) and U0.derivative()(u)
    rr=[sp(a,p,u) for a in rows]
    assert any(r.degree()==a.degrees()[1] and r.degree()>0 for r,a in zip(rr,rows))
    f=rr[0].gcd(rr[1]).gcd(rr[2])
    assert f.degree()==1 and f.roots()==[(v,1)]
    assert finite(p,mode,u,v)==expect
    print(mode,key,'fixed complete place',p,u,v,expect,flush=True)
def run(modes):
    count=0
    for mode in modes:
        rank_zero(mode)
        fs,rows,G,ds=project(mode,'minors')
        assert ds==PROFILE[mode] and len(fs)==len(GUARD[mode])+len(SITE[mode])
        seen=set()
        for q,n in fs:
            key=q.total_degree(),n
            assert key not in seen
            seen.add(key)
            if key in GUARD[mode]:exact_guard(mode,q,rows,G,key)
            else:
                # Verify that the selected mod-prime root is a place of this
                # actual rational irreducible, not merely of a guessed factor.
                field(q)
                place(mode,q,rows,key)
            count+=1
        assert seen==set(GUARD[mode])|set(SITE[mode])
    if len(modes)==6:assert count==23
    print('complete both-S (1,1) shared exclusion',len(modes),'phase pairs',count,'projected fibres',flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or CASES)
