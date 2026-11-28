"""The six exact rank-zero phase charts, including all exceptional fields."""
from projection_rank import CASES,project,CZ
from number_field import field,spec,gcd,trim
from graph_gate import graph
from sympy.polys.rings import ring
PROFILE={
 'A2A2':[61,131],'A2A3':[61,33],'A2S':[61,33],
 'A3A3':[13,8],'A3S':[13,8],'SS':[13,8]}
MASK={
 'A2A2':{(5,1):'clock',(16,1):'graph',(3,5):'clock'},
 'A2A3':{(3,1):'unit'},'A2S':{(3,1):'unit'},
 'A3A3':{(2,1):'clock',(4,1):'graph'},
 'A3S':{(2,1):'clock',(4,1):'graph'},
 'SS':{(2,1):'clock',(4,1):'graph'}}
def sw(a):return CZ.from_dict({(j,i):z for (i,j),z in a.to_dict().items()})
def run(cases):
    total=0
    for mode in cases:
        p,rows,G,ds=project(mode)
        assert ds==PROFILE[mode] and len(p)==len(MASK[mode])
        assert {(q.total_degree(),n) for q,n in p}==set(MASK[mode])
        for q,n in p:
            _,K,u=field(sw(q));R,H=ring('H',K)
            f=lambda a:spec(sw(a),R,u)
            eq=sorted((g for a in rows if (g:=f(a))),key=lambda g:g.degree())
            assert eq
            d=eq[0].monic()
            for a in eq[1:]:d=gcd(d,a%d)
            key=q.total_degree(),n
            out=MASK[mode][key]
            if out=='unit':assert d==R.one
            else:
                assert d.degree()==1
                if out=='clock':assert trim(d,f(G['initial'][3]))==R.one
                else:assert graph(K,u,-d[(0,)]/d[(1,)],mode)==0
            total+=1
            print(mode,key,'exact exclusion',out,flush=True)
    print('complete disjoint-rank-zero',len(cases),'phase pairs',total,'projected fields',flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or CASES)
