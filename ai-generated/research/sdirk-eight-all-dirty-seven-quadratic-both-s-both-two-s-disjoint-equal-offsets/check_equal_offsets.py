"""Trace and actual fourth exact fibres for the same-phase disjoint diagonal."""
from projection_diag import CASES,project
from number_field import field,spec,gcd,trim
from sympy.polys.rings import ring
PROFILE={
 'SS':([47,32,29,11,9],[12]),
 'A3A3':([73,55,48,23,17],[1,12]),
 'A2A2':([121,82,78,26,26],[1,3,24])}
def run(cases):
    count=0
    for mode in cases:
        ps,eq,gs,ds=project(mode)
        d0,tags=PROFILE[mode]
        assert ds==d0 and len(ps)==3 and not ps[2]
        for j,f in enumerate(ps[:2]):
            assert sorted(p.total_degree() for p,n in f)==tags
            assert all(n==1 for p,n in f)
            for h,n in f:
                _,K,H=field(h)
                R,a=ring('a',K)
                g=lambda p:spec(p,R,H)
                rows=sorted((r for i in [0,1,2+j] if (r:=g(eq[i]))),key=lambda x:x.degree())
                assert rows
                r=rows[0].monic()
                for s in rows[1:]:r=gcd(r,s%r)
                assert r.degree()==1
                guard=gs['graph_anchors'][0] if h.total_degree()>=12 else gs['known'][6]
                assert trim(r,g(guard))==R.one
                count+=1
                print(mode,'plus' if j==0 else 'minus',h.total_degree(),
                      'exact a linear forbids L4(d)' if h.total_degree()>=12 else
                      'exact a linear forbids t=0',flush=True)
    if len(cases)==3:assert count==12
    print('all same-law equal-offset phase cases excluded: fibres',count,flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or CASES)
