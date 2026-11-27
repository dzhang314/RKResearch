"""Generate exact F19 dual-row certificates, using finite_search modular RREF."""
import finite_search as f
from itertools import product
from collections import Counter
from pathlib import Path
f.p=19
P=19

def lin(rows,rhs,n):
    s = f.rref_solve(rows,rhs,n)
    assert s is not None
    return s[0]

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))%P

def compact(row):
    return '#['+', '.join(map(str,row))+']'

stats=Counter()
by_z={}
for z,head,rear in product(range(1,P), list(f.headcharts()), list(f.headcharts())):
    u,w,g,h,ap=head; v,j,r,k,bp=rear
    for a,b in f.centers(z,head,rear):
        assert f.crosspoly(h,f.opN(k),z)
        x=[t%P for t in [1,1+u,1+w,a,b,z-1-j,z-1-v,z-1]]
        pay=[pow(z,j,P)*pow(j+1,-1,P)%P for j in range(7)]
        ev=[[pow(t,j,P) for j in range(7)] for t in x]
        raw=f.rref_solve(list(map(list,zip(*ev))),pay,8)
        if raw is None:
            stats['quad_reject']+=1
            cert=lin(ev+[pay],[0]*8+[1],7)
            receipt='decodeQuad '+compact(cert)
        else:
            free=next(i for i in range(8) if len({s for j,s in enumerate(x) if j!=i})==7)
            keep=[i for i in range(8) if i!=free]
            rows=[lin([ev[t] for t in keep],[int(t==i) for t in keep],7) if i!=free else [0]*7 for i in range(8)]
            dual=[]
            for af in range(P):
                beta=[af if i==free else (dot(pay,rows[i])-af*dot(ev[free],rows[i]))%P for i in range(8)]
                assert all(dot(rr,beta)==t for rr,t in zip(zip(*ev),pay))
                if all(beta) or all(x==0 for x in beta[:3]):
                    stats['seed_reject']+=1
                    if not all(beta):stats['ghost']+=1
                    M=[]
                    for j2 in range(5):
                        wt=[d*pow(t,j2,P)%P for t,d in zip(x,beta)]
                        M.append([wt[3],wt[4],dot(wt[5:],[r,f.kap(v),1]),dot(wt[:3],[1,f.kap(u),g])])
                    coeff=lin(list(map(list,zip(*M))),[0,0,0,1],5)
                else:
                    coeff=[0]*5
                dual.extend(coeff)
            stats['family_reject']+=1
            receipt=f'decodeFamily {free} '+compact(sum(rows,[]))+' '+compact(dual)
        key=f'⟨{z}, {u}, {v}, {str(bool(ap)).lower()}, {str(bool(bp)).lower()}⟩'
        by_z.setdefault(z,[]).append(f'  ({key}, {receipt})')
header='''module
public import RKCert.Research.SDIRKSevenEightStageF19Arithmetic

@[expose] public section
namespace RKResearch.Certified.SDIRKSeven.F19
def decodeQuad (p : Array Nat) : Recipe :=
  .rejectQuad (fun j => (p[j.val]! : K))
def decodeFamily (free : Fin 8) (p d : Array Nat) : Recipe :=
  .certifyFamily free (fun i j => (p[7*i.val+j.val]! : K))
    (fun i j => (d[5*i.val+j.val]! : K))

/-- The complete table of scalar cuts and dual certificates. Each witness
is verified in the kernel; the generator is not a trusted decision step. -/
def receipts (z : Fin 19) : List (Key × Recipe) :=
  match z.val with
'''
lines=[header]
for z in sorted(by_z):
    lines.append('  | '+str(z)+' => [\n'+',\n'.join(by_z[z])+']\n')
lines+=['  | _ => []\n','\nend RKResearch.Certified.SDIRKSeven.F19\n']
path=Path(__file__).resolve().parents[2] / 'lean/RKCert/Research/SDIRKSevenEightStageF19Receipts.lean'
path.write_text(''.join(lines))
assert stats==Counter(quad_reject=72,family_reject=78,seed_reject=1014)
print(stats, path.stat().st_size)
