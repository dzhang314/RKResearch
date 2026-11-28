"""Independent exact rational guard support proposals for the actual fourth."""
from literal4_projection import projections
from literal4_model import model
from rear5_diagonal import result
from check_star_arithmetic67 import s_coeffs
from silent8_diag import primitive
from regular_star_projection import red,con,t
from flint import fmpz_poly
from functools import lru_cache
from pathlib import Path

def rational(Q):
    if Q==con(Q):return Q
    assert Q==-con(Q)
    Q=red(2*t*Q);assert Q==con(Q)
    return Q

def facts(Y):
    Z=fmpz_poly([1]);F=[]
    for P,k in Y.factor_squarefree()[1]:
        for R,e in P.factor()[1]:
            assert e==1
            R=R if R[R.degree()]>0 else -R
            Z*=R**k
            F.append((R,k))
    assert Z==Y or Z==-Y
    return F

@lru_cache(None)
def guards_for_cover():
    A,B=projections();gg=model()[5]
    D,E=(fmpz_poly(list(s_coeffs(P)[-1])) for P in (A,B))
    G=D.gcd(E);G=G//G.content()
    out=[('leading',P,e) for P,e in facts(G)]
    for name,i in [('anchor',3),('x_eq_silent',6),('quintic',9),('terminal_h',10)]:
        f,h=primitive(rational(gg[i]))
        Y,shape=result(A,f,name)
        assert shape=={
           'anchor':(585,1456,585,72,25),
           'x_eq_silent':(129,306,129,26,6),
           'quintic':(390,1039,390,57,18),
           'terminal_h':(651,1667,651,138,28),
        }[name]
        out.extend((name,P,e) for P,e in facts(Y))
    print('whole independent literal-fourth guard source proposals',
          [(name,P.degree(),e) for name,P,e in out],flush=True)
    return out

def main():
    Path('literal4-aux-factors.txt').write_text('\n'.join(
       name+' '+str(e)+' '+' '.join(map(str,P)) for name,P,e in guards_for_cover()))

if __name__=='__main__':main()
