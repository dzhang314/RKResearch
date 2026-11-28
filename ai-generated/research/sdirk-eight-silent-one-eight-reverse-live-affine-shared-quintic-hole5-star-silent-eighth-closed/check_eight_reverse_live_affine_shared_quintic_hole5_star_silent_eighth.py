"""Regular ordinary hole5, actual star front and the genuinely silent eighth."""
from pathlib import Path
import sys

root=Path(__file__).resolve().parent.parent
sys.path.append(str(root/'sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-arithmetic-middle-closed'))
import check_eight_reverse_live_affine_shared_quintic_hole5_star_arithmetic_middle
from h58_star_projection import res23_terms
from h58_star_modular import test
from sympy import expand,isprime,resultant,symbols

def main():
    w,a,b,c,e,f,g,h=symbols('w a b c e f g h')
    assert expand(sum(res23_terms((a,b,c),(e,f,g,h)))
        - resultant(a+b*w+c*w**2,e+f*w+g*w**2+h*w**3,w))==0
    p,t=1129,203
    assert isprime(p) and 2*t*t%p==1
    out=[test(cubic,p,t) for cubic in (False,True)]
    assert out==[[(5,[]),(1,[])],[(24,[])]],out
    print('regular ordinary hole5 star-front actual silent eighth excluded',flush=True)

if __name__=='__main__':
    main()
