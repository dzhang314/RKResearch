"""Exact complete literal-second chart, with bounded-memory phases."""
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import sys,os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
for dep in (
    "sdirk-eight-half-quadratic",
    "sdirk-eight-half-star-quadratic",
    "sdirk-eight-silent-one-eight-reverse-live-constant",
    "sdirk-eight-silent-one-eight-reverse-live-exceptional",
    "sdirk-eight-silent-one-eight-reverse-live-regular-finite",
    "sdirk-eight-silent-one-eight-reverse-live-regular-silent-eighth-finite",
    "sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-regular-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-silent-eighth-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-arithmetic67-closed",
    "sdirk-eight-silent-one-eight-reverse-live-star-arithmetic5-closed",
    "sdirk-eight-silent-one-seven-distinct-anchors",
    "sdirk-eight-silent-one-seven-distinct-coprime",
    "sdirk-eight-silent-one-seven-six-anchored",
    "sdirk-eight-silent-one-seven-six-reverse",
    "sdirk-eight-silent-one-seven-six-shared",
    "sdirk-eight-silent-three-closure",
    "sdirk-eight-silent-two-equal",
    "sdirk-eight-silent-two-high",
    "sdirk-eight-silent-two-unequal",
):
    sys.path.append(str(ROOT/dep))
sys.set_int_max_str_digits(0)

def phase(arg):
    if arg=='oriented':
        from arith2_outer import exact
        exact()
    elif arg=='aux':
        from arith2_aux import main
        main()
    elif arg=='cover':
        from arith2_cover_probe import main
        main()
    elif arg=='norm_quotient':
        from arith2_norm_cover import main
        main()
    elif arg=='guard':
        from arith2_guarded_fibers import main
        main()
    elif arg=='generic':
        from arith2_generic import main
        main()
    else:raise ValueError(arg)

def main():
    if len(sys.argv)>1:
        assert sys.argv[1]=='--phase' and len(sys.argv)==3
        phase(sys.argv[2])
        return
    directory=Path(os.environ.get('RK_ARITHMETIC_SCRATCH','.')).resolve()
    with TemporaryDirectory(prefix='rk-arith2-',dir=directory) as temp:
        for arg in ('oriented','aux','cover','norm_quotient','guard','generic'):
            run([sys.executable,str(Path(__file__).resolve()),'--phase',arg],cwd=temp,check=True)
    print('strict SDIRK8 actual silent second regular arithmetic/ordinary-arithmetic excluded',flush=True)

if __name__=='__main__':main()
