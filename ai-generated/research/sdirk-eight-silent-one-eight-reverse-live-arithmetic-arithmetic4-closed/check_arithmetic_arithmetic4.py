"""Exact complete literal-fourth chart using compact profile coordinates."""
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
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-arithmetic2-closed",
    "sdirk-eight-silent-one-eight-reverse-live-arithmetic-arithmetic3-closed",
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
        from arith4_outer import exact
        exact()
    elif arg=='rankdrop':
        from arith4_guard_support import rankdrop_main
        rankdrop_main()
    elif arg=='cover_and_fibres':
        from arith4_guard_support import main
        main()
    else:
        raise ValueError(arg)

def main():
    if len(sys.argv)>1:
        assert sys.argv[1]=='--phase' and len(sys.argv)==3
        phase(sys.argv[2])
        return
    directory=Path(os.environ.get('RK_ARITHMETIC_SCRATCH','.')).resolve()
    with TemporaryDirectory(prefix='rk-arith4-',dir=directory) as temp:
        for arg in ('oriented','cover_and_fibres'):
            run([sys.executable,str(Path(__file__).resolve()),'--phase',arg],cwd=temp,check=True)
    print('strict SDIRK8 actual silent fourth regular arithmetic/ordinary-arithmetic excluded',flush=True)

if __name__=='__main__':main()
