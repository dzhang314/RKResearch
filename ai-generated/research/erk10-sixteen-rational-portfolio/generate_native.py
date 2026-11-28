#!/usr/bin/env python3
"""Regenerate the independent kernel-certificate sources for the named charts."""

from argparse import ArgumentParser
from pathlib import Path
import re
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
MIRROR = HERE.parent / "erk10-sixteen-rational-mirror"
NATIVE = HERE.parent.parent / "lean" / "RKCert" / "ReviewedNative"
ORIGINAL = "ERK10RationalSixteen"
CHARTS = {
    "compact": ("ERK10MirrorCompact", "theta-five-fourths.json",
                (1691, 27783000, -50329, 357210000)),
    "theta-four": ("ERK10MirrorThetaFour", "theta-four.json",
                   (-46337, 103680, 723883, 48384000)),
    "unit13": ("ERK10MirrorUnit13", "denominator-unit-at-13.json",
               (58014567931723802324069, 895164549957335337177540096,
                -577229118592014411047078673162971, 19595092960614736461392401950374400)),
}


def replace_abbrevs(text, replacements):
    for name, value in replacements.items():
        text, count = re.subn(rf"(abbrev {name} : ℤ := )-?\d+",
                              lambda match: match[1] + str(value), text)
        assert count == 1
    return text


def generate(chart, emit):
    prefix, data, (n1, d1, n2, d2) = CHARTS[chart]
    emit.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        generator = scratch / "generate.py"
        generator.write_text((MIRROR / "generate_lean.py").read_text().replace(ORIGINAL, prefix))
        subprocess.run([sys.executable, "-B", str(generator), "--source", str(HERE / data),
                        "--emit", str(emit.resolve()), "--modules", str(scratch / "modules.txt")],
                       check=True)
    for suffix in ("Core", "JoinPoint", "Next", ""):
        scaffold = (NATIVE / f"{ORIGINAL}{suffix}.lean").read_text().replace(ORIGINAL, prefix)
        if suffix == "Core":
            scaffold = scaffold.replace("Exact integer verification of the universal seventeen-stage method.",
                                        "Exact integer verification of the sixteen-stage rational tableau.")
        if suffix == "Next":
            scaffold = replace_abbrevs(scaffold, {"d₁": d1, "n₁": n1, "d₂": d2, "n₂": n2})
        if not suffix:
            e1 = pow(n1, -1, abs(n2))
            e2 = (1 - e1 * n1) // n2
            assert e1 * n1 + e2 * n2 == 1
            scaffold = replace_abbrevs(scaffold, {"e₁": e1, "e₂": e2})
        (emit / f"{prefix}{suffix}.lean").write_text(scaffold)


if __name__ == "__main__":
    cli = ArgumentParser()
    cli.add_argument("chart", choices=CHARTS)
    cli.add_argument("emit", type=Path)
    args = cli.parse_args()
    generate(args.chart, args.emit)
