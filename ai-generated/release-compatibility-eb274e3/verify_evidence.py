#!/usr/bin/env python3
"""Recheck the recorded matrix offline. This does not run Lean or validate its kernel."""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

RELEASES = {"v4.34.1", "v4.35.0", "v4.36.0", "v4.37.0-rc1"}
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FOCUS_COUNT = 30
AUDIT_LINE = re.compile(
    r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]+)\])"
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_manifest(path):
    result = {}
    for line in path.read_text().splitlines():
        sha, name = line.split("  ", 1)
        require(re.fullmatch("[0-9a-f]{64}", sha) and name not in result, f"invalid {path.name}")
        result[name] = sha
    return result


def read_json(path):
    return json.loads(path.read_text())


def clean_log(path):
    data = path.read_text()
    require(not re.search(r"(?im)^(?:⚠|[^\n]*(?:warning|error):)", data), f"warning/error in {path}")
    return data


def check(root):
    checksums = read_manifest(root / "SHA256SUMS")
    files = {p.relative_to(root).as_posix(): p for p in root.rglob("*") if p.is_file()}
    files.pop("SHA256SUMS")
    require(set(files) == set(checksums), "bundle contains missing or unexpected files")
    for name, path in files.items():
        require(not path.is_symlink() and digest(path) == checksums[name], f"SHA-256 mismatch: {name}")

    matrix = read_json(root / "results.json")
    versions = read_json(root / "versions.json")
    rows = matrix["pairs"]
    require(set(rows) == set(versions) == RELEASES, "version set differs from public matrix")
    for filename, field in [("published.sources.sha256", "publishedSourceManifestSHA256"),
                            ("candidate.sources.sha256", "candidateSourceManifestSHA256"),
                            ("portability.patch", "patchSHA256"), ("incremental-portability.patch", "incrementalPatchSHA256"), ("repository-root.patch", "repositoryRootPatchSHA256")]:
        require(digest(root / filename) == matrix[field], f"{field} differs")
    old = read_manifest(root / "published.sources.sha256")
    new = read_manifest(root / "candidate.sources.sha256")
    require(set(new) == set(old), "proof patch changes file set")
    blob_info = read_json(root / "published-git-blobs.json")
    require(blob_info["commit"] == matrix["publishedSourceCommit"], "Git tree commit mismatch")
    tree = {}
    for line in (root / "published-git-tree.tsv").read_text().splitlines():
        raw, name = line.split("\t", 1)
        if name.endswith(".lean"):
            mode, kind, blob = raw.split()
            require(mode == "100644" and kind == "blob" and name not in tree, "bad Git proof record")
            tree[name] = blob
    require(tree == blob_info["blobs"] and set(tree) == {"ai-generated/lean/" + n for n in old}, "published Git tree and source manifest disagree")
    modules = sum(n.startswith("RKCert/") and n.endswith(".lean") for n in new)
    expected = read_json(root / "audited-declarations.json")
    all_names = [name for group in expected.values() for name in group]
    focus = set(read_json(root / "focused-modules.json"))
    require(len(focus) == FOCUS_COUNT and modules == 280 and len(expected) == 22 and len(all_names) == 428 and len(set(all_names)) == 422, "coverage differs from the published snapshot")

    all_tree = {name: meta.split()[2] for meta, name in (line.split("\t", 1) for line in (root / "published-git-tree.tsv").read_text().splitlines())}
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        body = (root / "locks" / "v4.36.0" / name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(body)).encode() + bytes([0]) + body).hexdigest()
        require(blob == all_tree["ai-generated/lean/" + name], "4.36 reference configuration was not the published byte stream: " + name)

    observed_by_tag = {}
    for tag, (lean_commit, mathlib_commit, _, _) in versions.items():
        observed_by_tag[tag] = {}
        row = rows[tag]
        prefix = root / "locks" / tag
        evidence = root / "verified" / tag
        require(row["status"] == "pass" and row["exactSourceSHA256"] == matrix["candidateSourceManifestSHA256"],
                f"{tag}: not a pass on the common source")
        require(row["leanCommit"] == lean_commit and row["mathlibCommit"] == mathlib_commit,
                f"{tag}: commit mismatch")
        require((prefix / "lean-toolchain").read_text().strip() == "leanprover/lean4:" + tag and
                digest(prefix / "lake-manifest.json") == row["lockSHA256"], f"{tag}: pin/lock mismatch")
        packages = read_json(prefix / "lake-manifest.json")["packages"]
        mathlib = [p for p in packages if p["name"] == "mathlib"]
        require(len(mathlib) == 1 and mathlib[0]["inputRev"] == tag and mathlib[0]["rev"] == mathlib_commit,
                f"{tag}: Mathlib pin mismatch")

        def dep_triples(entries):
            return {(p["name"], p["url"], p["rev"]) for p in entries}

        inherited = read_json(prefix / "upstream-mathlib-manifest.json")["packages"]
        require(dep_triples(inherited) == dep_triples(p for p in packages if p["name"] != "mathlib"),
                f"{tag}: transitive locks disagree with recorded upstream manifest")
        toolfiles = list(evidence.glob("toolchain.*"))
        require(len(toolfiles) == 1, f"{tag}: expected exactly one toolchain log")
        tool = clean_log(toolfiles[0])
        require(f"version {tag[1:]}," in tool and f"commit {lean_commit}," in tool,
                f"{tag}: measured Lean commit differs")
        build = clean_log(evidence / "build.log").rstrip().splitlines()
        expected_builds = {n[:-5].replace("/", ".") for n in new if n.startswith("RKCert/") or n == "RKCert.lean"}
        emitted_builds = set(re.findall(r"\bBuilt (RKCert(?:\.[A-Za-z0-9_]+)*)\s+\(", "\n".join(build)))
        require(emitted_builds == expected_builds, f"{tag}: clean build log omits or adds project targets")
        require(build and build[-1] == f"Build completed successfully ({row['lakeJobs']} jobs).",
                f"{tag}: successful Lake job count differs")
        require(row["modules"] == modules and row["auditQueries"] == len(all_names) and
                row["distinctAuditedDeclarations"] == len(set(all_names)), f"{tag}: coverage count differs")
        for audit, names in expected.items():
            output = clean_log(evidence / f"{audit}.log")
            records = AUDIT_LINE.findall(output)
            require([name for name, _ in records] == names, f"{tag}/{audit}: missing/unexpected query result")
            for name, raw in records:
                used = set(t.strip() for t in raw.split(",") if t.strip())
                require(used <= AXIOMS, f"{tag}/{audit}/{name}: unexpected reported axiom")
                ordered = sorted(used)
                require(name not in observed_by_tag[tag] or observed_by_tag[tag][name] == ordered, "duplicate audit disagreement")
                observed_by_tag[tag][name] = ordered
        captures = {p.stem[len("replay-"):]: p for p in evidence.glob("replay-*.log")}
        require(set(captures) == focus == set(row["focusedDefaultKernelReplays"]),
                f"{tag}: replay endpoint set differs")
        for name, path in captures.items():
            require(("replaying " + name) in clean_log(path).splitlines(), f"{tag}: missing replay line: {name}")
        print(f"{tag}: {row['lakeJobs']} jobs; {modules} modules; {len(all_names)} queries; {len(focus)} replays")
    differences = {name: {tag: observed_by_tag[tag][name] for tag in versions} for name in sorted(set(all_names)) if len({tuple(observed_by_tag[tag][name]) for tag in versions}) > 1}
    require(read_json(root / "audit-reporting-differences.json")["declarations"] == differences and matrix["differentReportedStandardAxiomSets"] == len(differences), "inter-release axiom diagnostic summary differs from raw logs")
    print(f"Exact common source manifest: {matrix['candidateSourceManifestSHA256']}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        check(args.directory.resolve())
    except (ValueError, KeyError, OSError, IndexError) as problem:
        sys.exit(f"Evidence verification failed: {problem}")
