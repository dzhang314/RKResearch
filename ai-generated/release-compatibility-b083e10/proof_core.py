"""Dependency-ordered, clean Lean typechecking without irrelevant native C products."""
import concurrent.futures as cf
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

KNOWN = {"propext", "Classical.choice", "Quot.sound"}
DIAGNOSTIC = re.compile(r"(?im)^(?:⚠|[^\n]*(?:warning|error)(?:\([^\n)]*\))?:)")
AUDIT = re.compile(r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]+)\])")
IMPORT = re.compile(r"(?m)^\s*(?:public\s+|meta\s+)*import(?: all)?[ \t]+([^\n/]+)")
IDENT = re.compile(r"(?:[A-Za-z_][A-Za-z0-9_']*)(?:\.(?:[A-Za-z_][A-Za-z0-9_']*))*")


def sh(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    temp = path.with_suffix(path.suffix + ".part")
    temp.write_text(json.dumps(value, indent=2) + "\n")
    temp.replace(path)


def imports(path):
    names = set()
    for packet in IMPORT.findall(path.read_text()):
        names.update(word for word in packet.split() if IDENT.fullmatch(word))
    return names


def run(log, args, work, env, timeout=4000):
    with log.open("w") as out:
        result = subprocess.run(args, cwd=work, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=timeout)
    return result.returncode, log.read_text()


def checked(log, args, work, env):
    status, text = run(log, args, work, env)
    if status or DIAGNOSTIC.search(text):
        raise RuntimeError(f"{log}: failed or emitted warnings/diagnostics (exit {status})")
    return text


def build(work, out, source_hashes, env, evidence, jobs=4, only=None, basis=None):
    """Compile every requested project module, with compiler-produced OLeans as the only interface."""
    pmap = {n[:-5].replace("/", "."): n for n in source_hashes if n.startswith("RKCert/") or n == "RKCert.lean"}
    actual = {m: imports(work / n) for m, n in pmap.items()}
    graph = {m: deps & set(pmap) for m, deps in actual.items()}
    unsupported = {dep for deps in actual.values() for dep in deps if dep.startswith("RKCert.") and dep not in pmap}
    if unsupported:
        raise RuntimeError(f"unavailable project imports: {sorted(unsupported)}")
    requested = set(only if only is not None else pmap)
    accepted = set(pmap) - requested
    basis_info = {}
    if accepted:
        if basis is None or only is None:
            raise RuntimeError("partial targets require exact same-release baseline artifacts")
        for m in accepted - {"RKCert"}:
            path = basis / (m.replace(".", "/") + ".olean")
            if not path.is_file():
                raise RuntimeError(f"missing saved baseline module {m}")
            basis_info[m] = sh(path.read_bytes())
        if any("RKCert" in graph[m] for m in requested):
            raise RuntimeError("a smoke target must not import the aggregate")
    logs = evidence / "module-logs"
    logs.mkdir(exist_ok=True)
    out.mkdir(parents=True, exist_ok=True)
    # Lean resolves a module-prefix directory in the first search root containing it.
    # In the smoke lane, place read-only same-release baseline and new modules in the
    # same prefix directory; names are disjoint and the baseline remains hash-checked.
    if basis:
        for name in basis_info:
            rel = Path(name.replace(".", "/"))
            d = out / rel.parent
            d.mkdir(parents=True, exist_ok=True)
            for src in (basis / rel.parent).glob(rel.name + ".*"):
                if src.is_file():
                    dest = d / src.name
                    if not dest.exists():
                        os.link(src, dest)
                    else:
                        assert src.samefile(dest), name
    before = {p.relative_to(out).as_posix() for p in out.rglob("*.olean")}
    prior = {}
    attestation = evidence / "module-checkpoints.json"
    if attestation.exists():
        prior = json.loads(attestation.read_text())
    unrecorded = {n[:-6].replace("/", ".") for n in before} - set(prior) - set(basis_info)
    for name in sorted(unrecorded):
        if name not in requested:
            raise RuntimeError(f"foreign proof artifact in output: {name}")
        rel = Path(name.replace(".", "/"))
        # An interrupted or diagnostic compiler may have produced an OLean before
        # its result was accepted. Discard only that module's private outputs.
        for f in (out / rel.parent).glob(rel.name + ".*"):
            if not f.is_file() or f.is_symlink() or not f.resolve().is_relative_to(out.resolve()):
                raise RuntimeError(f"unexpected artifact path: {f}")
            f.unlink()
    for n in prior:
        if n not in requested or prior[n]["sourceSHA256"] != source_hashes[pmap[n]]:
            raise RuntimeError(f"previous compilation for a different source: {n}")
        path = out / (n.replace(".", "/") + ".olean")
        if not path.is_file() or sh(path.read_bytes()) != prior[n]["oleanSHA256"]:
            raise RuntimeError(f"compiled checkpoint bytes changed: {n}")
    if any(not (graph[n] <= (set(prior) | accepted)) for n in prior):
        raise RuntimeError("compiled checkpoint imported a missing project module")
    accepted.update(prior)
    records = dict(prior)
    pending = requested - set(prior)
    failed = {}
    running = {}
    e = dict(env)
    e["LEAN_PATH"] = os.pathsep.join([str(out), env.get("LEAN_PATH", "")])
    compile_env = dict(e)
    compile_env["LEAN_NUM_THREADS"] = "1"

    def compile_module(m):
        rel = pmap[m]
        file = out / (m.replace(".", "/") + ".olean")
        file.parent.mkdir(parents=True, exist_ok=True)
        start = time.monotonic()
        status, text = run(logs / f"{m}.log", ["lean", "-j", "1", "-o", str(file), rel], work, compile_env)
        if status or DIAGNOSTIC.search(text) or not file.is_file():
            errors = [line.strip() for line in text.splitlines() if re.search(r"(?:warning|error)(?:\([^\n)]*\))?:", line)]
            return None, {"exit": status, "firstDiagnostics": errors[:8]}
        return {"sourceSHA256": source_hashes[rel], "oleanSHA256": sh(file.read_bytes()),
                "durationMS": round((time.monotonic() - start) * 1000)}, None

    with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            ready = sorted(n for n in pending if graph[n] <= accepted)
            for n in ready[:max(0, jobs - len(running))]:
                pending.remove(n)
                running[pool.submit(compile_module, n)] = n
            if not running:
                break
            done, _ = cf.wait(running, return_when=cf.FIRST_COMPLETED)
            for x in done:
                n = running.pop(x)
                record, failure = x.result()
                if failure:
                    failed[n] = failure
                    print("FAIL", n, failure, flush=True)
                else:
                    records[n] = record
                    accepted.add(n)
                    write_json(attestation, records)
                    print(f"BUILT {n} ({len(records)}/{len(requested)})", flush=True)
    if basis:
        for m, a in basis_info.items():
            assert sh((basis / (m.replace(".", "/") + ".olean")).read_bytes()) == a, m
    with (evidence / "build.log").open("w") as stream:
        for n in sorted(records):
            print(f"BUILT {n} {records[n]['sourceSHA256']} {records[n]['oleanSHA256']}", file=stream)
        print(f"Direct Lean typechecking: {len(records)}/{len(requested)} targets", file=stream)
    write_json(evidence / "module-result.json", {"completed": len(records), "requested": len(requested), "buildTargets": sorted(records),
                                              "failed": failed, "blocked": sorted(pending)})
    if failed or pending:
        raise RuntimeError(f"{len(failed)} failed and {len(pending)} blocked; see {evidence / 'module-result.json'}")
    return e


def audit(work, evidence, env, expected, jobs=2):
    def check(item):
        name, table = item
        rel = name + ".lean"
        text = checked(evidence / (name + ".log"), ["lean", rel], work, env)
        found = AUDIT.findall(text)
        if [name for name, _ in found] != table or len(re.findall(r"(?m)^#print axioms ", (work / rel).read_text())) != len(found):
            print(name, "expected-versus-observed", list(zip(table, [n for n, _ in found])), flush=True)
            raise ValueError(f"audit coverage differs: {name}")
        result = []
        for n, raw in found:
            used = sorted({a.strip() for a in raw.split(",") if a.strip()})
            if not set(used) <= KNOWN:
                raise ValueError(f"{name}, {n}: unexpected reported axioms {used}")
            result.append({"declaration": n, "reported_axioms": used})
        return name, result

    with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
        results = dict(pool.map(check, expected.items()))
    write_json(evidence / "audit-queries.json", results)
    return results


def replay(work, evidence, env, focus, jobs=2):
    def check(n):
        observed = checked(evidence / f"replay-{n}.log", ["leanchecker", "--verbose", n], work, env).splitlines()
        if ("replaying " + n) not in observed:
            raise ValueError(f"missing kernel replay {n}")

    with cf.ThreadPoolExecutor(max_workers=jobs) as pool:
        list(pool.map(check, focus))
