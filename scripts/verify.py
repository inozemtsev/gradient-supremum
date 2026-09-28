#!/usr/bin/env python3
"""Build the proof, check its transitive axioms, and record source hashes."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LAKE = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
ENV = dict(os.environ, LEAN_NUM_THREADS="2")
EXPECTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
THEOREMS = ["GradientSupremum.supremum_gradient_step",
            "Mathoverflow347178.bounded_only", "Mathoverflow347178.bounded_only_strong"]


def run(args, timeout):
    start = time.monotonic()
    result = subprocess.run([LAKE, *args], cwd=ROOT, env=ENV,
                            capture_output=True, text=True, timeout=timeout)
    text = result.stdout + result.stderr
    return {"command": ["lake", *args], "exit_code": result.returncode,
            "seconds": round(time.monotonic() - start, 3), "output": text}

def main():
    checks = []
    try:
        checks.append(run(["--wfail", "build"], 300))
        checks.append(run(["env", "lean", "-j2", "scripts/AxiomAudit.lean"], 120))
        checks.append(run(["env", "lean", "-j2", "scripts/StatementTests.lean"], 120))
    except (OSError, subprocess.TimeoutExpired) as exc:
        (ROOT / "VALIDATION.json").write_text(json.dumps(
            {"passed": False, "error": str(exc), "checks": checks}, indent=2) + "\n")
        print(exc, file=sys.stderr)
        return 1
    audit = checks[1]["output"]
    axioms = {}
    for name in THEOREMS:
        match = re.search(re.escape("'" + name + "' depends on axioms:") +
                          r"\s*\[([^\]]*)\]", audit)
        axioms[name] = sorted(x.strip() for x in match.group(1).split(",")) if match else []
    sources = [ROOT / "GradientSupremum.lean"]
    for directory in ["GradientSupremum", "scripts"]:
        sources.extend(sorted((ROOT / directory).glob("*.lean")))
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sources}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = {}
    for package in manifest["packages"]:
        name = package["name"].removeprefix("«").removesuffix("»")
        directory = ROOT / manifest["packagesDir"] / name
        revision = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        clean = subprocess.run(
            ["git", "-C", str(directory), "diff", "--quiet", "HEAD", "--"],
            check=False).returncode == 0
        dependencies[name] = {"revision": revision, "expected_revision": package["rev"],
                              "tracked_files_unchanged": clean}
    actual = dependencies["mathlib"]["revision"]
    passed = (all(c["exit_code"] == 0 and "warning:" not in c["output"] for c in checks)
              and all(set(axioms[name]) == EXPECTED_AXIOMS for name in THEOREMS)
              and all(d["revision"] == d["expected_revision"] and d["tracked_files_unchanged"]
                      for d in dependencies.values()))
    receipt = {"passed": passed, "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
               "mathlib_revision": actual, "axioms": axioms, "source_sha256": hashes,
               "checks": checks, "dependencies": dependencies}
    (ROOT / "VALIDATION.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"passed": passed, "mathlib_revision": actual, "axioms": axioms}, indent=2))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
