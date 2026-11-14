#!/usr/bin/env python3
"""Offline source build, in import order, followed by both axiom audits."""
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parent.parent
sources = {
    ".".join(path.relative_to(root).with_suffix("").parts): path
    for path in (root / "IsogenyAttack").rglob("*.lean")
    if path.name not in ("Audit.lean", "AuditAll.lean")
}
sources["IsogenyAttack"] = root / "IsogenyAttack.lean"
visiting, checked = set(), set()
resume = "--resume" in sys.argv


def check(module):
    if module in checked:
        return
    if module in visiting:
        raise RuntimeError("Import cycle at " + module)
    visiting.add(module)
    source = sources[module]
    dependencies = re.findall(r"^import\s+(\S+)", source.read_text(), re.M)
    for dependency in dependencies:
        if dependency in sources:
            check(dependency)
    target = root / ".lake/build/lib/lean" / Path(*module.split("."))
    target = target.with_suffix(".olean")
    target.parent.mkdir(parents=True, exist_ok=True)
    newest_input = max(source.stat().st_mtime, (root / "lean-toolchain").stat().st_mtime)
    for dependency in dependencies:
        if dependency in sources:
            obj = root / ".lake/build/lib/lean" / Path(*dependency.split("."))
            newest_input = max(newest_input, obj.with_suffix(".olean").stat().st_mtime)
    if resume and target.exists() and target.stat().st_mtime >= newest_input:
        print("Already checked " + module, flush=True)
    else:
        print("Checking " + module, flush=True)
        subprocess.run(
            [str(root / "scripts/lean-local.sh"), "-o", str(target), str(source)],
            cwd=root, check=True,
        )
    visiting.remove(module)
    checked.add(module)


for module in sorted(sources):
    check(module)
for audit in ("Audit.lean", "AuditAll.lean"):
    subprocess.run(
        [str(root / "scripts/lean-local.sh"), str(root / "IsogenyAttack" / audit)],
        cwd=root, check=True,
    )
print("All %d source modules and both audits passed." % len(checked))
