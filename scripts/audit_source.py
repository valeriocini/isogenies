#!/usr/bin/env python3
"""Scan project and imported TauCeti sources; the kernel audit remains authoritative."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent.parent
tau = root / ".lake/packages/TauCeti"


def code_only(text):
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed comment")
    return "".join(result)


imports = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)", re.M)
forbidden = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b")


def inspect(path):
    data = path.read_bytes()
    code = code_only(data.decode())
    matches = [m.group() for m in forbidden.finditer(code)]
    if matches:
        raise ValueError(str(path) + ": " + str(matches))
    dependencies = [name for line in imports.findall(code) for name in line.split()
                    if name.startswith("TauCeti.")]
    return {"sha256": hashlib.sha256(data).hexdigest(), "lines": data.count(b"\n")}, dependencies


project, external, pending = {}, {}, []
for path in sorted((root / "IsogenyAttack").rglob("*.lean")) + [root / "IsogenyAttack.lean"]:
    record, dependencies = inspect(path)
    project[str(path.relative_to(root))] = record
    pending.extend(dependencies)
while pending:
    module = pending.pop()
    if module in external:
        continue
    path = tau.joinpath(*module.split(".")).with_suffix(".lean")
    record, dependencies = inspect(path)
    external[module] = record
    pending.extend(dependencies)
out = root / "audit"
out.mkdir(exist_ok=True)
for name, files in [("project-source-audit", project), ("tau-source-audit", external)]:
    result = {"file_count": len(files), "findings": [], "files": dict(sorted(files.items()))}
    (out / (name + ".json")).write_text(json.dumps(result, indent=2) + "\n")
(out / "tauceti-source-modules.txt").write_text("\n".join(sorted(external)) + "\n")
print(f"Source audit passed: {len(project)} project files and {len(external)} TauCeti modules.")
