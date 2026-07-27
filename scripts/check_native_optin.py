#!/usr/bin/env python3
"""Check that native-executing checks are opt-in.

Elaborating a module that (transitively) imports a `precompileModules` lane module
loads the lane's locally compiled dylib, and the interpreter then dispatches calls
into it for any evaluation run during that module's elaboration. Loading is
unavoidable for the lane's own proof modules, so the enforced invariant is one
level up: no module whose import closure reaches a lane module may contain an
evaluation-based check (`#eval`, `#guard`, `native_decide`) unless it is on the
explicit opt-in list below. A check that executes locally compiled native code
trusts the C emitter, the local C toolchain, and the loader, coarse-grained and
with no axiom trace — so it must be a documented decision, never ambient.

Scope: textual, non-adversarial (comments and strings are stripped heuristically;
crafted code could evade this). The local lane is parsed from lakefile.toml; the
pin lane is an explicit mirror (see PIN_LANE). Run from the repository root;
exits non-zero on violation.
"""
import re, sys
from pathlib import Path

def parse_local_lane():
    """The local lane, parsed from lakefile.toml (the single source of truth):
    every lean_lib with precompileModules = true contributes its globs. A glob
    ending in ".+" is a prefix entry. Parse failures are violations, not skips.
    (A hand-rolled block parse rather than tomllib, which needs python 3.11+.)"""
    text = Path("lakefile.toml").read_text()
    lane = []
    for block in re.split(r"(?m)^\[\[lean_lib\]\]", text)[1:]:
        block = re.split(r"(?m)^\[", block)[0]  # stop at the next table header
        if not re.search(r"(?m)^precompileModules\s*=\s*true", block):
            continue
        globs_m = re.search(r"(?m)^globs\s*=\s*\[(.*?)\]", block, re.S)
        globs = re.findall(r'"([^"]+)"', globs_m.group(1)) if globs_m else []
        if not globs:
            name_m = re.search(r'(?m)^name\s*=\s*"([^"]+)"', block)
            print(f"ERROR: cannot determine the globs of precompileModules "
                  f"library {name_m.group(1) if name_m else '?'}; extend "
                  f"parse_local_lane", file=sys.stderr)
            sys.exit(2)
        for g in globs:
            lane.append(("prefix", g[:-2]) if g.endswith(".+") else ("one", g))
    if not lane:
        print("ERROR: no precompileModules library found in lakefile.toml; "
              "if the lane was removed, retire this script", file=sys.stderr)
        sys.exit(2)
    return lane

# The CompElliptic pin's lane modules: importing them loads the pin's dylib.
# Not derivable from this repository's lakefile — mirror of the pin's
# precompileModules globs; re-check whenever the CompElliptic pin is bumped
# (the pin's scripts/check_native_optin.py --print-lane prints them).
PIN_LANE = [
    ("one", "FastFieldNative"),
    ("one", "CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs"),
    ("one", "CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs"),
]

LANE_ENTRIES = parse_local_lane() + PIN_LANE

def is_lane(mod: str) -> bool:
    return any(mod == name or (kind == "prefix" and mod.startswith(name + "."))
               for kind, name in LANE_ENTRIES)
# Modules allowed to contain evaluation-based checks despite reaching a lane
# module. Add a module here only with a comment saying which checks it runs and
# why native execution is intended.
OPT_IN = {
    # One bundled `native_decide` computational certificate checking the derived
    # verifying key field-by-field against the captured fixture over fixed
    # circuit data; native execution is the point of the check.
    "Zcash.Snark.Keygen.Certificate",
}

EVAL_TOKENS = re.compile(r"#eval\b|#guard\b|\bnative_decide\b|\bdecide\s*\+\s*native\b")

def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)

def strip_code(text: str) -> str:
    # Remove block comments (with nesting), line comments, and string literals.
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        two = text[i:i+2]
        if two == "/-":
            depth += 1; i += 2; continue
        if depth > 0:
            if two == "-/":
                depth -= 1; i += 2
            else:
                i += 1
            continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        out.append(text[i]); i += 1
    return "".join(out)

files = sorted(Path("Zcash").rglob("*.lean")) + [p for p in [Path("Zcash.lean")] if p.exists()]
imports = {}
for f in files:
    mods = re.findall(r"^import\s+([A-Za-z0-9_.]+)", f.read_text(), re.M)
    imports[module_name(f)] = set(mods)

# Modules whose import closure reaches the lane.
reaches = set()
changed = True
while changed:
    changed = False
    for m, deps in imports.items():
        if m not in reaches and any(is_lane(d) or d in reaches for d in deps):
            reaches.add(m); changed = True

status = 0
for f in files:
    m = module_name(f)
    if m not in reaches or is_lane(m) or m in OPT_IN:
        continue
    code = strip_code(f.read_text())
    hits = sorted(set(EVAL_TOKENS.findall(code)))
    if hits:
        print(f"VIOLATION: {f} reaches a precompiled lane module and contains "
              f"evaluation-based check(s) {hits}; native-executing checks must be "
              f"opt-in — add the module to OPT_IN in this script with a rationale, "
              f"or move the check out of the lane's import cone", file=sys.stderr)
        status = 1

in_cone = sorted(m for m in reaches if not is_lane(m) and m in imports)
print(f"native opt-in: {len(in_cone)} module(s) in the lane import cone, "
      f"{len(OPT_IN)} opted in, no ambient native-executing checks"
      if status == 0 else "native opt-in: violations found", file=sys.stdout)
sys.exit(status)
