#!/usr/bin/env python3
"""Split the library's modules into the three stages of the CI build.

    python3 scripts/ci_plan.py ROOT HEAVY_PATTERN [SLOW_FIRST...]

ROOT is the library's root module (e.g. `LeanPlayground`), HEAVY_PATTERN an
fnmatch pattern for the modules that are too big to build side by side (e.g.
`LeanPlayground.PerfectCuboid.Fibers.*`), and SLOW_FIRST optional heavy
modules to put at the front of the list so their jobs start first.

Prints JSON with
* `core`:  modules that import no heavy module, built together in one job;
* `heavy`: the heavy modules, each built in a job of its own;
* `tail`:  modules that import a heavy module (and ROOT), built last.

Imports are read from the `import` lines of the sources, so this needs no
Lean toolchain.
"""

import fnmatch
import json
import re
import sys
from pathlib import Path

IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def main() -> None:
    root, pattern, *slow_first = sys.argv[1:]
    files = [Path(f"{root}.lean"), *sorted(Path(root).rglob("*.lean"))]
    imports = {}
    for f in files:
        mod = ".".join(f.with_suffix("").parts)
        imports[mod] = [m for m in IMPORT.findall(f.read_text()) if m.split(".")[0] == root]

    heavy = sorted(m for m in imports if fnmatch.fnmatchcase(m, pattern))
    heavy.sort(key=lambda m: slow_first.index(m) if m in slow_first else len(slow_first))

    # Everything that reaches a heavy module through its imports.
    tail: set[str] = set()
    changed = True
    while changed:
        changed = False
        for m, deps in imports.items():
            if m not in tail and m not in heavy and any(d in tail or d in heavy for d in deps):
                tail.add(m)
                changed = True

    core = sorted(m for m in imports if m not in tail and m not in heavy)
    print(json.dumps({"core": core, "heavy": heavy, "tail": sorted(tail)}))


if __name__ == "__main__":
    main()
