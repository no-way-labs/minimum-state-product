#!/usr/bin/env python3
"""
ra8_import_graph.py — Transitive import graph for LeanMn/LowerBound/*.lean

Identifies which files are "clean" (no transitive import of forbidden files)
and which are "dirty" (transitively import a forbidden file).

Forbidden files:
  - PhaseExtraction.lean
  - CaseObstructions.lean
  - CaseObstructionsCore.lean
  - AllNormalFormFalse.lean
  - AllNormalFormFalse2.lean
"""

import os
import re
from collections import defaultdict

BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                    "..", "lean")

FORBIDDEN = {
    "LeanMn.LowerBound.EntryConflict.PhaseExtraction",
    "LeanMn.LowerBound.CaseObstructions",
    "LeanMn.LowerBound.CaseObstructionsCore",
    "LeanMn.LowerBound.EntryConflict.AllNormalFormFalse",
    "LeanMn.LowerBound.EntryConflict.AllNormalFormFalse2",
}

def module_to_path(mod):
    return os.path.join(BASE, mod.replace(".", "/") + ".lean")

def path_to_module(path):
    rel = os.path.relpath(path, BASE)
    return rel.replace("/", ".").replace(".lean", "")

def find_lean_files():
    files = []
    for root, _, fnames in os.walk(os.path.join(BASE, "LeanMn", "LowerBound")):
        for f in fnames:
            if f.endswith(".lean"):
                files.append(os.path.join(root, f))
    return sorted(files)

def parse_imports(path):
    imports = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            m = re.match(r'^import\s+([\w.]+)', line)
            if m:
                imports.append(m.group(1))
    return imports

def build_graph():
    files = find_lean_files()
    # direct imports: module -> [module]
    graph = {}
    for path in files:
        mod = path_to_module(path)
        graph[mod] = parse_imports(path)
    return graph

def transitive_closure(graph):
    """For each module, compute all transitively imported modules."""
    cache = {}

    def dfs(mod, visiting=None):
        if mod in cache:
            return cache[mod]
        if visiting is None:
            visiting = set()
        if mod in visiting:
            return set()  # cycle
        visiting.add(mod)
        result = set()
        for dep in graph.get(mod, []):
            result.add(dep)
            result |= dfs(dep, visiting)
        visiting.discard(mod)
        cache[mod] = result
        return result

    for mod in graph:
        dfs(mod)
    return cache

def main():
    graph = build_graph()
    tc = transitive_closure(graph)

    print("=" * 80)
    print("TRANSITIVE IMPORT ANALYSIS")
    print("=" * 80)

    # Classify each module
    clean = []
    dirty = []
    for mod in sorted(graph.keys()):
        forbidden_deps = tc[mod] & FORBIDDEN
        if forbidden_deps:
            dirty.append((mod, forbidden_deps))
        else:
            # Also check if the module itself is forbidden
            if mod in FORBIDDEN:
                dirty.append((mod, {mod}))
            else:
                clean.append(mod)

    print("\n--- CLEAN files (no forbidden transitive imports) ---")
    for mod in clean:
        print(f"  {mod}")

    print(f"\n--- DIRTY files ({len(dirty)}) ---")
    for mod, deps in dirty:
        short_deps = [d.split(".")[-1] for d in deps]
        print(f"  {mod}")
        print(f"    -> forbidden: {', '.join(sorted(short_deps))}")

    print("\n" + "=" * 80)
    print("IMPORT CHAINS FOR KEY FILES")
    print("=" * 80)

    key_files = [
        "LeanMn.LowerBound.ZeroWindingAssembly",
        "LeanMn.LowerBound.EntryConflict.GlobalMinGap",
        "LeanMn.LowerBound.EntryConflict.ConsecutiveBinaryEC",
        "LeanMn.LowerBound.EntryConflict.NonConsecutive",
        "LeanMn.LowerBound.EntryConflict.Palindromic",
        "LeanMn.LowerBound.EntryConflict.WaterfallBridge",
        "LeanMn.LowerBound.EntryConflict.PhaseExtractionBase",
        "LeanMn.LowerBound.Shadow.Theorem",
        "LeanMn.LowerBound.EntryConflict.CleanProof",
        "LeanMn.LowerBound.EntryConflict.AllNormalFormFalse",
        "LeanMn.LowerBound.EntryConflict.AllNormalFormFalse2",
    ]

    for mod in key_files:
        if mod not in graph:
            print(f"\n{mod}: NOT FOUND")
            continue
        forbidden_deps = tc.get(mod, set()) & FORBIDDEN
        if mod in FORBIDDEN:
            forbidden_deps.add(mod)
        status = "DIRTY" if forbidden_deps else "CLEAN"
        print(f"\n{mod}: {status}")
        print(f"  Direct imports: {graph.get(mod, [])}")
        if forbidden_deps:
            short = [d.split(".")[-1] for d in forbidden_deps]
            print(f"  Forbidden transitive: {', '.join(sorted(short))}")
        # Show full transitive deps
        all_deps = tc.get(mod, set())
        lb_deps = sorted(d for d in all_deps if d.startswith("LeanMn.LowerBound"))
        if lb_deps:
            print(f"  All LB transitive imports ({len(lb_deps)}):")
            for d in lb_deps:
                tag = " [FORBIDDEN]" if d in FORBIDDEN else ""
                print(f"    {d}{tag}")

    # Check what ZeroWindingAssembly currently imports transitively
    zwa = "LeanMn.LowerBound.ZeroWindingAssembly"
    print("\n" + "=" * 80)
    print(f"ZeroWindingAssembly TRANSITIVE IMPORTS")
    print("=" * 80)
    zwa_deps = tc.get(zwa, set())
    for d in sorted(zwa_deps):
        if d.startswith("LeanMn.LowerBound"):
            tag = " [FORBIDDEN]" if d in FORBIDDEN else ""
            print(f"  {d}{tag}")

    # Check: what if ZWA also imported WaterfallBridge?
    print("\n" + "=" * 80)
    print("WHAT IF ZWA imported WaterfallBridge?")
    print("=" * 80)
    wb = "LeanMn.LowerBound.EntryConflict.WaterfallBridge"
    wb_deps = tc.get(wb, set())
    new_forbidden = wb_deps & FORBIDDEN
    if new_forbidden:
        print(f"  WaterfallBridge transitively imports FORBIDDEN: {[d.split('.')[-1] for d in new_forbidden]}")
    else:
        print(f"  WaterfallBridge is CLEAN - safe to import!")

    # Check: what if ZWA also imported PhaseExtractionBase?
    print("\n" + "=" * 80)
    print("WHAT IF ZWA imported PhaseExtractionBase?")
    print("=" * 80)
    peb = "LeanMn.LowerBound.EntryConflict.PhaseExtractionBase"
    peb_deps = tc.get(peb, set())
    new_forbidden = peb_deps & FORBIDDEN
    if new_forbidden:
        print(f"  PhaseExtractionBase transitively imports FORBIDDEN: {[d.split('.')[-1] for d in new_forbidden]}")
    else:
        print(f"  PhaseExtractionBase is CLEAN - safe to import!")

if __name__ == "__main__":
    main()
