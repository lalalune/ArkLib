#!/usr/bin/env python3
"""Classify ArkLib duplication findings into *valid dedup moves*.

Consumes the JSON emitted by `dedup_audit.py --json` and cross-references each
finding against a module import graph (built by scanning `import ArkLib.*`
lines) so every duplicate can be labelled with a concrete, safety-checked action:

  SAFE-DELETE   file with zero importers whose decls are all duplicated elsewhere
  DE-COLLIDE    same FQN, different signatures -> namespace/rename one side
  MERGE-LIVE    duplicate decl across >1 live file -> pick canonical, repoint
  UNIFY-PROOF   identical proof body across files -> extract shared lemma
  IN-FILE       identical proof body within ONE file -> local combinator
  ARTIFACT      self-described intentional witness/audit file -> keep
  NO-ACTION     coincidental (e.g. shared `Basic.lean` name, trivial proof)

Read-only. Usage:
    python3 scripts/dedup_audit.py --json /tmp/dedup.json
    python3 scripts/dedup_classify.py /tmp/dedup.json --md > issue_body.md
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path("ArkLib")
IMPORT_RE = re.compile(r"^\s*import\s+(ArkLib\.[\w.]+)")


def module_of(rel_path: str) -> str:
    """`ArkLib/Foo/Bar.lean` -> `ArkLib.Foo.Bar`."""
    p = rel_path[:-5] if rel_path.endswith(".lean") else rel_path
    return p.replace("/", ".")


def build_import_graph() -> dict[str, set[str]]:
    """module -> set of modules that import it (reverse import edges)."""
    importers: dict[str, set[str]] = defaultdict(set)
    for path in ROOT.rglob("*.lean"):
        if any(part in (".lake", "blueprint", "home_page") for part in path.parts):
            continue
        mod = module_of(str(path))
        try:
            for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
                m = IMPORT_RE.match(line)
                if m:
                    importers[m.group(1)].add(mod)
        except OSError:
            continue
    return importers


def file_of(loc: str) -> str:
    """`ArkLib/Foo/Bar.lean:42` -> `ArkLib/Foo/Bar.lean`."""
    return loc.rsplit(":", 1)[0]


ARTIFACT_HINTS = (
    "compatibility re-export", "kernel-clean", "witness", "scratch",
    "disposition", "audit", "intentionally not asserted",
)


def is_artifact(rel_path: str) -> bool:
    p = ROOT.parent / rel_path
    try:
        head = p.read_text(encoding="utf-8", errors="replace")[:1500].lower()
    except OSError:
        return False
    return any(h in head for h in ARTIFACT_HINTS)


def importer_count(rel_path: str, importers: dict[str, set[str]]) -> int:
    """Real importers, excluding the generated umbrella `ArkLib`."""
    mod = module_of(rel_path)
    return len({m for m in importers.get(mod, set()) if m != "ArkLib"})


def classify(data: dict) -> dict:
    importers = build_import_graph()

    def ic(rel: str) -> int:
        return importer_count(rel, importers)

    out: dict[str, list] = {
        "dup_names": [], "same_stmt_identical": [], "same_stmt_diff": [],
        "identical_proof_cross": [], "identical_proof_infile": [],
        "dead_dup_files": [], "real_dup_basenames": [],
    }

    # --- duplicate FQN names ---
    for fqn, locs in data.get("dup_names_exact", {}).items():
        files = {file_of(l) for l in locs}
        if len(files) == 1:
            action = "DE-COLLIDE (same-file clash; file will not compile)"
        else:
            counts = {f: ic(f) for f in files}
            live = [f for f, n in counts.items() if n > 0]
            if len(live) <= 1:
                action = "SAFE-DELETE / DE-COLLIDE (only %d live)" % len(live)
            else:
                action = "MERGE-LIVE (multiple live definers)"
        out["dup_names"].append({
            "fqn": fqn, "locs": locs,
            "importers": {f: ic(f) for f in files}, "action": action,
        })

    # --- same statement type ---
    for key, info in data.get("same_statement", {}).items():
        stem = key.split("|", 1)[0]
        locs = info["locs"]
        files = sorted({file_of(l) for l in locs})
        rec = {
            "stem": stem, "locs": locs,
            "importers": {f: ic(f) for f in files},
            "artifact": any(is_artifact(f) for f in files),
        }
        if info["identical_proofs"]:
            out["same_stmt_identical"].append(rec)
        else:
            out["same_stmt_diff"].append(rec)

    # --- identical proof bodies ---
    for grp in data.get("identical_proof_bodies", []):
        files = sorted({file_of(d["loc"]) for d in grp["decls"]})
        rec = {
            "count": grp["count"], "body": grp["body"][:120],
            "decls": grp["decls"],
            "importers": {f: ic(f) for f in files},
        }
        if len(files) == 1:
            out["identical_proof_infile"].append(rec)
        else:
            out["identical_proof_cross"].append(rec)

    # --- dead duplicate files: every decl's stem duplicated elsewhere AND 0 importers
    # Approximate via same_statement membership: files where all same-stmt entries
    # are cross-file and the file has 0 importers.
    file_dupshare: dict[str, int] = defaultdict(int)
    for key, info in data.get("same_statement", {}).items():
        for l in info["locs"]:
            file_dupshare[file_of(l)] += 1
    for rel, n in sorted(file_dupshare.items(), key=lambda kv: -kv[1]):
        cnt = ic(rel)
        if cnt == 0 and not is_artifact(rel):
            out["dead_dup_files"].append({
                "file": rel, "dup_decls": n, "importers": 0,
                "artifact": False,
            })

    # --- real duplicate basenames: same basename AND share >=1 decl stem ---
    # (we only have basenames; flag the small/suspicious ones, skip Basic/General)
    GENERIC = {"Basic.lean", "General.lean", "Lemmas.lean", "Defs.lean",
               "Prelude.lean", "Spec.lean", "Completeness.lean", "Soundness.lean",
               "SingleRound.lean", "Mem.lean", "Ops.lean", "Domain.lean"}
    for base, paths in data.get("dup_file_basenames", {}).items():
        if base in GENERIC:
            continue
        out["real_dup_basenames"].append({"base": base, "paths": paths})

    return out


def md_report(c: dict) -> str:
    L = []
    def h(s): L.append(s)

    h("## Automated classification\n")
    h("Generated by `scripts/dedup_classify.py` over `dedup_audit.py` output. ")
    h("Importer counts exclude the generated `ArkLib.lean` umbrella.\n")

    h("### A. Duplicate fully-qualified names (hard build hazards)\n")
    if not c["dup_names"]:
        h("_None remaining._\n")
    for d in c["dup_names"]:
        h(f"- **`{d['fqn']}`** — {d['action']}")
        for loc in d["locs"]:
            h(f"  - `{loc}` (importers: {d['importers'].get(file_of(loc), '?')})")
    h("")

    h("### B. Same statement type, IDENTICAL proof (drop-in duplicates)\n")
    rows = [r for r in c["same_stmt_identical"]]
    h(f"_{len(rows)} groups._ Keep one, delete the rest (or re-export).\n")
    for r in rows:
        tag = " ⚠️artifact" if r["artifact"] else ""
        h(f"- `{r['stem']}`{tag}: " + ", ".join(
            f"`{l}`(imp {r['importers'].get(file_of(l),'?')})" for l in r["locs"]))
    h("")

    h("### C. Same statement type, DIFFERING proof (keep the better proof)\n")
    rows = c["same_stmt_diff"]
    h(f"_{len(rows)} groups._ Compare proofs; unify on the simpler/stronger one.\n")
    for r in rows[:60]:
        tag = " ⚠️artifact" if r["artifact"] else ""
        h(f"- `{r['stem']}`{tag}: " + ", ".join(
            f"`{l}`(imp {r['importers'].get(file_of(l),'?')})" for l in r["locs"]))
    if len(rows) > 60:
        h(f"- …and {len(rows)-60} more (see JSON)")
    h("")

    h("### D. Identical proof body across files (extract shared lemma)\n")
    rows = sorted(c["identical_proof_cross"], key=lambda r: -r["count"])
    h(f"_{len(rows)} groups._\n")
    for r in rows[:40]:
        h(f"- ({r['count']}×) `{r['body']}`")
        for d in r["decls"]:
            h(f"  - `{d['loc']}` `{d['name']}`")
    if len(rows) > 40:
        h(f"- …and {len(rows)-40} more")
    h("")

    h("### E. Identical proof body within ONE file (local combinator / `<;>`)\n")
    rows = sorted(c["identical_proof_infile"], key=lambda r: -r["count"])
    h(f"_{len(rows)} groups._\n")
    for r in rows[:25]:
        files = {file_of(d['loc']) for d in r['decls']}
        h(f"- ({r['count']}×) in `{list(files)[0]}`: `{r['body']}`")
    if len(rows) > 25:
        h(f"- …and {len(rows)-25} more")
    h("")

    h("### F. Candidate dead duplicate files (0 importers, decls duplicated elsewhere)\n")
    rows = c["dead_dup_files"]
    h(f"_{len(rows)} files._ Verify then delete + drop the `ArkLib.lean` import.\n")
    for r in rows:
        h(f"- `{r['file']}` — {r['dup_decls']} of its decls duplicated elsewhere, 0 importers")
    h("")

    h("### G. Non-generic duplicate file basenames (possible split/merge)\n")
    for r in c["real_dup_basenames"][:30]:
        h(f"- **{r['base']}** ×{len(r['paths'])}: " + ", ".join(f"`{p}`" for p in r["paths"]))
    h("")
    return "\n".join(L)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("json", help="dedup_audit.py --json output")
    ap.add_argument("--md", action="store_true", help="emit markdown")
    args = ap.parse_args()
    data = json.loads(Path(args.json).read_text())
    c = classify(data)
    if args.md:
        print(md_report(c))
    else:
        print(json.dumps(c, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
