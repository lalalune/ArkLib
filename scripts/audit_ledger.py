#!/usr/bin/env python3
"""Generate AUDIT_LEDGER.md: a complete inventory of proof debt in ArkLib.

Categories:
  S  - `sorry` / `admit` occurrences (with enclosing declaration)
  N  - `native_decide` occurrences (compiler-trusting shortcut)
  A  - `axiom` declarations
  R  - strict residual Prop definitions from `scripts/residual_census.py`
       (`def <Name>Residual ... : Prop := ...`), with open/discharged status
  C  - strict conjecture Prop definitions (`def <Name>Conjecture ... : Prop`)

Usage: python3 scripts/audit_ledger.py   (from repo root; writes AUDIT_LEDGER.md)
"""

import os
import re
import sys
from collections import defaultdict
from pathlib import Path

from residual_census import collect as collect_residual_census
from residual_census import find_providers, summarize

REPO_ROOT = Path(__file__).resolve().parent.parent
ROOT = REPO_ROOT / "ArkLib"
OUT = REPO_ROOT / "AUDIT_LEDGER.md"

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |scoped |local )*"
    r"(theorem|lemma|def|abbrev|instance|class|structure|axiom|opaque)\s+([^\s({\[:]+)"
)
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])(sorry|admit)(?![A-Za-z0-9_'])")
NATIVE_RE = re.compile(r"(?<![A-Za-z0-9_'])native_decide(?![A-Za-z0-9_'])")
AXIOM_RE = re.compile(r"^\s*(?:noncomputable\s+)?axiom\s+(\S+)")


def strip_comments(lines):
    """Yield (lineno, code) with line/block comments and docstrings blanked."""
    in_block = 0
    for i, raw in enumerate(lines, 1):
        line = raw
        out = []
        j = 0
        while j < len(line):
            if in_block:
                # Lean block comments NEST: count inner `/-` openers before the next `-/`.
                nxt_open = line.find("/-", j)
                nxt_close = line.find("-/", j)
                if nxt_close == -1 and nxt_open == -1:
                    j = len(line)
                elif nxt_open != -1 and (nxt_close == -1 or nxt_open < nxt_close):
                    in_block += 1
                    j = nxt_open + 2
                else:
                    in_block -= 1
                    j = nxt_close + 2
                continue
            if line.startswith("/-", j):
                in_block += 1
                j += 2
                continue
            if line.startswith("--", j):
                break
            out.append(line[j])
            j += 1
        yield i, "".join(out)


def subsystem(path):
    parts = Path(path).parts
    if len(parts) >= 3 and parts[1] in ("ProofSystem", "Data", "OracleReduction"):
        sub = parts[2] if not parts[2].endswith(".lean") else parts[1]
        return f"{parts[1]}/{sub}" if sub != parts[1] else parts[1]
    return parts[1].removesuffix(".lean") if len(parts) > 1 else parts[0]


def is_strict_conjecture_prop(decl):
    last = decl["name"].rsplit(".", 1)[-1]
    result_norm = " ".join(decl["result"].split())
    return (
        decl["kind"] == "def"
        and result_norm == "Prop"
        and ("Conjecture" in last or "CONJECTURE" in last)
    )


def provider_note(row):
    providers = row.get("providers", [])
    if row["status"] == "discharged":
        concrete = [
            p
            for p in providers
            if not p["conditional_on_residuals"] and not p["ambiguous_name_match"]
        ]
        first = concrete[0]["name"] if concrete else providers[0]["name"]
        return f" — **discharged** ({len(concrete)} concrete provider(s); first: `{first}`)"

    conds = sorted({c for p in providers for c in p["conditional_on_residuals"]})
    if conds:
        return f" — **open** (only conditional providers on: `{', '.join(conds)}`)"
    if providers:
        return " — **open** (provider matches are ambiguous)"
    return " — **open**"


def main():
    sorries, natives, axioms = [], [], []
    for dirpath, _dirs, files in os.walk(ROOT):
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = Path(dirpath) / fn
            rel_path = path.relative_to(REPO_ROOT).as_posix()
            with open(path, encoding="utf-8") as fh:
                raw_lines = fh.readlines()
            current_decl = "?"
            for lineno, code in strip_comments(raw_lines):
                mdecl = DECL_RE.match(code)
                if mdecl:
                    current_decl = mdecl.group(2)
                if SORRY_RE.search(code):
                    sorries.append((rel_path, lineno, current_decl))
                if NATIVE_RE.search(code):
                    natives.append((rel_path, lineno, current_decl))
                max_ = AXIOM_RE.match(code)
                if max_:
                    axioms.append((rel_path, lineno, max_.group(1)))

    all_decls, residuals, near_misses = collect_residual_census(REPO_ROOT)
    find_providers(all_decls, residuals)
    residuals.sort(key=lambda r: (r["file"], r["line"]))
    residual_summary = summarize(residuals)
    residual_sites = {(r["file"], r["line"]) for r in residuals}
    conjectures = [
        {
            "name": d["name"].rsplit(".", 1)[-1],
            "fq_name": d["fq_name"],
            "file": d["file"],
            "line": d["line"],
        }
        for d in all_decls
        if is_strict_conjecture_prop(d) and (d["file"], d["line"]) not in residual_sites
    ]
    conjectures.sort(key=lambda r: (r["file"], r["line"]))

    by_sub = defaultdict(lambda: defaultdict(list))
    for cat, items in (("S", sorries), ("N", natives), ("A", axioms)):
        for it in items:
            by_sub[subsystem(it[0])][cat].append(it)
    for row in residuals:
        by_sub[subsystem(row["file"])]["R"].append(row)
    for row in conjectures:
        by_sub[subsystem(row["file"])]["C"].append(row)

    with open(OUT, "w", encoding="utf-8") as out:
        out.write("# ArkLib proof-debt ledger (generated by scripts/audit_ledger.py)\n\n")
        out.write(
            "Goal: zero `sorry`/`admit`, zero `axiom`, zero `native_decide`, and every\n"
            "Residual/Conjecture Prop surface either **proven**, **deleted**, or honestly\n"
            "documented as open research with the paper trail.\n\n"
        )
        out.write(
            "The residual columns use the strict census from `scripts/residual_census.py`: only\n"
            "`def <Name>Residual ... : Prop` declarations are counted as residual Prop surfaces.\n"
            "Provider theorem names and residual-like helper declarations are not counted here;\n"
            f"the census JSON records {len(near_misses)} residual-like near misses separately.\n\n"
        )
        out.write(
            f"Strict residual census: **{residual_summary['total']}** total, "
            f"**{residual_summary['open']}** open, "
            f"**{residual_summary['discharged']}** discharged.\n\n"
        )
        out.write(
            "| subsystem | sorry/admit | native_decide | axioms | residual Prop defs | "
            "open residual Prop defs | conjecture Prop defs |\n"
        )
        out.write("|---|---|---|---|---|---|---|\n")
        tot = [0, 0, 0, 0, 0, 0]
        for sub in sorted(by_sub):
            c = by_sub[sub]
            open_residuals = sum(1 for r in c["R"] if r["status"] == "open")
            out.write(
                f"| {sub} | {len(c['S'])} | {len(c['N'])} | {len(c['A'])} | "
                f"{len(c['R'])} | {open_residuals} | {len(c['C'])} |\n"
            )
            tot[0] += len(c["S"])
            tot[1] += len(c["N"])
            tot[2] += len(c["A"])
            tot[3] += len(c["R"])
            tot[4] += open_residuals
            tot[5] += len(c["C"])
        out.write(
            f"| **TOTAL** | **{tot[0]}** | **{tot[1]}** | **{tot[2]}** | "
            f"**{tot[3]}** | **{tot[4]}** | **{tot[5]}** |\n\n"
        )

        for sub in sorted(by_sub):
            c = by_sub[sub]
            out.write(f"\n## {sub}\n\n")
            if c["A"]:
                out.write("### axioms\n")
                for path, ln, name in c["A"]:
                    out.write(f"- `{path}:{ln}` axiom **{name}**\n")
            if c["S"]:
                out.write("### sorry / admit\n")
                for path, ln, decl in c["S"]:
                    out.write(f"- `{path}:{ln}` in `{decl}`\n")
            if c["N"]:
                out.write("### native_decide\n")
                for path, ln, decl in c["N"]:
                    out.write(f"- `{path}:{ln}` in `{decl}`\n")
            if c["R"]:
                out.write("### residual Prop definitions\n")
                for row in c["R"]:
                    out.write(
                        f"- `{row['file']}:{row['line']}` def **{row['fq_name']}**"
                        f"{provider_note(row)}\n"
                    )
            if c["C"]:
                out.write("### conjecture Prop definitions\n")
                for row in c["C"]:
                    out.write(f"- `{row['file']}:{row['line']}` def **{row['fq_name']}**\n")

    print(
        f"wrote {OUT.relative_to(REPO_ROOT)}: sorry={len(sorries)} native={len(natives)} "
        f"axiom={len(axioms)} residual-prop={len(residuals)} "
        f"open-residual-prop={residual_summary['open']} conjecture-prop={len(conjectures)}"
    )


if __name__ == "__main__":
    main()
