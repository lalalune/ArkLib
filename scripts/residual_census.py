#!/usr/bin/env python3
"""Residual census for the ArkLib source tree.

ArkLib encodes open proof obligations as named Prop definitions:

  def <Name>Residual ... : Prop := ...

End-to-end theorems consume these as hypotheses; the mission metric is the
number of *open* residuals falling over time.  This script inventories every
`def` under ArkLib/ whose name ends in `Residual` and whose result type is
exactly `Prop` (multiline signatures handled), then conservatively classifies
each as:

  discharged — a concrete providing declaration exists: a theorem/def
               elsewhere whose *result type* head is that residual (this
               covers `: <Name>Residual ...` providers, including ones proved
               by anonymous constructor `⟨...⟩`), or a `<name>_holds*` /
               `<name>_proved*` theorem whose result mentions the residual.
               Providers whose own hypotheses consume a census residual are
               recorded but do NOT count as a discharge (a conditional
               reduction is not a proof).  When several census residuals
               share a last name across namespaces, a provider is narrowed
               via its qualified result head or namespace affinity; if it
               stays ambiguous it is recorded but does not discharge.
  refuted    — a concrete declaration proves a negated instance of the residual
               (for example `theorem ..._false : ¬ FooResidual ...`).  This is
               not a discharge; it means the statement surface is known false
               or too broad and should be repaired/retired rather than carried
               as open proof debt.
  open       — everything else.

A residual name appearing only in hypothesis position (`(h : <Name>Residual
...)`) is consumption, not provision, and never counts.

Residual-like defs that miss the strict pattern (name contains `Residual` /
`residual` but not as a `Residual` suffix, or suffix-matching defs whose
result type is not literally `Prop`) are reported as near-misses but kept out
of the census.

Usage:
  python3 scripts/residual_census.py                 # summary + JSON
  python3 scripts/residual_census.py --root <dir>    # explicit checkout root
  python3 scripts/residual_census.py --out <file>    # JSON destination

Writes scripts/residual_census.json by default.  Python 3 stdlib only.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def configure_stdio() -> None:
    """Prefer UTF-8 output for declaration names on Windows consoles."""
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            reconfigure(encoding="utf-8")


DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|instance|abbrev|opaque)\s+([^\s({\[:⦃]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
HEAD_IDENT_RE = re.compile(r"[^\s({\[⦃⟨:,]+")

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

PROVIDER_KINDS = {"theorem", "lemma", "def", "instance"}


def strip_comments(text: str) -> str:
    """Blank out line comments, block comments, and docstrings (newlines kept)."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out[i] = " "
            if i + 1 < n:
                out[i + 1] = " "
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out[i] = " "
            if i + 1 < n:
                out[i + 1] = " "
            i += 2
        else:
            if depth > 0 and text[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def split_signature(window: str) -> tuple[str, str]:
    """Split a declaration tail (after the name) into (binders, result type).

    The signature colon is the first `:` at bracket depth 0 that is not part
    of `:=`; the signature ends at the first depth-0 `:=`.  Bracket depth
    tracks (), [], {}, ⟨⟩, ⦃⦄ so binder-internal colons and named arguments
    `(k := k)` are skipped.
    """
    depth = 0
    sig_colon = None
    end = len(window)
    i = 0
    while i < len(window):
        c = window[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and c == ":":
            if i + 1 < len(window) and window[i + 1] == "=":
                end = i
                break
            if sig_colon is None:
                sig_colon = i
        i += 1
    if sig_colon is None:
        return window[:end], ""
    return window[:sig_colon], window[sig_colon + 1 : end]


def strip_forall_prefix(result: str) -> str:
    """Strip leading `∀ ...,` binders from a result type."""
    s = result.strip()
    for _ in range(8):
        if not s.startswith("∀"):
            break
        depth = 0
        for i, c in enumerate(s):
            if c in OPEN_BRACKETS:
                depth += 1
            elif c in CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif c == "," and depth == 0:
                s = s[i + 1 :].strip()
                break
        else:
            return ""
    return s


def result_head(result: str) -> str:
    """Head identifier of a result type, stripping leading `∀ ...,` binders."""
    s = strip_forall_prefix(result)
    m = HEAD_IDENT_RE.match(s)
    return m.group(0) if m else ""


def is_ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'"


def mentions_word(text: str, word: str) -> bool:
    """Whole-identifier occurrence of `word`; allows a qualifying dot before,
    rejects a dot after (that would be a namespace use, not the residual)."""
    start = 0
    while True:
        idx = text.find(word, start)
        if idx == -1:
            return False
        before = text[idx - 1] if idx > 0 else " "
        after = text[idx + len(word)] if idx + len(word) < len(text) else " "
        if not is_ident_char(before) and not is_ident_char(after) and after != ".":
            return True
        start = idx + 1


def lower_first(name: str) -> str:
    return name[:1].lower() + name[1:] if name else name


def parse_file(path: Path, root: Path) -> list[dict]:
    """All top-level-ish declarations in one file, with parsed signatures."""
    text = path.read_text(encoding="utf-8", errors="replace")
    code = strip_comments(text)
    lines = code.splitlines(keepends=True)

    line_starts: list[int] = []
    pos = 0
    for ln in lines:
        line_starts.append(pos)
        pos += len(ln)

    ns_stack: list[tuple[str, str | None]] = []  # (kind, name)
    headers: list[dict] = []
    for idx, raw in enumerate(lines):
        ln = raw.rstrip("\n")
        m = NAMESPACE_RE.match(ln)
        if m:
            ns_stack.append(("namespace", m.group(1)))
            continue
        if SECTION_RE.match(ln):
            ns_stack.append(("section", None))
            continue
        if END_RE.match(ln):
            if ns_stack:
                ns_stack.pop()
            continue
        m = DECL_RE.match(ln)
        if m:
            prefix = ".".join(n for k, n in ns_stack if k == "namespace" and n)
            headers.append(
                {
                    "kind": m.group(1),
                    "name": m.group(2),
                    "line": idx + 1,
                    "start": line_starts[idx],
                    "sig_from": line_starts[idx] + m.end(2),
                    "namespace": prefix,
                }
            )

    decls: list[dict] = []
    rel = str(path.relative_to(root))
    for i, h in enumerate(headers):
        window_end = headers[i + 1]["start"] if i + 1 < len(headers) else len(code)
        binders, result = split_signature(code[h["sig_from"] : window_end])
        name = h["name"]
        fq = f"{h['namespace']}.{name}" if h["namespace"] else name
        decls.append(
            {
                "kind": h["kind"],
                "name": name,
                "fq_name": fq,
                "file": rel,
                "line": h["line"],
                "binders": binders,
                "result": result,
            }
        )
    return decls


def collect(root: Path) -> tuple[list[dict], list[dict], list[dict]]:
    """Return (all decls, census residual rows, near-miss rows)."""
    all_decls: list[dict] = []
    for f in sorted((root / "ArkLib").rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        all_decls.extend(parse_file(f, root))

    residuals: list[dict] = []
    near_misses: list[dict] = []
    for d in all_decls:
        last = d["name"].rsplit(".", 1)[-1]
        if "Residual" not in last and "residual" not in last:
            continue
        result_norm = " ".join(d["result"].split())
        strict = d["kind"] == "def" and last.endswith("Residual") and result_norm == "Prop"
        if strict:
            residuals.append(
                {
                    "name": last,
                    "fq_name": d["fq_name"],
                    "file": d["file"],
                    "line": d["line"],
                }
            )
        elif d["kind"] in {"def", "abbrev"}:
            if not last.endswith("Residual"):
                reason = "name does not end in `Residual`"
            elif d["kind"] != "def":
                reason = f"declared as `{d['kind']}`, not `def`"
            else:
                reason = f"result type is `{result_norm or '<none>'}`, not `Prop`"
            near_misses.append(
                {
                    "name": last,
                    "fq_name": d["fq_name"],
                    "kind": d["kind"],
                    "file": d["file"],
                    "line": d["line"],
                    "reason": reason,
                }
            )
    return all_decls, residuals, near_misses


def _ns_of(fq: str) -> str:
    return fq.rsplit(".", 1)[0] if "." in fq else ""


def _ns_affinity(c_ns: str, p_ns: str) -> bool:
    """Loose namespace kinship between a candidate residual and a provider."""
    if not c_ns or not p_ns:
        return False
    return (
        p_ns == c_ns
        or p_ns.endswith("." + c_ns)
        or c_ns.endswith("." + p_ns)
        or p_ns.split(".")[-1] == c_ns.split(".")[-1]
    )


def _resolve(candidates: list[dict], head_full: str, provider_ns: str) -> tuple[list[dict], bool]:
    """Narrow same-named census rows via a qualified result head or namespace
    affinity.  Returns (rows, ambiguous): ambiguous providers never count as a
    discharge on their own."""
    def ambiguity(rows: list[dict]) -> bool:
        # Same fq name in several files is one logical declaration duplicated,
        # not an ambiguity.
        return len({c["fq_name"] for c in rows}) > 1

    if not ambiguity(candidates):
        return candidates, False
    if "." in head_full:
        qualified = [
            c
            for c in candidates
            if c["fq_name"] == head_full or c["fq_name"].endswith("." + head_full)
        ]
        if qualified:
            return qualified, ambiguity(qualified)
    affine = [c for c in candidates if _ns_affinity(_ns_of(c["fq_name"]), provider_ns)]
    if affine:
        return affine, ambiguity(affine)
    return candidates, True


def find_providers(all_decls: list[dict], residuals: list[dict]) -> None:
    """Attach providers/refutations + status to each census row, in place."""
    census_names = sorted({r["name"] for r in residuals})
    by_name: dict[str, list[dict]] = {}
    for r in residuals:
        r["providers"] = []
        r["refutations"] = []
        by_name.setdefault(r["name"], []).append(r)

    def_sites = {(r["file"], r["line"]) for r in residuals}

    for d in all_decls:
        if d["kind"] not in PROVIDER_KINDS:
            continue
        if (d["file"], d["line"]) in def_sites:
            continue  # the residual definition itself is never its provider
        last = d["name"].rsplit(".", 1)[-1]
        head_full = result_head(d["result"])
        head_last = head_full.rsplit(".", 1)[-1]
        result_no_forall = strip_forall_prefix(d["result"])

        targets: set[str] = set()
        if head_last in by_name:
            targets.add(head_last)
        for rname in census_names:
            for stem in (rname, lower_first(rname)):
                if re.match(re.escape(stem) + r"_(holds|proved)(_|$)", last):
                    # name-based hit must still mention the residual in its
                    # result type, else it is about something adjacent.
                    if mentions_word(d["result"], rname):
                        targets.add(rname)
        consumed = [n for n in census_names if mentions_word(d["binders"], n)]
        provider_ns = _ns_of(d["fq_name"])
        for rname in targets:
            head_for_resolution = head_full if head_last == rname else ""
            rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
            for row in rows:
                row["providers"].append(
                    {
                        "name": d["fq_name"],
                        "kind": d["kind"],
                        "file": d["file"],
                        "line": d["line"],
                        "conditional_on_residuals": consumed,
                        "ambiguous_name_match": ambiguous,
                    }
                )

        refuted_targets: set[str] = set()
        if result_no_forall.startswith("¬"):
            negated = result_no_forall[1:].strip()
            neg_head_full = result_head(negated)
            neg_head_last = neg_head_full.rsplit(".", 1)[-1]
            if neg_head_last in by_name:
                refuted_targets.add(neg_head_last)
            for rname in census_names:
                if mentions_word(negated, rname):
                    refuted_targets.add(rname)
            for rname in refuted_targets:
                head_for_resolution = neg_head_full if neg_head_last == rname else ""
                rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
                for row in rows:
                    row["refutations"].append(
                        {
                            "name": d["fq_name"],
                            "kind": d["kind"],
                            "file": d["file"],
                            "line": d["line"],
                            "conditional_on_residuals": consumed,
                            "ambiguous_name_match": ambiguous,
                        }
                    )

    def dedupe_entries(entries: list[dict]) -> list[dict]:
        seen: set[tuple] = set()
        out: list[dict] = []
        for p in sorted(entries, key=lambda p: (p["file"], p["line"], p["name"])):
            key = (
                p["name"],
                p["file"],
                p["line"],
                tuple(p["conditional_on_residuals"]),
                p["ambiguous_name_match"],
            )
            if key in seen:
                continue
            seen.add(key)
            out.append(p)
        return out

    for r in residuals:
        r["providers"] = dedupe_entries(r["providers"])
        r["refutations"] = dedupe_entries(r["refutations"])
        concrete = [
            p
            for p in r["providers"]
            if not p["conditional_on_residuals"] and not p["ambiguous_name_match"]
        ]
        concrete_refutations = [
            p
            for p in r["refutations"]
            if not p["conditional_on_residuals"] and not p["ambiguous_name_match"]
        ]
        if concrete:
            r["status"] = "discharged"
        elif concrete_refutations:
            r["status"] = "refuted"
        else:
            r["status"] = "open"


def top_dir(file: str) -> str:
    parts = Path(file).parts  # ('ArkLib', <top>, ..., '<name>.lean')
    return parts[1] if len(parts) > 2 else "(root)"


def summarize(residuals: list[dict]) -> dict:
    by_dir: dict[str, dict[str, int]] = {}
    for r in residuals:
        d = by_dir.setdefault(
            top_dir(r["file"]),
            {"total": 0, "open": 0, "discharged": 0, "refuted": 0},
        )
        d["total"] += 1
        d[r["status"]] += 1
    return {
        "total": len(residuals),
        "open": sum(1 for r in residuals if r["status"] == "open"),
        "discharged": sum(1 for r in residuals if r["status"] == "discharged"),
        "refuted": sum(1 for r in residuals if r["status"] == "refuted"),
        "by_top_dir": dict(sorted(by_dir.items())),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="ArkLib checkout root (default: parent of scripts/)",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=None,
        help="JSON output path (default: scripts/residual_census.json)",
    )
    args = ap.parse_args()

    root = args.root.expanduser().resolve()
    out_path = args.out or root / "scripts" / "residual_census.json"

    all_decls, residuals, near_misses = collect(root)
    find_providers(all_decls, residuals)
    residuals.sort(key=lambda r: (r["file"], r["line"]))
    near_misses.sort(key=lambda r: (r["file"], r["line"]))
    summary = summarize(residuals)

    payload_residuals = []
    for r in residuals:
        row = dict(r)
        if not row.get("refutations"):
            row.pop("refutations", None)
        payload_residuals.append(row)
    payload = {"summary": summary, "residuals": payload_residuals, "near_misses": near_misses}
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )

    print(
        f"residual census: total {summary['total']} | "
        f"open {summary['open']} | discharged {summary['discharged']} | "
        f"refuted {summary['refuted']}"
    )
    print("\nby top-level directory (total / open / discharged / refuted):")
    for name, c in summary["by_top_dir"].items():
        print(
            f"  {name:<16} {c['total']:>3} / {c['open']:>3} / "
            f"{c['discharged']:>3} / {c['refuted']:>3}"
        )

    open_rows = [r for r in residuals if r["status"] == "open"]
    if open_rows:
        print(f"\n{len(open_rows)} open residual(s):")
        for r in open_rows:
            conds = sorted(
                {c for p in r["providers"] for c in p["conditional_on_residuals"]}
            )
            extra = f"  [only conditional providers, on: {', '.join(conds)}]" if conds else ""
            print(f"  {r['fq_name']}  ({r['file']}:{r['line']}){extra}")
    refuted_rows = [r for r in residuals if r["status"] == "refuted"]
    if refuted_rows:
        print(f"\n{len(refuted_rows)} refuted residual(s):")
        for r in refuted_rows:
            refs = [
                p for p in r["refutations"]
                if not p["conditional_on_residuals"] and not p["ambiguous_name_match"]
            ]
            ref_labels = [f"{p['name']} ({p['file']}:{p['line']})" for p in refs]
            extra = f"  [refuted by: {', '.join(ref_labels)}]" if refs else ""
            print(f"  {r['fq_name']}  ({r['file']}:{r['line']}){extra}")
    if near_misses:
        print(
            f"\nnote: {len(near_misses)} residual-like def(s) outside the strict pattern "
            "(see near_misses in JSON)"
        )
    print(f"\nwrote {out_path}")
    return 0


if __name__ == "__main__":
    configure_stdio()
    sys.exit(main())
