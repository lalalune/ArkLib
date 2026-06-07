#!/usr/bin/env python3
"""mine_premises.py — mine REAL (theorem statement -> used internal premise) pairs from
ArkLib's Lean source, as the training corpus for the energy premise-selector.

Premise selection is THE selector organ of a proof agent: given a goal, which lemmas are
relevant. We mine it lexically from source (no Lean execution): for every declared
theorem/lemma, the statement is its type signature, and its "used premises" are the
identifiers in its proof body that are themselves ArkLib-declared lemma names (internal
premise graph). One pair per (statement, used-premise), emitted as {"a","b"} for the
contrastive ranker (a = goal statement, b = a premise it uses).

Identifiers are split into subwords (on `.`/`_`/camelCase, lowercased) so a word-level
tokenizer sees real tokens: `Polynomial.natDegree_mul` -> "polynomial nat degree mul".

Out: bench/agent/arklib_premises.jsonl  ({"a","b","source":"arklib","premise_raw"})
Run: python3 bench/agent/mine_premises.py
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "ArkLib"
OUT = Path(__file__).resolve().parent / "arklib_premises.jsonl"

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)",
    re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
_CAMEL = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")

# tactic/keyword identifiers that are not premises
STOP = {
    "by", "fun", "do", "let", "have", "show", "from", "with", "at", "in", "then",
    "else", "if", "match", "calc", "intro", "intros", "exact", "apply", "refine",
    "simp", "rw", "rfl", "ring", "omega", "linarith", "constructor", "cases",
    "rcases", "obtain", "rintro", "induction", "exact?", "sorry", "admit", "this",
    "Type", "Prop", "Sort", "fun", "True", "False",
}


def subwords(name: str) -> str:
    """`Polynomial.natDegree_mul` -> 'polynomial nat degree mul' (subword split)."""
    parts = re.split(r"[._]", name)
    out = []
    for p in parts:
        out.extend(w for w in _CAMEL.sub(" ", p).split() if w)
    return " ".join(out).lower()


def looks_like_premise(name: str) -> bool:
    """A real lemma/def reference, not a bound variable: qualified (has `.`), or
    snake_case, or a long CamelCase name — never a 1-3 char local like `t`/`R`/`hyp`."""
    if len(name) < 4:
        return False
    if "." in name or "_" in name:
        return True
    return len(name) >= 6 and not name.islower()  # long Camel/mixed, not a short local


def split_decls(text: str):
    """Yield (kind, name, header_to_assign, body) for each top-level decl."""
    ms = list(DECL.finditer(text))
    for i, m in enumerate(ms):
        start = m.end()
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        block = text[start:end]
        # statement = up to the first `:=` (the type); body = after it
        cut = block.find(":=")
        header = block[:cut] if cut >= 0 else block
        body = block[cut + 2:] if cut >= 0 else ""
        yield m.group(1), m.group(2), header, body


def main() -> int:
    files = [p for p in SRC.rglob("*.lean") if ".lake" not in p.parts]
    decls = []  # (kind, name, header, body, file)
    names = set()
    for f in files:
        try:
            txt = f.read_text()
        except Exception:
            continue
        for kind, name, header, body in split_decls(txt):
            if kind in ("theorem", "lemma", "def") and looks_like_premise(name):
                names.add(name)            # only real, premise-shaped declared names
            decls.append((kind, name, header, body))
    print(f"scanned {len(files)} files, {len(decls)} decls, {len(names)} names", flush=True)

    pairs = []
    seen = set()
    for kind, name, header, body in decls:
        if kind not in ("theorem", "lemma"):
            continue
        stmt = subwords(name) + " : " + " ".join(subwords(t) for t in IDENT.findall(header))
        stmt = re.sub(r"\s+", " ", stmt).strip()
        if len(stmt) < 5:
            continue
        used = set()
        for ident in IDENT.findall(body):
            if ident in STOP or ident == name:
                continue
            if ident in names and looks_like_premise(ident):
                used.add(ident)
        for prem in used:
            key = (name, prem)
            if key in seen:
                continue
            seen.add(key)
            pairs.append({"a": stmt[:600], "b": subwords(prem), "source": "arklib",
                          "premise_raw": prem, "thm": name})
    # keep premises that occur at least twice (a real, rankable target) — drops hapax noise
    from collections import Counter
    bc = Counter(p["b"] for p in pairs)
    pairs = [p for p in pairs if bc[p["b"]] >= 2 and p["b"]]
    OUT.write_text("".join(json.dumps(p) + "\n" for p in pairs))
    uniq_thm = len({p["thm"] for p in pairs})
    uniq_prem = len({p["b"] for p in pairs})
    print(f"wrote {len(pairs)} (statement -> premise) pairs "
          f"({uniq_thm} theorems, {uniq_prem} distinct premises) -> {OUT}", flush=True)
    if pairs:
        print("example:", json.dumps(pairs[0])[:200], flush=True)
    return 0 if len(pairs) >= 200 else 1


if __name__ == "__main__":
    sys.exit(main())
