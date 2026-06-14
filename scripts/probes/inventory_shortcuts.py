#!/usr/bin/env python3
"""Inventory real (non-comment) sorries, axioms, admits, and placebo patterns in ArkLib."""
import os, re, sys, json

ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "ArkLib")

def strip_comments(text):
    out = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    while i < n:
        c = text[i]
        if depth == 0 and not in_str and c == '"':
            in_str = True; out.append(c); i += 1; continue
        if in_str:
            if c == '\\' and i + 1 < n:
                out.append(text[i:i+2]); i += 2; continue
            if c == '"':
                in_str = False
            out.append(c); i += 1; continue
        if c == '/' and i + 1 < n and text[i+1] == '-':
            depth += 1; i += 2; continue
        if depth > 0:
            if c == '-' and i + 1 < n and text[i+1] == '/':
                depth -= 1; i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '-' and i + 1 < n and text[i+1] == '-':
            j = text.find('\n', i)
            if j == -1: j = n
            i = j; continue
        out.append(c); i += 1
    return ''.join(out)

results = {"sorry": [], "admit": [], "axiom": [], "native_decide": [],
           "true_placebo": [], "holds_def": []}

for dirpath, dirnames, filenames in os.walk(ROOT):
    for fn in filenames:
        if not fn.endswith(".lean"): continue
        path = os.path.join(dirpath, fn)
        rel = os.path.relpath(path, os.path.join(ROOT, "..")).replace("\\", "/")
        try:
            text = open(path, encoding="utf-8").read()
        except Exception as e:
            print(f"READ FAIL {rel}: {e}", file=sys.stderr); continue
        stripped = strip_comments(text)
        for ln, line in enumerate(stripped.split('\n'), 1):
            if re.search(r'\bsorry\b', line):
                results["sorry"].append(f"{rel}:{ln}: {line.strip()[:120]}")
            if re.search(r'\badmit\b', line):
                results["admit"].append(f"{rel}:{ln}: {line.strip()[:120]}")
            if re.search(r'^\s*(noncomputable\s+)?(unsafe\s+)?axiom\b', line):
                results["axiom"].append(f"{rel}:{ln}: {line.strip()[:160]}")
            if re.search(r'\bnative_decide\b', line):
                results["native_decide"].append(f"{rel}:{ln}: {line.strip()[:120]}")
            # def/theorem whose statement is just True (placebo)
            if re.search(r'(def|theorem|lemma|abbrev)\s+\S+.*:\s*True\s*(:=|$)', line):
                results["true_placebo"].append(f"{rel}:{ln}: {line.strip()[:160]}")
            if re.search(r'(axiom|def|abbrev)\s+\w*_holds\b', line):
                results["holds_def"].append(f"{rel}:{ln}: {line.strip()[:160]}")

for key in results:
    print(f"\n=== {key.upper()} ({len(results[key])}) ===")
    for item in results[key]:
        print(item)
