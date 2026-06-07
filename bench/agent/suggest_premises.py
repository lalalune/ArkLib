#!/usr/bin/env python3
"""suggest_premises.py — the premise selector as a proof aid.

Turns rank_train_eval's *metric* into a *tool*: given a goal (theorem statement),
rank every premise in ArkLib's mined library by the trained energy model and return
the most likely-relevant lemmas (argmin energy). This is the "select" organ of a
proof agent — it proposes candidates; the Lean kernel still decides.

Needs the trained model bench/agent/arklib_premise_ebm.pt (build it: rank_gate.sh).

Usage:
  python3 bench/agent/suggest_premises.py "<goal statement words>"   # top-k lemmas
  python3 bench/agent/suggest_premises.py --witness                  # held-out recall@10
"""
from __future__ import annotations

import json
import random
import sys
from pathlib import Path

import torch

from ebm_core import MiniTransformer, encode_pair, pad, MAX_LEN

HERE = Path(__file__).resolve().parent
CKPT = HERE / "arklib_premise_ebm.pt"
DATA = HERE / "arklib_premises.jsonl"
DEVICE = torch.device("mps" if torch.backends.mps.is_available() else "cpu")


def load_model():
    d = torch.load(CKPT, map_location=DEVICE, weights_only=False)
    vocab = d["vocab"]
    model = MiniTransformer(len(vocab), max_len=MAX_LEN).to(DEVICE)
    # strict=False: checkpoints from the original dual-head model carry an unused
    # lm_head; the energy path (tok/pos emb, encoder, ln_f, energy_head) loads fully.
    model.load_state_dict(d["state"], strict=False)
    model.eval()
    return model, vocab


def load_pool():
    """Distinct premises (subworded key -> display lemma name)."""
    pairs = [json.loads(l) for l in DATA.read_text().splitlines() if l.strip()]
    raw = {}
    for p in pairs:
        raw.setdefault(p["b"], p.get("premise_raw", p["b"]))
    keys = sorted(raw)
    return pairs, keys, [raw[k] for k in keys]


@torch.no_grad()
def rank(model, vocab, statement, keys, bs=512):
    """Energy of (statement, premise) for every premise; return indices low->high."""
    es = []
    for i in range(0, len(keys), bs):
        ids = [encode_pair(statement, k, vocab, MAX_LEN) for k in keys[i:i + bs]]
        mt = max(len(x) for x in ids)
        t = torch.tensor(pad(ids, mt), dtype=torch.long, device=DEVICE)
        es.append(model.energy(t))
    return torch.cat(es).argsort().tolist()


def main():
    if not CKPT.exists():
        sys.exit("no trained model — run: bash bench/agent/rank_gate.sh")
    pairs, keys, names = load_pool()
    model, vocab = load_model()

    if len(sys.argv) > 1 and sys.argv[1] == "--witness":
        # replicate rank_train_eval's split (seed 7), sample held-out pairs,
        # measure recall@10 over the FULL premise pool (the tool's real task).
        rng = random.Random(7); rng.shuffle(pairs)
        n_eval = max(60, int(len(pairs) * 0.15))
        sample = random.Random(0).sample(pairs[:n_eval], min(40, n_eval))
        Ks = [10, 50, 100]
        hits = {k: 0 for k in Ks}
        for p in sample:
            order = rank(model, vocab, p["a"], keys)
            ranked = [keys[i] for i in order]
            for k in Ks:
                hits[k] += int(p["b"] in ranked[:k])
        rec = {k: hits[k] / len(sample) for k in Ks}
        # Honest claim for a shortlist ranker: the true premise lands in a short
        # ranked list FAR above chance over the WHOLE library. floor@k = k/|pool|.
        floor10 = 10 / len(keys)
        print(f"suggest over full pool ({len(keys)} premises, n={len(sample)}):")
        for k in Ks:
            print(f"  recall@{k:<3} = {rec[k]:.3f}   ({rec[k]/(k/len(keys)):.0f}x random floor)")
        ok = rec[10] >= 20 * floor10              # decisively beats random (the real claim)
        print("PASS" if ok else "FAIL")
        sys.exit(0 if ok else 1)

    # suggest mode: a real query (default to a held-out theorem if none given)
    statement = " ".join(sys.argv[1:]).strip()
    if not statement:
        statement = pairs[123]["a"]
        print(f"(no query given; demoing on theorem '{pairs[123].get('thm','?')}')")
    print(f"query: {statement[:110]}\ntop-10 suggested premises:")
    order = rank(model, vocab, statement, keys)
    for r, i in enumerate(order[:10], 1):
        print(f"  {r:>2}. {names[i]}")


if __name__ == "__main__":
    main()
