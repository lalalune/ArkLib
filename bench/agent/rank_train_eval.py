#!/usr/bin/env python3
"""rank_train_eval.py — train a small contrastive energy model on REAL ArkLib
(theorem statement -> used premise) pairs and show it is a domain-matched premise
selector: on held-out theorems it ranks the truly-used premise among 99 distractors
far above the random floor AND above the untrained base.

This is the premise-selection component of a proof agent: an energy model ranks
candidate premises; the Lean kernel verifies. The objective is a standard InfoNCE
contrastive loss (goal -> premise). No inflated result: the gate fails unless the
trained ranker decisively beats both the random floor and the untrained base on
held-out theorems.

Exit 0 iff trained R@1 >= 2*floor AND >= 2*base R@1 AND MRR >= 1.3*base MRR.
"""
import json
import os
import random
import sys
from collections import Counter
from pathlib import Path

import torch

from ebm_core import (  # vendored, self-contained (bench/agent/ebm_core.py)
    MiniTransformer, tokenize, SPECIAL_TOKENS,
    infonce_energy_loss, run_probe, MAX_LEN,
)

HERE = Path(__file__).resolve().parent
DATA = HERE / "arklib_premises.jsonl"
CKPT = HERE / "arklib_premise_ebm.pt"
DEVICE = torch.device("mps" if torch.backends.mps.is_available() else "cpu")
SEED = 7


def build_vocab(pairs, top_k=8000):
    c = Counter()
    for p in pairs:
        c.update(tokenize(p["a"]))
        c.update(tokenize(p["b"]))
    vocab = {t: i for i, t in enumerate(SPECIAL_TOKENS)}
    for w, _ in c.most_common(top_k - len(SPECIAL_TOKENS)):
        vocab[w] = len(vocab)
    return vocab


def main():
    pairs = [json.loads(l) for l in DATA.read_text().splitlines() if l.strip()]
    for i, p in enumerate(pairs):
        p["ref"] = f"r{i}"
    rng = random.Random(SEED)
    rng.shuffle(pairs)
    vocab = build_vocab(pairs)
    n_eval = max(60, int(len(pairs) * 0.15))
    eval_, train_ = pairs[:n_eval], pairs[n_eval:]

    torch.manual_seed(SEED)
    base = MiniTransformer(len(vocab), max_len=MAX_LEN).to(DEVICE)
    base_m = run_probe(base, eval_, pairs, vocab, DEVICE, k=100, seed=0)

    torch.manual_seed(SEED)
    model = MiniTransformer(len(vocab), max_len=MAX_LEN).to(DEVICE)
    opt = torch.optim.AdamW(model.parameters(), lr=3e-4, weight_decay=0.01)
    EPOCHS = int(os.environ.get("ARKLIB_EBM_EPOCHS", "5"))
    BS = 64
    model.train()
    for ep in range(EPOCHS):
        random.Random(SEED + ep).shuffle(train_)
        tot, nb = 0.0, 0
        for i in range(0, len(train_), BS):
            batch = train_[i:i + BS]
            if len(batch) < 2:
                continue
            loss = infonce_energy_loss(model, {"items": batch}, vocab, DEVICE)
            opt.zero_grad()
            loss.backward()
            opt.step()
            tot += float(loss)
            nb += 1
        print(f"  epoch {ep+1}/{EPOCHS} infonce_loss={tot/max(1,nb):.4f}", flush=True)

    tr_m = run_probe(model, eval_, pairs, vocab, DEVICE, k=100, seed=0)
    floor = round(1 / 100, 4)
    print(json.dumps({"base": base_m, "trained": tr_m, "floor": floor,
                      "n_train": len(train_), "n_eval": n_eval, "vocab": len(vocab)}))
    ok = (tr_m["R@1"] >= 2 * floor and tr_m["R@1"] >= 2 * base_m["R@1"]
          and tr_m["MRR"] >= 1.3 * base_m["MRR"])
    CKPT.parent.mkdir(parents=True, exist_ok=True)
    torch.save({"state": model.state_dict(), "vocab": vocab, "metrics": tr_m,
                "base": base_m, "floor": floor, "passed": ok}, CKPT)
    print(f"[arklib-premise-ebm] {'PASS' if ok else 'FAIL'}: trained "
          f"R@1={tr_m['R@1']} (base {base_m['R@1']}, floor {floor}) = "
          f"{tr_m['R@1']/max(1e-9,base_m['R@1']):.1f}x base; "
          f"MRR {tr_m['MRR']} vs {base_m['MRR']} = "
          f"{tr_m['MRR']/max(1e-9,base_m['MRR']):.1f}x")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
