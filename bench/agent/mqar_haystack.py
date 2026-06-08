#!/usr/bin/env python3
"""mqar_haystack.py — tests energy-read associative recall as the stored-key haystack scales.

A one-step energy read over N stored keys IS softmax attention, and softmax attention
is a high-capacity associative memory (modern Hopfield; Ramsauer et al. 2020,
arXiv:2008.02217). This probe is the haystack variant of MQAR (Multi-Query Associative
Recall; Arora et al., Zoology, arXiv:2312.04927): hold the key dimension D fixed and grow
the NUMBER of stored keys N, asking how gracefully recall degrades as the haystack grows.
A bounded-state alternative (linear attention) collapses faster than softmax as N grows.

  task   : store N random unit-norm keys with distinct value ids; query each stored key.
  energy : w = softmax(beta * Q K^T),  beta = sqrt(D);  recall = value of argmax-weight key.
  linear : bounded-capacity baseline  w_i ~ phi(q).phi(k_i),  phi = elu+1 (no softmax).

Parameter-free, deterministic, CPU — no training. Varies N in {64, 256, 1024, 4096} at
fixed D=64, 2000 queries, seed 0.

Run:  python3 bench/agent/mqar_haystack.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import torch
import torch.nn.functional as F

ROOT = Path(__file__).resolve().parent

DIM = 64
QUERIES = 2000
SEED = 0
NS = [64, 256, 1024, 4096]


def make_task(n_keys, dim, n_queries, g):
    """N random unit-norm keys, distinct value ids, queries = stored keys (no noise)."""
    K = F.normalize(torch.randn(n_keys, dim, generator=g), dim=1)
    values = torch.arange(n_keys)
    qi = torch.randint(0, n_keys, (n_queries,), generator=g)
    Q = K[qi]
    return K, values, Q, values[qi]


def energy_read(K, Q, beta):
    """Energy read: w = softmax(beta * Q K^T); predict value of argmax-weight key."""
    w = F.softmax(beta * (Q @ K.t()), dim=1)
    return w.argmax(dim=1)


def linear_read(K, Q):
    """Bounded-capacity baseline: linear-attention weights, phi = elu+1 (no softmax)."""
    phi = lambda x: F.elu(x) + 1.0
    s = phi(Q) @ phi(K).t()
    s = s / s.sum(dim=1, keepdim=True).clamp_min(1e-9)
    return s.argmax(dim=1)


def recall_acc(pred_idx, values, true_val):
    return float((values[pred_idx] == true_val).float().mean())


def main():
    beta = DIM ** 0.5
    g = torch.Generator().manual_seed(SEED)

    rows = []
    for N in NS:
        K, values, Q, true_val = make_task(N, DIM, QUERIES, g)
        e_idx = energy_read(K, Q, beta)
        l_idx = linear_read(K, Q)
        rows.append({"N": N,
                     "energy_recall": round(recall_acc(e_idx, values, true_val), 4),
                     "linear_recall": round(recall_acc(l_idx, values, true_val), 4)})

    out = {"bench": "mqar_haystack", "dim": DIM, "beta": round(beta, 3),
           "queries": QUERIES, "seed": SEED, "rows": rows}
    (ROOT / "mqar_haystack_result.json").write_text(json.dumps(out, indent=2))

    print(f"=== MQAR haystack (dim={DIM}, beta={beta:.2f}, queries={QUERIES}, seed={SEED}) ===")
    print(f"  {'N':>6} | {'energy_recall':>13} | {'linear_recall':>13}")
    for r in rows:
        print(f"  {r['N']:>6} | {r['energy_recall']:>13} | {r['linear_recall']:>13}")
    print(f"  -> bench/agent/mqar_haystack_result.json")

    through_1024 = [r for r in rows if r["N"] <= 1024]
    capacity_ok = all(r["energy_recall"] >= 0.9 for r in through_1024)
    dominance_ok = all(r["energy_recall"] >= r["linear_recall"] for r in rows)
    ok = capacity_ok and dominance_ok
    print(f"\n  energy>=0.9 through N=1024: {capacity_ok}   energy>=linear @ every N: {dominance_ok}   "
          f"=> {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
