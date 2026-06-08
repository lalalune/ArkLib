#!/usr/bin/env python3
"""mqar_dim.py — tests energy-read associative-memory capacity vs embedding dimension.

A one-step energy read over stored keys is softmax attention, which acts as a
high-capacity associative memory (modern Hopfield; Ramsauer et al. 2020,
arXiv:2008.02217). That theory predicts capacity grows fast with embedding
dimension: with random near-orthogonal keys, recall should rise toward 1.0 as the
dimension D increases. This benchmark isolates that claim by fixing the store size
and sweeping D, comparing the energy read against a bounded-state linear baseline.

  task   : store N random unit-norm keys with distinct value ids; query = stored key.
  energy : w = softmax(beta * Q K^T), beta = sqrt(D); recall = value of argmax key.
  linear : bounded-capacity baseline  w_i ~ phi(Q) phi(K)^T,  phi = elu+1 (no softmax).

Parameter-free, deterministic, CPU — no training. torch-only, self-contained.

Run:  python3 bench/agent/mqar_dim.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import torch
import torch.nn.functional as F

ROOT = Path(__file__).resolve().parent

N_KEYS = 256
N_QUERIES = 2000
SEED = 0
DIMS = [8, 16, 32, 64, 128]


def make_task(n_pairs, dim, n_queries, g):
    """N random unit-norm keys, distinct value ids, queries = stored keys (no noise)."""
    K = F.normalize(torch.randn(n_pairs, dim, generator=g), dim=1)
    values = torch.arange(n_pairs)
    qi = torch.randint(0, n_pairs, (n_queries,), generator=g)
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
    rows = []
    for dim in DIMS:
        g = torch.Generator().manual_seed(SEED)
        beta = dim ** 0.5
        K, values, Q, true_val = make_task(N_KEYS, dim, N_QUERIES, g)
        e_idx = energy_read(K, Q, beta)
        l_idx = linear_read(K, Q)
        rows.append({"dim": dim,
                     "beta": round(beta, 3),
                     "energy_recall": round(recall_acc(e_idx, values, true_val), 4),
                     "linear_recall": round(recall_acc(l_idx, values, true_val), 4)})

    out = {"bench": "mqar_dim", "n_keys": N_KEYS, "queries": N_QUERIES,
           "seed": SEED, "dims": DIMS, "results": rows}
    (ROOT / "mqar_dim_result.json").write_text(json.dumps(out, indent=2))

    print(f"=== MQAR recall vs embedding dim (N={N_KEYS} keys, "
          f"queries={N_QUERIES}, seed={SEED}) ===")
    print(f"  {'dim':>6} | {'energy_recall':>13} | {'linear_recall':>13}")
    for r in rows:
        print(f"  {r['dim']:>6} | {r['energy_recall']:>13} | {r['linear_recall']:>13}")
    print(f"  -> bench/agent/mqar_dim_result.json")

    energy = [r["energy_recall"] for r in rows]
    monotone = all(b >= a for a, b in zip(energy, energy[1:]))
    by_dim = {r["dim"]: r for r in rows}
    reaches = by_dim[64]["energy_recall"] >= 0.95
    beats_linear = all(r["energy_recall"] >= r["linear_recall"] for r in rows)
    ok = monotone and reaches and beats_linear
    print(f"\n  monotone_nondecr={monotone}  energy@D=64>=0.95={reaches}  "
          f"energy>=linear@all={beats_linear}  => {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
