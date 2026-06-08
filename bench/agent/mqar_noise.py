#!/usr/bin/env python3
"""mqar_noise.py — noise-robustness of the energy read as an associative memory.

A one-step energy read over stored keys IS softmax attention, and softmax
attention is a high-capacity associative memory (modern Hopfield; Ramsauer et al.
2020, arXiv:2008.02217). This benchmark isolates one property of that read: how
gracefully it recovers a stored value when the query is a CORRUPTED version of a
stored key. That is the associative-memory regime — retrieve the clean stored
pattern from a noisy cue — and it is exactly where an attractor read should beat a
bounded-state alternative.

  task   : store N random unit-norm keys with distinct value ids. Each query is a
           stored key perturbed by Gaussian noise (std = sigma) and re-normalized.
  energy : w = softmax(beta * Q K^T), beta = sqrt(dim); predict value of the
           argmax-weight key (the selector's read, = softmax attention exactly).
  linear : bounded-capacity baseline w_i ~ phi(Q) phi(K)^T, phi = elu+1 (linear-
           attention feature map; no softmax); predict value of argmax-weight key.

Sweeps the noise level sigma at fixed store size and reports the recall of each
read. The energy read should stay robust as the cue degrades. Parameter-free,
deterministic, CPU — no training.

Run:  python3 bench/agent/mqar_noise.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import torch
import torch.nn.functional as F

ROOT = Path(__file__).resolve().parent

N_PAIRS = 128
DIM = 64
N_QUERIES = 2000
SEED = 0
SIGMAS = [0.0, 0.1, 0.3, 0.5, 1.0]


def make_task(n_pairs, dim, n_queries, sigma, g):
    """N random unit-norm keys, distinct value ids, queries = stored keys + Gaussian noise."""
    K = F.normalize(torch.randn(n_pairs, dim, generator=g), dim=1)
    values = torch.arange(n_pairs)
    qi = torch.randint(0, n_pairs, (n_queries,), generator=g)
    Q = K[qi]
    if sigma > 0:
        Q = F.normalize(Q + sigma * torch.randn(n_queries, dim, generator=g), dim=1)
    return K, values, Q, values[qi]


def energy_read(K, Q, beta):
    """Selector's read: w = softmax(beta * Q K^T); predict value of argmax-weight key."""
    w = F.softmax(beta * (Q @ K.t()), dim=1)
    return w.argmax(dim=1)


def linear_read(K, Q):
    """Bounded-capacity baseline: linear-attention weights, phi = elu+1 (no softmax)."""
    phi = lambda x: F.elu(x) + 1.0
    s = phi(Q) @ phi(K).t()
    return s.argmax(dim=1)


def recall_acc(pred_idx, values, true_val):
    return float((values[pred_idx] == true_val).float().mean())


def main():
    beta = DIM ** 0.5
    g = torch.Generator().manual_seed(SEED)

    rows = []
    for sigma in SIGMAS:
        K, values, Q, true_val = make_task(N_PAIRS, DIM, N_QUERIES, sigma, g)
        e_idx = energy_read(K, Q, beta)
        l_idx = linear_read(K, Q)
        rows.append({"sigma": sigma,
                     "energy_recall": round(recall_acc(e_idx, values, true_val), 4),
                     "linear_recall": round(recall_acc(l_idx, values, true_val), 4)})

    out = {"bench": "mqar_noise_robustness", "n_pairs": N_PAIRS, "dim": DIM,
           "beta": round(beta, 3), "queries": N_QUERIES, "seed": SEED,
           "noise_curve": rows}
    (ROOT / "mqar_noise_result.json").write_text(json.dumps(out, indent=2))

    print(f"=== MQAR noise robustness (N={N_PAIRS}, dim={DIM}, beta={beta:.2f}, "
          f"queries={N_QUERIES}, seed={SEED}) ===")
    print(f"  {'sigma':>6} | {'energy_recall':>13} | {'linear_recall':>13}")
    for r in rows:
        print(f"  {r['sigma']:>6} | {r['energy_recall']:>13} | {r['linear_recall']:>13}")
    print(f"  -> bench/agent/mqar_noise_result.json")

    # The corroboration claim (same as the dim/haystack benchmarks): the energy read
    # beats the linear baseline at EVERY condition. The gate tests exactly that.
    energy_ge_linear = all(r["energy_recall"] >= r["linear_recall"] for r in rows)
    # Honest measured LIMIT (reported, NOT gated): the parameter-free read is not
    # noise-invariant — recall degrades as the query is corrupted.
    min_energy = min(r["energy_recall"] for r in rows)
    ok = energy_ge_linear
    print(f"\n  energy>=linear @ every sigma={energy_ge_linear}  => {'PASS' if ok else 'FAIL'}")
    print(f"  honest limit (reported, not gated): energy recall degrades under noise, "
          f"min={min_energy} (NOT noise-invariant)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
