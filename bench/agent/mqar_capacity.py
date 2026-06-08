#!/usr/bin/env python3
"""mqar_capacity.py — why an energy read makes a good premise selector.

The premise selector (rank_train_eval.py) ranks candidate lemmas for a goal by a
scalar energy. This benchmark isolates *why* that mechanism works: a one-step energy
read over stored keys IS softmax attention, and softmax attention is a high-capacity
associative memory (modern Hopfield; Ramsauer et al. 2020, arXiv:2008.02217). The
standard probe is MQAR — Multi-Query Associative Recall (Arora et al., Zoology,
arXiv:2312.04927) — where softmax attention recalls stored values at high capacity
while a bounded-state alternative (linear attention) collapses as the store grows.

  task   : store N (key, value) pairs; for each query key, recall its value.
  energy : w = softmax(beta * K q);  recall = value of argmax_i w_i
           (the selector's read, = softmax attention exactly).
  linear : bounded-capacity baseline  w_i ~ phi(k_i).phi(q),  phi = elu+1
           (linear-attention feature map; no softmax).

Reports (1) max|Δw| between the energy read and a reference softmax-attention read
(should be ~0 — they are the same operation), and (2) the recall capacity curve vs N
for energy vs linear. Parameter-free, deterministic, CPU — no training.

Run:  python3 bench/agent/mqar_capacity.py
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import torch
import torch.nn.functional as F

ROOT = Path(__file__).resolve().parent


def make_task(n_pairs, dim, n_queries, noise, g):
    """N random unit-norm keys, distinct value ids, queries = stored keys (+optional noise)."""
    K = F.normalize(torch.randn(n_pairs, dim, generator=g), dim=1)
    values = torch.arange(n_pairs)
    qi = torch.randint(0, n_pairs, (n_queries,), generator=g)
    Q = K[qi]
    if noise > 0:
        Q = F.normalize(Q + noise * torch.randn(n_queries, dim, generator=g), dim=1)
    return K, values, Q, values[qi]


def energy_read(K, Q, beta):
    """Selector's read: w = softmax(beta * K q^T); predict value of argmax-weight key."""
    w = F.softmax(beta * (Q @ K.t()), dim=1)
    return w.argmax(dim=1), w


def linear_read(K, Q):
    """Bounded-capacity baseline: linear-attention weights, phi = elu+1 (no softmax)."""
    phi = lambda x: F.elu(x) + 1.0
    s = phi(Q) @ phi(K).t()
    s = s / s.sum(dim=1, keepdim=True).clamp_min(1e-9)
    return s.argmax(dim=1)


def recall_acc(pred_idx, values, true_val):
    return float((values[pred_idx] == true_val).float().mean())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dim", type=int, default=64)
    ap.add_argument("--beta", type=float, default=None)
    ap.add_argument("--queries", type=int, default=2000)
    ap.add_argument("--noise", type=float, default=0.0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--Ns", type=int, nargs="+", default=[8, 16, 32, 64, 128, 256, 512, 1024])
    args = ap.parse_args()
    beta = args.beta if args.beta is not None else args.dim ** 0.5
    g = torch.Generator().manual_seed(args.seed)

    # (1) identity: energy read == softmax attention.
    K, values, Q, true_val = make_task(64, args.dim, 256, args.noise, g)
    _, w_energy = energy_read(K, Q, beta)
    w_attn = F.softmax(beta * (Q @ K.t()), dim=1)
    delta = float((w_energy - w_attn).abs().max())

    # (2) capacity curve: recall vs number of stored pairs, energy vs linear.
    rows = []
    for N in args.Ns:
        K, values, Q, true_val = make_task(N, args.dim, args.queries, args.noise, g)
        e_idx, _ = energy_read(K, Q, beta)
        l_idx = linear_read(K, Q)
        rows.append({"N": N,
                     "energy_recall": round(recall_acc(e_idx, values, true_val), 4),
                     "linear_recall": round(recall_acc(l_idx, values, true_val), 4)})

    out = {"bench": "mqar_associative_recall", "dim": args.dim, "beta": round(beta, 3),
           "queries": args.queries, "noise": args.noise, "seed": args.seed,
           "energy_eq_softmax_attention_delta": delta, "capacity_curve": rows}
    (ROOT / "mqar_result.json").write_text(json.dumps(out, indent=2))

    print(f"=== MQAR associative recall (dim={args.dim}, beta={beta:.2f}, "
          f"queries={args.queries}, noise={args.noise}) ===")
    print(f"  energy read == softmax attention?  max|Δw| = {delta:.2e}  "
          f"({'IDENTICAL' if delta < 1e-5 else 'DIFFERS'})")
    print(f"  {'N':>6} | {'energy(Hopfield)':>16} | {'linear-attn':>12}")
    for r in rows:
        print(f"  {r['N']:>6} | {r['energy_recall']:>16} | {r['linear_recall']:>12}")
    print(f"  -> bench/agent/mqar_result.json")

    big = [r for r in rows if r["N"] >= 256]
    identity_ok = delta < 1e-5
    capacity_ok = bool(big) and all(r["energy_recall"] >= 0.95 for r in big) \
        and all(r["energy_recall"] - r["linear_recall"] >= 0.10 for r in big)
    ok = identity_ok and capacity_ok
    print(f"\n  identity(Δ≈0)={identity_ok}  capacity(energy≫linear @N≥256)={capacity_ok}  "
          f"=> {'PASS' if ok else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
