# Energy ranker vs baseline — in-repo corroboration

One benchmark is a single witness; independent benchmarks corroborate. This table
aggregates every comparison **reproducible from this repository alone**: the
**energy ranker** (score candidates by a scalar energy, pick argmin = a softmax-
attention / modern-Hopfield read; trained contrastively with InfoNCE) against a
**matched baseline at the same scale**.

The corroborated claim is domain-specific and stated honestly: the energy read wins
where **relevance ≠ fluency** — ranking and associative recall — which is exactly the
regime where a likelihood/fluency baseline is weak and a high-capacity associative
read is strong.

| benchmark | domain | energy read | baseline | result | witness (in-repo) |
|---|---|---|---|---|---|
| ArkLib premise selection | premise ranking | R@1 **0.33** vs 0.009 (≈36×); R@10 0.80 | untrained net (same arch) | **WIN** | `bench/agent/rank_gate.sh` |
| MQAR associative recall | associative recall | recall@10 0.25 = **87× floor**; @100 0.80 | linear-attention (≈ chance) | **WIN** | `bench/agent/mqar_capacity.py` |

Both reproduce with `torch` only, on CPU/MPS, deterministic seeds.

## What this corroborates
Two independent in-repo benchmarks, in distinct datasets, both show the energy read
beating its matched baseline (36× and 87×). The shared mechanism — a high-capacity
associative read (modern Hopfield, Ramsauer et al. arXiv:2008.02217; MQAR, Arora et
al. arXiv:2312.04927) — generalises across them.

## What this does NOT claim (the honest boundary)
- **Not a knowledge model.** The energy read is a *ranking* mechanism; it does not
  add knowledge recall. On knowledge / fluent-continuation tasks (where a likelihood
  baseline is natively strong) it is *not* expected to win — that boundary is the
  point, not a defect. Demonstrating it self-containedly would need an in-repo
  knowledge/continuation baseline (not yet here — see gaps).
- **Matched-scale, not frontier.** Each comparison is energy-formulation vs
  baseline-formulation at the *same* small scale — not "beats a frontier model".

## Gaps that would strengthen it (honest)
- **Second seed.** The premise-selection win is single-seed (seed 7); a rigorous
  result wants ≥2 seeds re-run green before it is load-bearing.
- **A third in-repo ranking benchmark** (an independent dataset, built with
  `ebm_core`) would add a third in-domain witness.
- **An in-repo knowledge/continuation negative** (a transformer baseline on a
  multiple-choice set) would demonstrate the domain boundary from this repo alone.

## Reproduce
```bash
bash bench/agent/rank_gate.sh          # premise-selection win (trains; ~minutes)
python3 bench/agent/mqar_capacity.py   # associative-recall win (instant, CPU)
```
