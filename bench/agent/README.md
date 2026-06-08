# Premise selector (energy-based) for ArkLib

A small contrastive **energy model** that, given an ArkLib theorem statement, ranks
the lemmas its proof actually uses above unrelated distractors. This is the
premise-selection component of a proof agent: it proposes *which* lemmas are likely
relevant; the Lean kernel still decides whether a proof using them type-checks.

It is **tooling, not a proof** — it closes no `sorry` and proves no theorem. It is a
ranking aid, measured honestly against a baseline.

## Pieces

| file | what it does | deps |
|---|---|---|
| `mine_premises.py` | mines `(theorem statement → used internal premise)` pairs from ArkLib's Lean source (lexical, no Lean execution) | stdlib only |
| `ebm_core.py` | self-contained tiny transformer + InfoNCE energy loss + held-out ranking probe | `torch` |
| `rank_train_eval.py` | trains the selector, evaluates on held-out theorems, exits non-zero unless it decisively beats the untrained baseline | `torch` |
| `rank_gate.sh` | the witness: mine → train → eval; exit 0 only on a decisive win | `torch` |
| `mqar_capacity.py` | *why* an energy read ranks well: associative-recall (MQAR) capacity of the energy read (= softmax attention) vs a bounded linear-attention baseline | `torch` |
| `suggest_premises.py` | the selector **as a tool**: given a goal statement, rank the whole library and return the top-k likely-relevant lemmas (`--witness` for held-out recall) | `torch` |

## Run

```bash
bash bench/agent/rank_gate.sh          # mines, trains, evaluates; exit 0 = pass
# override the interpreter: ARKLIB_EBM_PY=/path/to/python bash bench/agent/rank_gate.sh
```

`arklib_premises.jsonl` (mined pairs) and `arklib_premise_ebm.pt` (trained model) are
regenerable and gitignored.

## Method

Each `(statement, used-premise)` pair is encoded as `[<BOS> statement <SEP> premise
<EOS>]`; identifiers are split into subwords (`Polynomial.natDegree_mul → "polynomial
nat degree mul"`) so a word-level tokenizer sees real tokens. The model scores each
pair with a scalar **energy**; an InfoNCE objective drives the true pairing to the
lowest energy in its batch. Evaluation ranks each held-out statement's true premise
against 99 random distractors.

## Honest criterion

The gate passes **only** if the trained model beats an *identically-evaluated
untrained* model — never a fixed threshold that an untrained net could clear by
chance. Concretely: trained `R@1 ≥ 2×floor` and `≥ 2×base R@1`, and `MRR ≥ 1.3×base`.

Measured (mined ArkLib, ~6.2k theorems, 3.5k distinct premises; held-out n≈2.9k,
seed 7):

| | R@1 | R@10 | MRR |
|---|---|---|---|
| untrained base | 0.009 | — | 0.049 |
| trained | 0.333 | 0.797 | 0.484 |
| random floor | 0.010 | — | — |

→ R@1 ≈ 36× the untrained base; the energy model learns real structure in ArkLib's
internal premise graph. Numbers reproduce from the source tree (deterministic seed);
exact values shift slightly as the library evolves.
