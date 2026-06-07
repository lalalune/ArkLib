#!/usr/bin/env python3
"""ebm_core.py — a small self-contained contrastive energy model for ranking.

A tiny decoder-style transformer with a scalar energy head over a pair
``[<BOS> A <SEP> B <EOS>]``. Trained with an InfoNCE objective so the true
``(A, B)`` pairing has the lowest energy among in-batch alternatives, it learns
to rank which ``B`` belongs to a given ``A``. Here ``A`` is a theorem statement
and ``B`` is a candidate premise (see ``rank_train_eval.py``).

Pure PyTorch, no external project dependency — runs on CPU or Apple MPS.
~500k params at the default config.
"""
from __future__ import annotations

import random
import re

import torch
import torch.nn as nn
import torch.nn.functional as F

# Fixed special-token ids.
PAD, UNK, SEP, EOS, BOS = 0, 1, 2, 3, 4
SPECIAL_TOKENS = ["<PAD>", "<UNK>", "<SEP>", "<EOS>", "<BOS>"]

MAX_LEN = 96

_WORD_RE = re.compile(r"[a-z]+|[0-9]+|[\.,;:!?]")


def tokenize(text: str) -> list[str]:
    """Word-level tokens. Inputs are already subworded to lowercase by the miner,
    so this just splits on the word/number/punctuation regex."""
    return _WORD_RE.findall(text.lower())


def encode(text: str, vocab: dict[str, int]) -> list[int]:
    return [vocab.get(w, UNK) for w in tokenize(text)]


def encode_pair(a: str, b: str, vocab: dict[str, int], max_len: int = MAX_LEN) -> list[int]:
    ids = [BOS] + encode(a, vocab) + [SEP] + encode(b, vocab) + [EOS]
    return ids[:max_len]


def pad(batch: list[list[int]], max_len: int) -> list[list[int]]:
    return [seq + [PAD] * (max_len - len(seq)) for seq in batch]


class MiniTransformer(nn.Module):
    """Tiny pre-norm transformer encoder with a scalar energy head."""

    def __init__(self, vocab_size: int, d_model: int = 128, nhead: int = 4,
                 nlayers: int = 4, d_ff: int = 512, max_len: int = MAX_LEN,
                 dropout: float = 0.1):
        super().__init__()
        self.d_model = d_model
        self.max_len = max_len
        self.tok_emb = nn.Embedding(vocab_size, d_model, padding_idx=PAD)
        self.pos_emb = nn.Embedding(max_len, d_model)
        layer = nn.TransformerEncoderLayer(
            d_model=d_model, nhead=nhead, dim_feedforward=d_ff, dropout=dropout,
            batch_first=True, activation="gelu", norm_first=True,
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=nlayers)
        self.ln_f = nn.LayerNorm(d_model)
        self.energy_head = nn.Linear(d_model, 1)
        self.apply(self._init_weights)

    @staticmethod
    def _init_weights(m: nn.Module) -> None:
        if isinstance(m, nn.Linear):
            nn.init.normal_(m.weight, mean=0.0, std=0.02)
            if m.bias is not None:
                nn.init.zeros_(m.bias)
        elif isinstance(m, nn.Embedding):
            nn.init.normal_(m.weight, mean=0.0, std=0.02)

    def _encode(self, ids: torch.Tensor) -> torch.Tensor:
        B, T = ids.shape
        pos = torch.arange(T, device=ids.device).unsqueeze(0).expand(B, T)
        x = self.tok_emb(ids) + self.pos_emb(pos)
        pad_mask = ids == PAD
        causal = torch.triu(torch.ones(T, T, device=ids.device, dtype=torch.bool), diagonal=1)
        h = self.encoder(x, mask=causal, src_key_padding_mask=pad_mask)
        return self.ln_f(h)

    def energy(self, ids: torch.Tensor) -> torch.Tensor:
        """Scalar energy per sequence (lower = preferred). Pools the hidden state
        at the last non-pad position of ``[<BOS> A <SEP> B <EOS>]``."""
        h = self._encode(ids)
        nonpad = (ids != PAD).long()
        last_idx = (nonpad.sum(dim=1) - 1).clamp(min=0)
        pooled = h[torch.arange(h.size(0), device=h.device), last_idx]
        return self.energy_head(pooled).squeeze(-1)

    def param_count(self) -> int:
        return sum(p.numel() for p in self.parameters())


def infonce_energy_loss(model, batch, vocab, device):
    """BxB grid of (A_i, B_j) energies; the diagonal is the positive pairing.
    Loss = cross-entropy over ``-energy`` with target = diagonal index."""
    items = batch["items"]
    B = len(items)
    grid_ids = [encode_pair(items[i]["a"], items[j]["b"], vocab, MAX_LEN)
                for i in range(B) for j in range(B)]
    max_t = max(len(x) for x in grid_ids)
    ids_tensor = torch.tensor(pad(grid_ids, max_t), dtype=torch.long, device=device)
    energies = model.energy(ids_tensor).view(B, B)
    targets = torch.arange(B, device=device)
    return F.cross_entropy(-energies, targets)


@torch.no_grad()
def run_probe(model, eval_items, pool_items, vocab, device, k=100, seed=0):
    """Rank each held-out item's true B-premise against ``k-1`` distractors drawn
    from the pool. Returns R@1/R@5/R@10/MRR."""
    rng = random.Random(seed)
    model.eval()
    pool_by_ref = {c["ref"]: c for c in pool_items}
    ranks = []
    actual_k = k
    for item in eval_items:
        ref = item["ref"]
        pool_refs = [r for r in pool_by_ref if r != ref]
        take = min(k - 1, len(pool_refs))
        actual_k = take + 1
        distractor_refs = rng.sample(pool_refs, take)
        candidate_bs = [item["b"]] + [pool_by_ref[r]["b"] for r in distractor_refs]
        grid_ids = [encode_pair(item["a"], b, vocab, MAX_LEN) for b in candidate_bs]
        max_t = max(len(x) for x in grid_ids)
        ids = torch.tensor(pad(grid_ids, max_t), dtype=torch.long, device=device)
        energies = model.energy(ids).tolist()
        true_e = energies[0]
        higher = sum(1 for e in energies[1:] if e < true_e)
        ties = sum(1 for e in energies[1:] if e == true_e)
        ranks.append(1 + higher + ties // 2)
    model.train()
    n = len(ranks)
    return {
        "R@1": round(sum(1 for r in ranks if r == 1) / n, 4),
        "R@5": round(sum(1 for r in ranks if r <= 5) / n, 4),
        "R@10": round(sum(1 for r in ranks if r <= 10) / n, 4),
        "MRR": round(sum(1.0 / r for r in ranks) / n, 4),
        "k": actual_k, "n": n, "seed": seed,
    }
