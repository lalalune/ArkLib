/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.CommitmentScheme.MerkleTree.Extraction
import VCVio

/-!
# Hiding for inductive Merkle-tree commitments (salted leaves)

A plain Merkle commitment is *not* hiding: the root and an opening can leak information about the
committed leaf (e.g. a low-entropy leaf can be brute-forced through the public hash). The standard
fix (SNARGs book §18) is to commit to *salted* leaves: each leaf `v` is replaced by a leaf
commitment `leafCommit r v` using fresh randomness (salt) `r`, and the Merkle tree is built over the
salted leaves. Opening reveals `(v, r)` together with the authentication path.

This file provides:

* `leafCommit` / `saltedLeaves` / `buildSaltedTree` — the salted-leaf commitment construction over
  the VCVio inductive Merkle tree.
* `salted_completeness` — a **fully proven** correctness lemma: the salted construction is itself an
  honest Merkle tree over the commitment leaves, so single-index completeness transports verbatim.
* `Hiding` — the **definition** of the hiding security property in the indistinguishability style
  (SNARGs book §18): the joint distribution of `(root, openings)` for any two leaf assignments that
  agree on the *opened* positions are computationally indistinguishable. This is stated as a `Prop`
  over distributions; it is *not* proven here, because establishing it requires a random-oracle /
  computational-indistinguishability argument over the salt distribution (see the roadmap below).

## Roadmap for a full hiding proof (not attempted here — research-grade)

A simulation-based hiding proof needs: (1) a simulator that produces `(root, openings)` from only
the opened leaves and the public parameters, sampling the unopened salted leaves uniformly; and
(2) a hybrid argument over the random oracle showing the simulated and real transcripts are
statistically/computationally close, using that each unopened salted leaf `leafCommit r v` is
(near-)uniform when `r` is fresh. Neither ingredient is available as a finished VCVio lemma, so we
record the property as a definition and keep the construction-level correctness fully proven.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/-- A salted leaf commitment: combine a leaf value `v` with salt `r` via the compression function.
Using the same two-to-one `hashFn` keeps the construction inside the single-oracle model. -/
def leafCommit (hashFn : α → α → α) (r v : α) : α := hashFn r v

/-- Replace every leaf `v` of the data tree by its salted commitment, given a salt tree `salts`
of the same shape. -/
def saltedLeaves {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : LeafData α s :=
  match salts, leaves with
  | LeafData.leaf r, LeafData.leaf v => LeafData.leaf (leafCommit hashFn r v)
  | LeafData.internal sl sr, LeafData.internal ll lr =>
    LeafData.internal (saltedLeaves hashFn sl ll) (saltedLeaves hashFn sr lr)

/-- Build the salted Merkle tree: hash the salted leaves into a tree using `hashFn`. -/
def buildSaltedTree {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : FullData α s :=
  buildMerkleTreeWithHash (saltedLeaves hashFn salts leaves) hashFn

/-- The leaf value used in a salted opening at index `idx` is the salted commitment of the
underlying leaf with its salt. -/
theorem saltedLeaves_get {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    (saltedLeaves hashFn salts leaves).get idx
      = leafCommit hashFn (salts.get idx) (leaves.get idx) := by
  induction idx with
  | ofLeaf =>
    cases salts; cases leaves; rfl
  | ofLeft idxLeft ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofLeft]
        exact ih sl ll
  | ofRight idxRight ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofRight]
        exact ih sr lr

/-- **Salted-construction completeness** (fully proven): an honest opening of the salted tree —
the salted leaf commitment at `idx` plus the honest path — verifies against the salted root.
The salted construction is just a Merkle tree over the commitment leaves, so the single-index
`functional_completeness` applies directly. -/
theorem salted_completeness {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    getPutativeRootWithHash idx
      ((saltedLeaves hashFn salts leaves).get idx)
      (generateProof (buildSaltedTree hashFn salts leaves) idx) hashFn
      = (buildSaltedTree hashFn salts leaves).getRootValue := by
  unfold buildSaltedTree
  exact functional_completeness idx (saltedLeaves hashFn salts leaves) hashFn

/-- **Same-salt deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same salt, sibling path, and root cannot
reveal different underlying leaf values. This is still the deterministic core only: the
random-oracle collision-probability step remains a separate probabilistic statement. -/
theorem salted_opening_binding_value {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt value₂) proof hashFn
      = rootValue) :
    value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt value₁ = leafCommit hashFn salt value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt value₁) (leafCommit hashFn salt value₂) rootValue proof h₁ h₂
  exact (hinj salt value₁ salt value₂ hcommit).2

/-- **Pair-level deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same sibling path and root determine the
entire salted opening pair: both the salt and the underlying leaf value are equal.

This is still only the deterministic no-collision implication. The random-oracle step that bounds
the probability of violating the collision-free premise remains separate. -/
theorem salted_opening_binding_pair {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt₁ salt₂ value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt₁ value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt₂ value₂) proof hashFn
      = rootValue) :
    salt₁ = salt₂ ∧ value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt₁ value₁ = leafCommit hashFn salt₂ value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt₁ value₁) (leafCommit hashFn salt₂ value₂) rootValue proof h₁ h₂
  exact hinj salt₁ value₁ salt₂ value₂ hcommit

/-- **Honest salted-opening uniqueness.** If a candidate salted pair verifies against the honest
salted root using the honest authentication path, then it is the honest salt and leaf at that
index, assuming the compression function is collision-free.

This is the salted analogue of the deterministic extractor soundness in `Extraction.lean`: the
honest salted tree and path pin down the opened `(salt, value)` pair. -/
theorem salted_opening_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s)
    (salt value : α)
    (h : getPutativeRootWithHash idx (leafCommit hashFn salt value)
        (generateProof (buildSaltedTree hashFn salts leaves) idx) hashFn
        = (buildSaltedTree hashFn salts leaves).getRootValue) :
    salt = salts.get idx ∧ value = leaves.get idx := by
  apply salted_opening_binding_pair idx hashFn hinj salt (salts.get idx) value (leaves.get idx)
    (buildSaltedTree hashFn salts leaves).getRootValue
    (generateProof (buildSaltedTree hashFn salts leaves) idx) h
  simpa [saltedLeaves_get] using salted_completeness hashFn salts leaves idx

/-- **Multi-opening deterministic uniqueness for honest salted trees.** Every accepting salted
opening in a finite list, checked against the honest salted root with the honest path for its index,
reveals the honest salt and leaf value at that index.

This is the salted analogue of `multi_instance_extracted_leaves_unique`; it is still a deterministic
no-collision statement, not the probabilistic random-oracle binding theorem. -/
theorem multi_salted_openings_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s)
    (openings : List ((_ : SkeletonLeafIndex s) × α × α))
    (hver : ∀ o ∈ openings,
      getPutativeRootWithHash o.1 (leafCommit hashFn o.2.1 o.2.2)
        (generateProof (buildSaltedTree hashFn salts leaves) o.1) hashFn
        = (buildSaltedTree hashFn salts leaves).getRootValue) :
    ∀ o ∈ openings, o.2.1 = salts.get o.1 ∧ o.2.2 = leaves.get o.1 := by
  intro o ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves o.1 o.2.1 o.2.2
    (hver o ho)

/-- The transcript an honest committer publishes when opening a set of indices: the salted root
together with, for each opened index, the salt, the underlying leaf, and the authentication path. -/
def openTranscript {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) :=
  let tree := buildSaltedTree hashFn salts leaves
  (tree.getRootValue,
    idxs.map (fun i => ⟨i, salts.get i, leaves.get i, generateProof tree i⟩))

/-- The honest salted transcript root is the root of the salted Merkle tree. -/
theorem openTranscript_root_eq {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).1 =
      (buildSaltedTree hashFn salts leaves).getRootValue := by
  simp [openTranscript]

/-- The honest salted transcript entries are exactly the requested indices mapped to their honest
salt, leaf value, and authentication path. -/
theorem openTranscript_entries_eq {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).2 =
      idxs.map
        (fun i =>
          ⟨i, salts.get i, leaves.get i,
            generateProof (buildSaltedTree hashFn salts leaves) i⟩) := by
  simp [openTranscript]

/-- If two leaf assignments agree on the requested opened indices under the same salts, then the
honest transcripts reveal the same opened payloads `(index, salt, value)`. This is the
deterministic payload projection used by hiding simulators; roots and authentication paths still
depend on the unopened leaves and are not compared here. -/
theorem openTranscript_entries_payload_eq_of_agree {s : Skeleton} (hashFn : α → α → α)
    (salts leaves₁ leaves₂ : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hagree : ∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) :
    ((openTranscript hashFn salts leaves₁ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) =
      ((openTranscript hashFn salts leaves₂ idxs).2.map
        (fun o => (o.1, o.2.1, o.2.2.1))) := by
  simp [openTranscript, Function.comp_def]
  exact hagree

/-- The honest salted transcript emits exactly one opening entry for each requested index. -/
theorem openTranscript_entries_length {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    (openTranscript hashFn salts leaves idxs).2.length = idxs.length := by
  simp [openTranscript]

/-- Projecting honest salted transcript entries to their indices recovers the requested index list.
This names the basic transcript-shape invariant used by simulators and deterministic extractors. -/
theorem openTranscript_entries_indices {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ((openTranscript hashFn salts leaves idxs).2.map (fun o => o.1)) = idxs := by
  simp [openTranscript, Function.comp_def]

/-- If the requested opened indices are duplicate-free, then the honest salted transcript entries
are duplicate-free too. This is transcript-shape bookkeeping for simulator/extractor arguments:
each entry carries its requested index as the first field. -/
theorem openTranscript_entries_nodup {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (hidxs : idxs.Nodup) :
    (openTranscript hashFn salts leaves idxs).2.Nodup := by
  simpa [openTranscript] using hidxs.map (by
    intro i j h
    exact congrArg (fun o => o.1) h)

/-- Every opening emitted by the honest salted transcript carries the honest salt and leaf value
for its own index. This exposes the transcript data invariant used by deterministic extraction and
future simulator/hybrid arguments. -/
theorem openTranscript_entry_eq_honest_pair {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      o.2.1 = salts.get o.1 ∧ o.2.2.1 = leaves.get o.1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simp

/-- Every opening emitted by the honest salted transcript carries the honest authentication path
for its own index. This completes the transcript-shape invariants for index, salt/value, and path
fields. -/
theorem openTranscript_entry_path_eq_honest_proof {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      o.2.2.2 = generateProof (buildSaltedTree hashFn salts leaves) o.1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simp

/-- Every opening emitted by the honest salted transcript verifies against the transcript root. This
is the list-level packaging of `salted_completeness` used by future simulator/hybrid arguments. -/
theorem openTranscript_entry_verifies {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    ∀ o ∈ (openTranscript hashFn salts leaves idxs).2,
      getPutativeRootWithHash o.1 (leafCommit hashFn o.2.1 o.2.2.1) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1 := by
  intro o ho
  simp [openTranscript] at ho ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  simpa [saltedLeaves_get] using salted_completeness hashFn salts leaves i

/-- Any candidate salted pair that verifies against the transcript root using an honest transcript
entry's path equals the pair carried by that entry. This packages deterministic extraction for
individual entries of `openTranscript`. -/
theorem openTranscript_entry_unique_against_candidate {s : Skeleton} (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (o : (i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)
    (ho : o ∈ (openTranscript hashFn salts leaves idxs).2)
    (salt value : α)
    (h : getPutativeRootWithHash o.1 (leafCommit hashFn salt value) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    salt = o.2.1 ∧ value = o.2.2.1 := by
  simp [openTranscript] at ho h ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves i salt value (by
    simpa [openTranscript] using h)

/-- Any candidate salted pair that verifies against an honest transcript entry's path equals the
honest salt and leaf at that entry's index. This is the transcript-facing form of
`salted_opening_unique_against_honest_tree`, useful for deterministic extraction statements that
want the honest tree values rather than the pair stored in the transcript entry. -/
theorem openTranscript_candidate_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (o : (i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth)
    (ho : o ∈ (openTranscript hashFn salts leaves idxs).2)
    (salt value : α)
    (h : getPutativeRootWithHash o.1 (leafCommit hashFn salt value) o.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    salt = salts.get o.1 ∧ value = leaves.get o.1 := by
  simp [openTranscript] at ho h ⊢
  obtain ⟨i, _hi, rfl⟩ := ho
  exact salted_opening_unique_against_honest_tree hashFn hinj salts leaves i salt value (by
    simpa [openTranscript] using h)

/-- Batch transcript-entry deterministic extraction. For any finite list of candidate salted
opening pairs attached to honest transcript entries, if each candidate verifies against the honest
transcript root using the attached path, then every candidate pair equals the salt and leaf pair
stored in that transcript entry. -/
theorem openTranscript_candidates_unique_against_entries {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (attempts :
      List (((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) × α × α))
    (hmem : ∀ a ∈ attempts, a.1 ∈ (openTranscript hashFn salts leaves idxs).2)
    (hver : ∀ a ∈ attempts,
      getPutativeRootWithHash a.1.1 (leafCommit hashFn a.2.1 a.2.2) a.1.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    ∀ a ∈ attempts, a.2.1 = a.1.2.1 ∧ a.2.2 = a.1.2.2.1 := by
  intro a ha
  exact openTranscript_entry_unique_against_candidate hashFn hinj salts leaves idxs
    a.1 (hmem a ha) a.2.1 a.2.2 (hver a ha)

/-- Batch transcript-facing deterministic extraction. For any finite list of candidate salted
opening pairs attached to honest transcript entries, if each candidate verifies against the honest
transcript root using the attached path, then every candidate pair is the honest salt and leaf at
that entry's index. -/
theorem openTranscript_candidates_unique_against_honest_tree {s : Skeleton}
    (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (attempts :
      List (((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) × α × α))
    (hmem : ∀ a ∈ attempts, a.1 ∈ (openTranscript hashFn salts leaves idxs).2)
    (hver : ∀ a ∈ attempts,
      getPutativeRootWithHash a.1.1 (leafCommit hashFn a.2.1 a.2.2) a.1.2.2.2 hashFn
        = (openTranscript hashFn salts leaves idxs).1) :
    ∀ a ∈ attempts, a.2.1 = salts.get a.1.1 ∧ a.2.2 = leaves.get a.1.1 := by
  intro a ha
  exact openTranscript_candidate_unique_against_honest_tree hashFn hinj salts leaves idxs
    a.1 (hmem a ha) a.2.1 a.2.2 (hver a ha)

section HidingDefinition

variable [DecidableEq α] [SampleableType α]

/-- **Hiding (indistinguishability definition, SNARGs book §18).** A salted Merkle commitment is
hiding for a fixed opened index set `idxs` if, for *any* two leaf assignments `leaves₁`, `leaves₂`
that agree on the opened positions, the published transcripts are computationally indistinguishable
when the salts are drawn from the salt sampler `sampleSalts`. We phrase indistinguishability as
equality of the induced output distributions of the transcript over the random choice of salts —
the perfect-hiding specialization; a computational version would replace `=` by an
indistinguishability relation.

This is a *definition only*; see the module roadmap for why a proof is out of scope here. -/
def Hiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) : Prop :=
  ∀ (leaves₁ leaves₂ : LeafData α s),
    (∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) →
    (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₁ idxs))
      = (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₂ idxs))

end HidingDefinition

end InductiveMerkleTree

/-! ### Axiom audit (issue #119 salted Merkle construction / hiding-definition front doors) -/

#print axioms InductiveMerkleTree.saltedLeaves_get
#print axioms InductiveMerkleTree.salted_completeness
#print axioms InductiveMerkleTree.salted_opening_binding_value
#print axioms InductiveMerkleTree.salted_opening_binding_pair
#print axioms InductiveMerkleTree.salted_opening_unique_against_honest_tree
#print axioms InductiveMerkleTree.multi_salted_openings_unique_against_honest_tree
#print axioms InductiveMerkleTree.openTranscript
#print axioms InductiveMerkleTree.openTranscript_root_eq
#print axioms InductiveMerkleTree.openTranscript_entries_eq
#print axioms InductiveMerkleTree.openTranscript_entries_payload_eq_of_agree
#print axioms InductiveMerkleTree.openTranscript_entries_length
#print axioms InductiveMerkleTree.openTranscript_entries_indices
#print axioms InductiveMerkleTree.openTranscript_entries_nodup
#print axioms InductiveMerkleTree.openTranscript_entry_eq_honest_pair
#print axioms InductiveMerkleTree.openTranscript_entry_path_eq_honest_proof
#print axioms InductiveMerkleTree.openTranscript_entry_verifies
#print axioms InductiveMerkleTree.openTranscript_entry_unique_against_candidate
#print axioms InductiveMerkleTree.openTranscript_candidate_unique_against_honest_tree
#print axioms InductiveMerkleTree.openTranscript_candidates_unique_against_entries
#print axioms InductiveMerkleTree.openTranscript_candidates_unique_against_honest_tree
#print axioms InductiveMerkleTree.Hiding
