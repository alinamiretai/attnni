# AttnNI — reference-implementation experiments (the utility gate)

Three experiments, in strict order. E1 validates the kernel correspondence
empirically (interface obligation 1). E2 is THE GATE: it measures the
utility tax and decides whether AttnNI proceeds as an inference-time shield,
a fine-tuning recipe + shield, or gets re-scoped. E3 ports the integrity
demos. Do not invest in E3 polish or any productization before E2 reads out.

## Setup

- Models: start with a small open model for iteration (1–3B class), confirm
  on a 7–8B class model. Instruction-tuned variants (the tasks are chat-shaped).
- Attention: `attn_implementation="eager"` first (most inspectable), then
  confirm on `"sdpa"`. Flash-style kernels come later — arbitrary 4D masks
  are exactly where their inspectability is weakest, which is the kernel-
  correspondence workstream's problem, not this harness's.
- Dtype: float32 for E1 (eliminate one variable), then repeat in bf16 —
  the bit-identity argument is dtype-independent (exact zeros), so bf16
  should ALSO be bit-identical; if fp32 passes and bf16 doesn't, that
  localizes a kernel-correspondence violation.
- Determinism: fixed seeds, deterministic algorithms on, no batching across
  the two runs (batch-size-dependent reductions are a known bitwise hazard;
  run the coupled pair as separate batch-1 calls).
- No KV cache in v0: recompute the full prefix each generation step. Slow
  and correct beats fast and confounded; cached generation with per-step
  4D masks is a v1 optimization to validate against v0's outputs.

## E1 — Bit-identity (the theorem, made empirical)

Prompt template with a designated secret span; two secrets A ≠ B tokenizing
to the SAME length (pad by construction). Label plan: prompt low, secret
span high, generated positions low. Mask: causal AND flows(label[k],
label[q]) — public rows never attend the secret span.

Assertions, in increasing strength:
1. Greedy-generated token ids identical for k tokens (k ≥ 20).
2. Logits at every public position bit-identical (`torch.equal`, not
   allclose) at every generation step.
3. Sampled generation with shared seed: identical token ids (Sampling.lean's
   coupling).
4. Negative control: corrupt one mask row (a public row attends the secret)
   → divergence appears and propagates (GenerationDemo's 414/2398 signature).
5. Secret-position sanity check: logits AT the secret span DO differ
   (otherwise the secret isn't entering the computation and the test is
   vacuous).

Pass = 1–3 exactly, 4–5 showing the expected signatures, on both eager and
SDPA, fp32 and bf16. Any allclose-but-not-equal result is a FINDING about
the kernel correspondence, to be diagnosed, not waved through.

## E2 — Utility under quarantine (THE GATE)

Question: how much does generation quality degrade when realistic quarantine
masks are imposed on a model pretrained with full attention?

Conditions per task: (a) full attention, secret present — baseline;
(b) quarantine mask, secret present — the shield; (c) full attention,
secret REMOVED from context — the utility ceiling for (b), since the shield
cannot beat not-having-the-secret; (d) quarantine mask over an EMPTY/dummy
secret span — isolates the cost of the mask structure itself from the cost
of losing the secret's content.

Tasks (secret must be irrelevant to the task, so degradation measures the
mask, not missing information): summarization of the public portion with an
unrelated secret span present; QA over public documents with a high-labeled
distractor document; agent-style tool-call emission from public instructions
with a high-labeled email in context. Metrics: task quality (exact match /
rubric score), mean per-token logprob of reference continuations, and
degradation deltas (b)−(c) and (d)−(a). Sweep secret-span size and position
(early/middle/late context) — attention-sink behavior makes early-position
masking the likely worst case; that sweep is the most informative plot.

Go/no-go (set thresholds before running; suggested):
- GO (inference-time shield): (b) within a small margin of (c) — the mask
  costs little beyond the information it removes — and (d)≈(a).
- CONDITIONAL (fine-tune path): meaningful degradation that a short
  masked-attention fine-tune (LoRA on mask-consistent data) substantially
  closes. The paper's story becomes "training recipe + shield."
- NO-GO for the current framing: degradation that fine-tuning doesn't
  close → re-scope (e.g., quarantine only for designated high-risk spans,
  or integrity-only deployment where masked regions are small).

## E3 — Integrity and session ports

Port DeclassifyDemo / PhasedSessionDemo / SessionDemo: schedule-fixed
summary and tool-call regions via constrained decoding phases, per-phase
masks (flows1/flows2), a tool adapter that receives ONLY the tool-call
region's token bytes. Assertions: strict mode — tool-call ids and tool
input bytes bit-identical under U substitution (same token length);
phased mode — identical when phase-1 summaries coincide, with the email-8
negative control (summary differs → tool call moves, though no phase-2
mask row touches U). Plus utility: tool-call validity rate under the
phase-2 mask (this is E2's question for the integrity plan, and the number
CaMeL-class comparisons will ask for).

## Reporting

Whatever E2 says, the writeup includes it. "Bit-exact airgap, at X% utility
cost, closable to Y% by fine-tuning" is a complete and honest result in
every branch; the field's documented blocker is exactly this number, and
publishing a bad number for the naive approach plus the fine-tune fix is
still the missing measurement.
