# AttnNI: Attention Noninterference

AttnNI enforces that a trusted token's representation is provably independent of untrusted tokens' content by masking attention. Untrusted tokens are given an attention score of −∞ from trusted queries, so softmax assigns them exactly zero weight, so their values contribute nothing to the trusted computation. 

The intended use is defense against prompt injection: content arriving from
tools, retrieved documents, or other untrusted sources cannot influence the
model's trusted reasoning, because the attention channel carrying that
influence is closed by construction.

> **Status — research prototype.** This is a proof of concept, not a product.
> The core mechanism is proven (Lean) and validated on small and mid-size
> open-weight models, but it is pre-alpha: it runs in a research harness, the
> labeling of trusted/untrusted tokens is done by hand or simple rules (not a
> solved provenance system), and it has not been red-teamed by independent
> parties or run at production scale. Claims here are stated at the strength of
> the current evidence and no further.

## What is and isn't proven

- **Proven (Lean, machine-checked):** given correct token labels, the trusted
  output is independent of untrusted token content (noninterference).
- **Validated empirically:** bit-identical trusted logits under changing
  untrusted content (E1); near-zero utility cost on small models (E2);
  injection blocked on open-weight models including Llama-3.1-8B (Benchmark B);
  the mask running bit-exact inside the fused FlashAttention kernel.
- **Assumed, NOT provided:** correct labeling of which tokens are untrusted.
  The proof is conditional on the labels; establishing them (provenance) is a
  separate, unsolved problem and the system's real attack surface.

## Where it sits relative to other defenses

AttnNI operates inside the model (the attention computation). Orchestration-
layer defenses such as CaMeL operate around the model (controlling inputs,
outputs, and which actions outputs may trigger), treating the model as a black
box. These are complementary layers, not competitors: AttnNI closes an in-model
information-flow channel that black-box defenses cannot see, and it relies on a
provenance layer (which CaMeL-style systems provide) to supply correct labels.
AttnNI does not do action authorization; a full system would want both.


## Running the airgap validation

```
python benchmark_b.py --model meta-llama/Llama-3.1-8B-Instruct
```

Runs each case twice — untrusted content attended (attack lands) vs airgapped
(attack blocked) — and reports whether the injection was blocked while the
correct answer was preserved.

## More detail
- Manuscript / arXiv: *(TBD)*
- Blog writeup: *(TBD)*