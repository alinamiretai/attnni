# AttnNI

**Machine-checked noninterference via attention masking.** *Part of the Admitto / LowEq line of work.*

Information moves between token positions in a transformer through exactly one
mechanism: attention. Everything else — MLPs, layernorms, residual connections —
is per-position. So masking an attention edge does not *reduce* information flow;
it **cuts the channel**: a masked edge carries zero information, not epsilon.

AttnNI proves, in Lean 4, that if secret positions are masked out of the public
stream's attention, then the public output is **identical regardless of secret
content — for any weights**. It is an architectural airgap: the model can be
trained to leak with every parameter it has, and it still cannot, because the
channel is not there.

## The theorem

```lean
theorem noninterference (m : Mask) (fs : List Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) :
    LowEq (run m fs c₁) (run m fs c₂)
```

Run any stack of layers `fs` under a well-formed quarantine mask `m`. Two contexts
that are **low-equivalent** — identical at every public position, differing only in
secret (high-labeled) content — stay low-equivalent. In particular
(`pub_noninterference`), every public position's output value is **identical**
across the two runs, so it carries **zero information** about the secrets:

```lean
theorem pub_noninterference (m : Mask) (fs : List Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) (p : Pos)
    (hp : (run m fs c₁).label p = .low) :
    (run m fs c₁).value p = (run m fs c₂).value p
```

The per-layer computations `fs` are **universally quantified** — a `List Combine`,
where each `Combine` is an arbitrary function. Proving noninterference for *all*
combining functions is proving it for *any weights*: the guarantee is a property of
the dataflow graph, not of the learned function. The airgap does not weaken as the
model grows more capable, because capability lives in the functions, and the
functions are quantified out.

**Trusted base:** `#print axioms Attnni.noninterference` → `[propext, Quot.sound]`.
No `Classical.choice`, no `sorry`, no `native_decide`.

## Why it works

The proof is one lemma and an induction.

- **`layerStep_preserves_lowEq`** — the heart. At a public position `p`, the new
  value is `f p (values p is permitted to read)`. Well-maskedness says every
  position `p` reads is public; low-equivalence says public values agree across the
  two runs; so the *list of values `p` reads* is identical in both runs; so the
  combining function `f` — whatever it is — returns the same output. The mask
  controls `f`'s inputs, and equal inputs force equal outputs, for any `f`.
- **`layerStep_preserves_wellMasked`** — labels never change, so the quarantine
  structure is invariant across layers.
- **`noninterference`** — induction over the layer stack, threading both
  invariants (well-maskedness stays true, low-equivalence is preserved) down every
  layer.

## The model

AttnNI models a transformer's *information flow*, not its arithmetic. This is the
key abstraction: noninterference is about which positions can influence which, so
concrete tensor computation is irrelevant and is abstracted away.

- **`Context`** — for each position, a value and a security label (`low` = public,
  `high` = secret).
- **`Mask`** — for each position, the set of positions it may attend to.
- **`Combine`** — the per-layer update, an *arbitrary* function from a position and
  the values it may read to a new value. Universal quantification over `Combine` is
  what makes the theorem hold for any weights.
- **`WellMasked`** — the quarantine constraint: every public position attends only
  to public positions.
- **`layerStep` / `run`** — one masked layer, and a fold over a stack of layers.

## Context

Architecture-level defenses that separate trusted from untrusted context are an
active area — CaMeL (DeepMind) runs a dual-LLM quarantine, and spotlighting /
structured-prompt methods isolate untrusted spans — but these are enforced or
heuristic, not proven. AttnNI establishes the underlying guarantee, noninterference
through masked attention, as a machine-checked theorem over the transformer's
dataflow, for any weights. It is the verified *quarantine* half of a safe agent
runtime; the policy half (gating tool calls and outputs) is LowEq / CaMeL
territory, and the two compose.

## Scope and limitations

AttnNI states exactly what it guarantees.

- **Any weights, capability-independent.** The combining functions are universally
  quantified, so the guarantee holds regardless of what the model computes or how
  capable it is.
- **Quarantine, not the whole system.** AttnNI proves the forward-pass airgap. It
  assumes positions are correctly labeled (a trusted runtime/tokenizer job), and it
  does not cover tool calls or post-generation actions — those need a policy gate
  (see LowEq). It also does not address metadata channels (e.g. the choice to mask,
  or span lengths).
- **Abstract dataflow model.** The theorem is over an abstract layered-dataflow
  semantics (per-position updates + masked attention aggregation), not real tensor
  arithmetic. Correspondence to a concrete transformer implementation, and
  extraction to a real inference stack, are future work.
- **Boundary, not cognition.** AttnNI governs an information channel. It says
  nothing about the model's goals or internals, and channels outside the masked
  forward pass (including any human who can be persuaded) are out of scope — the
  irreducible limit of the approach.

## Building

```bash
lake build

# inspect the trusted base
#print axioms Attnni.noninterference     -- [propext, Quot.sound]
```

## Files

- `Attnni/Model.lean` — abstract layered-dataflow semantics (positions, labels, masked layer step, run)
- `Attnni/Gate.lean` — the quarantine constraint (`WellMasked`) and low-equivalence
- `Attnni/Noninterference.lean` — the layer-step lemma, the induction, and the theorem
