# AttnNI

**Machine-checked noninterference via attention masking.** *Part of the Admitto / LowEq line of work.*

Information moves between token positions in a transformer through exactly one
mechanism: attention. Everything else — MLPs, layernorms, residual connections —
is per-position. So masking an attention edge does not *reduce* information flow;
it **cuts the channel**: a masked edge carries zero information, not epsilon.

AttnNI proves, in Lean 4, that if some positions are masked out of another
position's attention, then that position's output is **identical regardless of the
masked content — for any weights**. It is an architectural airgap: the model can be
trained to leak with every parameter it has, and it still cannot, because the
channel is not there.

The development goes beyond a single theorem to a small **verified system**:
a general multi-compartment guarantee, a decidable enforcement checker proved sound
and complete, and a controller that provably only ever runs a compliant mask.

---

## What's proved

Everything below is machine-checked, `sorry`-free, on the trusted base
`[propext, Quot.sound]` (or `[propext]` for the two-label core).

### 1. Multi-compartment noninterference (the general theorem)

```lean
theorem lnoninterference {flows : L -> L -> Prop}
    (htrans : forall a b c, flows a b -> flows b c -> flows a c)
    (l : L) (m : Mask) (fs : List Combine) {c1 c2 : LContext L}
    (hwm : LWellMasked flows m c1) (h : LEq flows l c1 c2) :
    LEq flows l (lrun m fs c1) (lrun m fs c2)
```

For **any** label type `L` with a transitive `flows` relation (an information-flow
lattice), **any** observer level, and a well-masked context, running any stack
of layers preserves l-equivalence: positions visible to the observer compute
identical values across any two runs that agree at observer-visible positions. The
per-layer computations `fs` are universally quantified, so this holds **for any
weights**.

This is a general information-flow isolation framework — per-user compartments,
per-tool isolation, need-to-know hierarchies are all instances of one theorem,
observed at every level simultaneously.

### 2. The two-label airgap (the core, and a corollary of the general theorem)

```lean
theorem noninterference (m : Mask) (fs : List Combine) {c1 c2 : Context}
    (hwm : WellMasked m c1) (h : LowEq c1 c2) :
    LowEq (run m fs c1) (run m fs c2)
```

The two-point (public/secret) case: under a quarantine mask where public positions
attend only to public positions, public outputs are identical regardless of secret
content. `noninterference_via_lattice` proves this is exactly the instance of the
general theorem at the two-point lattice with observer `low` — so the framework
demonstrably subsumes the concrete airgap.

### 3. A decidable enforcement checker (sound and complete)

```lean
theorem wellMaskedCheck_correct (m : Mask) (c : Context) (ps : List Pos) :
    wellMaskedCheck m c ps = true <-> WellMaskedOn m c ps
```

`wellMaskedCheck` is a `Bool`-returning decision procedure that audits a finite set
of positions (a real context is finite); the theorem proves it returns `true`
exactly when the mask is well-formed there. Enforcement is decidable and verified.

### 4. A controller that only runs compliant masks

```lean
theorem controller_noninterference (m : Mask) (fs : List Combine)
    {c1 c2 : Context} (ps : List Pos) (fallback : Context)
    (hout : forall p, p notin ps -> c1.label p = .high)
    (hran : controller m fs c1 ps fallback != fallback)
    (h : LowEq c1 c2) :
    LowEq (run m fs c1) (run m fs c2)
```

The controller runs the model only if the mask passes the check, else returns a safe
fallback. This end-to-end theorem chains the whole system: *controller executed ->
check passed -> bounded well-masked -> (audit-window bridge) fully well-masked ->
noninterference holds for the executed run.* The system provably never executes an
unchecked mask, and every executed run satisfies the airgap guarantee.

---

## See it work

`Attnni/Demo.lean` builds a concrete 3-position context — positions 0,1 public,
position 2 secret — with a mask that lets the public output (position 0) attend only
to public positions, and a layer that sums attended values. Running it:

```
public output, secret = 42   ->  1
public output, secret = 999  ->  1     <- IDENTICAL: the secret cannot leak
secret position, secret = 42 ->  43
secret position, secret = 999->  1000  <- differs, as allowed
checker on good mask         ->  true
checker on bad mask          ->  false <- bad mask (public reads secret) rejected
controller with good mask    ->  1     <- ran
controller with bad mask     ->  0     <- fell back to safe default
```

Flip the secret from 42 to 999 and the public output stays exactly `1`, while the
secret position itself moves from 43 to 1000 — the computation depends on the secret
everywhere it is *allowed* to, and nowhere it is not. That is the theorem, made
visible once; the proof makes it "always."

---

## Why it works

The proof is one lemma and an induction.

- **`lstep_preserves_lEq` / `layerStep_preserves_lowEq`** — the heart. At a position
  `p` visible to the observer, the new value is `f p (values p is permitted to
  read)`. Well-maskedness says every position `p` reads flows to `p`'s level;
  transitivity carries that to the observer's level; low-equivalence says values at
  observer-visible positions agree across the two runs; so the read lists are equal,
  so the combining function `f` — whatever it is — returns the same output. The mask
  controls `f`'s inputs, and equal inputs force equal outputs, for any `f`.
- **Label preservation** — layers never change labels, so the quarantine structure
  is invariant across the stack.
- **`noninterference` / `lnoninterference`** — induction over the layer stack,
  threading both invariants down every layer.

## The model

AttnNI models a transformer's *information flow*, not its arithmetic — the key
abstraction, since noninterference is about which positions can influence which.

- **`Context` / `LContext L`** — for each position, a value and a security label.
- **`Mask`** — for each position, the positions it may attend to.
- **`Combine`** — the per-layer update, an *arbitrary* function from a position and
  the values it may read to a new value. Universal quantification over `Combine` is
  what makes the theorem hold for any weights.
- **`WellMasked` / `LWellMasked`** — the quarantine constraint (every position
  attends only to positions whose labels flow into its own).
- **`layerStep` / `run`** — one masked layer, and a fold over a stack of layers.

## Context

Architecture-level defenses that separate trusted from untrusted context are an
active area — CaMeL (DeepMind) runs a dual-LLM quarantine; spotlighting and
structured-prompt / placeholder-masking methods (e.g. recent "untrusted content
masking" for web agents) isolate untrusted spans; causal masking in every decoder is
already this construction applied to temporal order. These are enforced, deployed,
or by-design, but not machine-checked. Separately, the transformer-expressivity
literature (RASP/Tracr, masked hard-attention characterizations) studies how masking
constrains dataflow, but as an expressivity question, not a security theorem. AttnNI
establishes the underlying guarantee — noninterference through masked attention — as
a machine-checked security theorem over the transformer's dataflow, for any weights,
and packages it with a verified enforcement checker and controller.

## Scope and limitations

AttnNI states exactly what it guarantees.

- **Any weights, capability-independent.** The combining functions are universally
  quantified, so the guarantee holds regardless of what the model computes or how
  capable it is. It is a property of the dataflow graph, not the learned function.
- **Quarantine, not the whole system.** AttnNI proves the forward-pass airgap. It
  assumes positions are correctly labeled (a trusted runtime/tokenizer job), and it
  does not cover tool calls or post-generation actions — those need a policy gate
  (see LowEq). It does not address metadata channels (e.g. span lengths, or the fact
  that a mask was applied).
- **Decidable checking is finite.** The checker audits a finite position window; the
  audit-window bridge (`wellMaskedOn_to_wellMasked`) closes this to the full
  guarantee under the conservative assumption that positions outside the window are
  secret.
- **Abstract dataflow model.** The theorem is over an abstract layered-dataflow
  semantics (per-position updates + masked attention aggregation), not real tensor
  arithmetic. Correspondence to a concrete transformer (via RASP/Tracr) and
  extraction to a real inference stack are future work.
- **Boundary, not cognition.** AttnNI governs an information channel. It says nothing
  about the model's goals or internals, and channels outside the masked forward pass
  (including any human who can be persuaded) are out of scope — the irreducible limit
  of the approach.

## Building

```bash
lake build

# inspect the trusted base
#print axioms Attnni.lnoninterference              -- [propext, Quot.sound]
#print axioms Attnni.controller_noninterference    -- [propext, Quot.sound]

# run the demo
lake env lean Attnni/Demo.lean
```

## Files

- `Attnni/Model.lean` — abstract layered-dataflow semantics (positions, labels, masked layer step, run)
- `Attnni/Gate.lean` — the quarantine constraint (`WellMasked`) and low-equivalence
- `Attnni/Noninterference.lean` — the two-label layer-step lemma, induction, and airgap theorem
- `Attnni/Lattice.lean` — multi-compartment generalization and the subsumption corollary
- `Attnni/Checker.lean` — the decidable checker (sound + complete), the controller, and the end-to-end guarantee
- `Attnni/Demo.lean` — a concrete, runnable demonstration
