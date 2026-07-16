# AttnNI — the theorem stack

Machine-checked noninterference for transformer dataflow via attention
masking, from a single forward pass to the full agent loop. Every theorem is
sorry-free on trusted base `[propext, Quot.sound]` (verify: `lake build`
prints the axiom set per theorem). Every load-bearing hypothesis is paired
with an executable counterexample showing it is necessary, not decorative.

## The model (Model.lean, Lattice.lean)

Positions are `Nat`; a context assigns each position a value and a FIXED
security label. A layer updates every position from the values its mask row
permits it to read, through an arbitrary combining function. Nothing else is
modeled — the guarantees are about which inputs each computation receives,
never what it computes, so every theorem is universally quantified over
weights (`Combine`), and later over tool behaviors. The design invariant
carried through the whole stack: **labels never change** — every policy
obligation is stated on the initial label plan and audited once, before
anything runs (Checker.lean makes this decidable and proves the checker
correct).

## Spec 1 — Confidentiality: "a secret in the context provably influences no emitted token"

| Rung | Theorem | File |
|---|---|---|
| Single forward pass, two labels | `noninterference`, `pub_noninterference` | Noninterference.lean |
| Single pass, arbitrary lattice, every observer | `lnoninterference` | Lattice.lean |
| RASP surface language / real layer structure | `rasp_noninterference`, `rich_noninterference` | Rasp.lean, RaspRich.lean |
| Data-dependent masks (implicit flows) | `dyn_noninterference`, conditional on `LowSound` | Dynamic.lean |
| Autoregressive generation | `gen_noninterference`, `lgen_noninterference` | Generation.lean |
| Sampled decoding, shared randomness | `seeded_gen_noninterference` (∀-seed = distributional invariance) | Sampling.lean |
| **Agent session with tool execution** | `session_noninterference` | Session.lean |

The generation rung is where the transitive-laundering channel is closed:
emitted tokens re-enter the context carrying a proof they are equal across
runs, so the induction's invariant (full-context low-equivalence, not
per-token equality) covers every re-entry. The session rung extends the same
induction through the environment: a tool is a declared read-list plus an
opaque compute function (the same shape as a layer), its clearance condition
is syntactic and mirrors well-maskedness, and the theorem holds for any tool
behavior. Three edge types, one discipline: attention (mask), emission
(schedule), environment (tool reads) — each a lattice condition on the fixed
label plan.

Consequence for output filtering: under these hypotheses the mutual
information between the secret and the emitted token sequence is exactly
zero — there is nothing for a steganographic encoder to modulate on the
token-content channel. The residual channels are enumerated and are all
metadata-shaped (see Scope).

Counterexamples: LeakDemo.lean (secret-dependent mask = implicit flow);
GenerationDemo.lean (token laundered through re-entry: a slot whose own
attention row is clean diverges); SessionDemo.lean (secret laundered through
a TOOL EXECUTION whose read-list is clean).

## Spec 2 — Mixed-trust integrity: "U may influence the summary region but not the tool-call region"

Two readings, both proved; the fork is whether the tool-call region consumes
the summary.

**Strict** (no S→C edge): unconditional. An instance of the lattice theorem
at the four-point policy `flows1` — `strict_tool_noninterference`
(Declassify.lean, within one generation) and
`session_strict_tool_noninterference` (PhasedSession.lean, across the agent
loop, tools interleaved anywhere).

**Only-through** (tool call consumes the summary): this is intransitive
noninterference — the policy wants U⊑S and S⊑C but not U⊑C, which no
transitive relation expresses, so it cannot be a single-lattice instance.
Resolution: designated-channel declassification as a PHASE-BOUNDARY POLICY
SWAP. Labels stay fixed for the whole turn; at the boundary between the
summary phase and the tool phase, the mask and the flows relation change
(`flows1` → `flows2`: the S→C edge opens, the U→S edge closes). The theorem
is conditional on the channel content: **if the two runs' generated
summaries agree, the tool-call region — executed tool outputs included — is
identical however U varies.** Equivalently, the tool call is a function of
(trusted content, tool-region initial state, summary content): U reaches the
execution only through what the summary says. `only_through_summary`
(Declassify.lean, generation phases), `session_only_through_summary`
(PhasedSession.lean, session phases — the agent-loop form).

What the conditional theorem does NOT say: it does not bound how much of U
the summary carries. It is a routing guarantee — all U-influence on the tool
region passes through one auditable channel — and the quantitative question
about that channel is deliberately separated.

Load-bearing constraints of the only-through form (in the spec, not the
footnotes): (1) all summary-writing steps precede all phase-two steps —
opening S→C while U→S is open would let U pump content past the audited
channel; (2) regions are schedule-fixed (operationally: constrained
decoding) — a content-dependent region boundary is the loop-level analogue
of Dynamic.lean's implicit flows and needs a `LowSound`-style condition,
out of scope by the repo's standing discipline.

Counterexamples: DeclassifyDemo.lean and PhasedSessionDemo.lean — emails 7
and 999 differ but produce coinciding summaries (tool call and executed
result provably pinned); email 8 produces a different summary and moves the
executed tool's output even though no phase-two mask row or tool read-list
touches U: the intransitive laundering signature.

## Scope — residual channels (enumerated, all metadata-shaped)

- **Stopping time / variable length**: fixed step count assumed; a
  secret-dependent stopping time is a metadata channel.
- **Content-dependent schedules, masks, read-lists, region boundaries**:
  implicit flows; the conditional treatment is Dynamic.lean's `LowSound`
  pattern, formalized there for masks and deliberately not silently assumed
  elsewhere.
- **Secret-dependent randomness**: the seed must be a public position
  (shared, secret-independent); Sampling.lean names this hypothesis.
- **Below the abstraction**: timing, memory traffic, numerical effects of
  masking in the kernel. See "Interface obligations."

## Interface obligations (the trusted base, made explicit)

1. **Kernel correspondence**: the abstract mask corresponds to the serving
   stack — masked scores never enter the softmax reduction. This is the one
   informal step between these theorems and a deployed system; it is the
   separate serving-stack workstream, analogous to CaMeL trusting its
   interpreter, except the interpreter-side reasoning here is proved and
   only the kernel mapping is trusted.
2. **Tool feeding**: the adapter feeds each tool ONLY its declared spans
   (the read-list), never the raw context. Session.lean's guarantee is
   conditioned on exactly this, and nothing else, about the environment.
3. **Checker deployment**: masks/schedules/read-lists audited against the
   label plan before the turn runs (Checker.lean's controller pattern;
   one audit covers the whole turn because labels never change).

## Comparison point (CaMeL)

Same guarantee level (the agent loop), different mechanism and expressiveness:
per-token labels instead of per-model roles; one model, no quarantine twin,
no schema handoff — the influence separation happens inside the forward
pass, which is also why the confidentiality spec is inexpressible by any
boundary-level filter. Universally quantified weights and tools: no trust in
model or tool behavior, only in the three interface obligations above.
CaMeL's capability discipline reappears here as the tool read-list clearance
— proved rather than interpreted, once obligation (2) holds.

## Reference-implementation test plan

Each demo file ends with its port spec. The spine: bit-identical emitted
token ids (and tool input bytes, and tool outputs) under secret/untrusted
substitution on an open-weight model, with the corresponding negative
control (one corrupted attention row; a summary-content change) reproducing
the divergence signatures the demos exhibit.
