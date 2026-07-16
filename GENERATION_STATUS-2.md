# Generation.lean — status note (v2, schedule-based)

Loop-level confidentiality noninterference for AttnNI. Extends the single-pass
airgap (`Noninterference.lean`) across the autoregressive generation loop.

## Build state

`Generation.lean` elaborated on toolchain v4.31.0 with exactly two errors, both
the same signature drift: `List.mem_cons_self` is argument-free in this
toolchain (`a ∈ a :: l`, both implicit) — the draft applied it to `e s`. Fixed
at the two call sites (`gen_noninterference`, `lgen_noninterference`); the
`sorryAx` in the reported axiom sets was error-recovery fallout from those two
terms only. Everything else — both step lemmas, all label-invariance lemmas,
`run_label`, the lattice half — elaborated clean on the first build.
**Re-verify after rebuild: `#print axioms` should report `[propext,
Quot.sound]` for both headline theorems.**

`GenerationDemo.lean` was rewritten (it targeted the v1 frontier API); it now
matches the v2 schedule API, uses a fixed label plan with pre-labeled public
output slots, discharges all three theorem premises for the demo
(`gCtx_lowEq`, `gMaskSafe_wellMasked`, `gSchedule_public` by `decide`), and
exhibits the transitive leak with a sharper negative control: under the unsafe
mask, the THIRD emitted token diverges even though its own attention row never
touches the secret — laundering through the first token, invisible to any
per-row check.

## What is proved

- `gen_noninterference` (two-label) + `emitted_token_noninterference`
  (per-token corollary): under a quarantine mask and a public-source schedule,
  two low-equivalent contexts generate identical public context — every
  emitted token included — for any weights, any number of steps.
- `lgen_noninterference` (multi-compartment): for any transitive `flows`, any
  observer ℓ, well-masked context, and a schedule satisfying `EmissionFlows`
  (each emission's destination label dominates its source's), the loop
  preserves ℓ-equivalence at every observer level simultaneously.

One induction over the schedule per theorem, each resting on: label invariance
(`genStep_label` / `lgenStep_label`, `rfl` — the fixed label plan), quarantine
invariance (labels never change, so one Checker audit covers the whole
generation), and the step lemma (the emitted value is the run's value at a
source visible to the observer, identical across runs by the per-pass theorem).
The emitted token re-enters the context carrying a PROOF it is equal across
runs — that is what closes the transitive-laundering channel.

## Design (v2, stated exactly)

- **Fixed label plan.** `Context` is total over `Pos := Nat`; output slots
  pre-exist with pre-assigned labels that never change. Preserves the repo's
  core invariant, keeps `WellMasked` static across the loop.
- **Faithful emission.** `genStep m fs (src,dst) c = writeAt c dst
  ((run m fs c).value src)` — one step runs the WHOLE stack, keeps only the
  emitted token (as in real decoding; a one-hop readout is `fs = [emit]`).
- **Emission is a flow edge.** The loop's only new obligation: each scheduled
  emission respects the lattice — `flows (label src) (label dst)`
  (`EmissionFlows`). Two-label instance as stated: all sources public (`hpe`).

## Known slack (harmless, could tighten later)

The two-label hypothesis `hpe : ∀ e ∈ s, label e.1 = .low` is stronger than
the lattice-minimal condition (`flowsLH` gives `src = low ∨ dst = high`): it
forbids high→high emissions, which are harmless. Not wrong — just narrower
scope than `lgen_noninterference` at `flowsLH`. If wanted, derive the
two-label theorem as that instance via `toLContext` (mirroring
`noninterference_via_lattice`) instead of proving it directly.

## Scope / limitations (load-bearing — do not drop from the paper)

- **Fixed schedule, fixed length.** Content-dependent schedules are implicit
  flows (loop-level `LowSound` analogue); secret-dependent stopping time is a
  metadata channel. Both out of scope here.
- **Deterministic readout.** Sampling under shared randomness (seed as a
  public position) is the natural next lemma.
- **Confidentiality only.** The mixed-trust integrity spec needs
  declassification — `Declassify.lean`, next.
- **Abstract dataflow model.** Inherited from AttnNI; the proof-to-kernel
  correspondence is the separate serving-stack workstream.

## Next steps (in dependency order)

1. Rebuild; confirm sorry-free and `[propext, Quot.sound]` for
   `gen_noninterference`, `lgen_noninterference`, `demo_gen_noninterference`.
   (Note: build the demo with `lake build Attnni.GenerationDemo` — file must
   live at `Attnni/GenerationDemo.lean` to be picked up by the lib glob.)
2. Port the demo's `#eval` block to the PyTorch reference implementation:
   bit-identical emitted token ids under secret substitution, plus the
   negative control (unmasked run diverges at a token whose own attention row
   is clean — the laundering signature).
3. `Declassify.lean` — decide the resolution first: taint propagation vs.
   designated-channel declassification vs. generation-order constraints, and
   how the content-dependent region boundary interacts with `LowSound`.
4. Composition corollary with `CaMeLcore`.
