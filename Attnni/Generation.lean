import Attnni.Model
import Attnni.Gate
import Attnni.Noninterference
import Attnni.Lattice

/-!
# Attnni.Generation — the autoregressive loop (confidentiality across generation)

`Noninterference.lean` proves the airgap for a *single* forward pass. Real
generation is a LOOP: run the stack, read a value at a source position, append
it to the context, run again. Emitted tokens re-enter the context — so a
per-pass theorem does not by itself bound whole-generation influence.

## The transitive-leak landmine (why this is not immediate)

If an emitted token could depend on the secret, it enters the context as a new
position, and later passes read it: the secret leaks one hop removed, through a
token that looks public. The loop theorem must close this laundering channel.
The confidentiality case closes it cleanly: the emitting position is itself
quarantined, so by the per-pass airgap its value is secret-independent; the
emitted token is therefore safe to re-enter the context; induction over steps
does the rest. Zero influence per pass composes to zero channel capacity across
the whole generation — there is nothing for a steganographic encoder to
modulate, because no emitted token carries any dependence on the secret.

## Modeling choices

* **Fixed label plan.** `Context` is total over `Pos := Nat`, so output slots
  exist before they are filled; we pre-assign their labels and never change
  them. This preserves the development's core invariant (layers and steps never
  touch labels), keeps `WellMasked` static across the loop — one Checker audit
  covers the whole generation — and makes the loop hypothesis a flat condition
  on the schedule rather than a per-step recursion.
* **Faithful emission.** One step runs the WHOLE stack and reads the run's
  value at the source: `genStep m fs (src, dst) c = writeAt c dst
  ((run m fs c).value src)`. The run's intermediate activations are discarded —
  the context carries only the token sequence, as in real decoding. (A one-hop
  readout is the instance `fs = [emit]`.)
* **Emission is a flow edge.** The new obligation the loop introduces is only
  this: each scheduled emission must respect the lattice — the destination
  slot's (pre-assigned) label dominates the source's. In the two-label case:
  tokens emitted into public slots come from public positions.

## Scope (stated exactly, as everywhere in AttnNI)

* **Fixed schedule, fixed length.** Which positions emit, where tokens land,
  and how many steps are all fixed in advance. A content-dependent schedule is
  an implicit flow — the loop-level analogue of `Dynamic.lean`'s mask
  generators — and a secret-dependent stopping time is a metadata channel,
  exactly as span-length is in the base development. Both belong to the
  integrity/declassification module, not this one.
* **Deterministic readout.** The emitted value is the run's value at the
  source (argmax folded into the last layer). Sampling under shared randomness
  (seed threaded as a public position) is the natural next lemma.
* **Confidentiality only.** "Secret masked from ALL emitted tokens." The
  mixed-trust integrity spec ("U may influence the summary region but not the
  tool-call region") requires declassification — `Declassify.lean`, next.
-/

namespace Attnni

/-! ### The generation step and loop -/

/-- Write value `v` at position `dst`; all other values and ALL labels
    unchanged. Labels are a fixed plan — output slots carry their labels before
    they are filled, which is what lets well-maskedness be checked once, ahead
    of generation. -/
def writeAt (c : Context) (dst : Pos) (v : Nat) : Context :=
  { value := fun p => if p = dst then v else c.value p
    label := c.label }

/-- One generation step: run the stack on the current context, read the value
    at `e.1` (the emitting position), write it at `e.2` (the next context
    slot). Only the emitted token persists. -/
def genStep (m : Mask) (fs : List Combine) (e : Pos × Pos) (c : Context) :
    Context :=
  writeAt c e.2 ((run m fs c).value e.1)

/-- A generation schedule: the (src, dst) pair for each step, fixed in
    advance. -/
abbrev Schedule := List (Pos × Pos)

/-- The autoregressive loop: fold generation steps over the schedule. -/
def genLoop (m : Mask) (fs : List Combine) (s : Schedule) (c : Context) :
    Context :=
  s.foldl (fun acc e => genStep m fs e acc) c

end Attnni

namespace Attnni

/-! ### Label invariance — the loop never touches labels -/

/-- `run` preserves labels — the two-label counterpart of `lrun_label`, needed
    to transport label facts into the run. -/
theorem run_label (m : Mask) (fs : List Combine) (c : Context) (p : Pos) :
    (run m fs c).label p = c.label p := by
  unfold run
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- A generation step preserves labels: `writeAt` touches only values. -/
theorem genStep_label (m : Mask) (fs : List Combine) (e : Pos × Pos)
    (c : Context) (p : Pos) :
    (genStep m fs e c).label p = c.label p := rfl

/-- The whole loop preserves labels. -/
theorem genLoop_label (m : Mask) (fs : List Combine) (s : Schedule)
    (c : Context) (p : Pos) :
    (genLoop m fs s c).label p = c.label p := by
  unfold genLoop
  induction s generalizing c with
  | nil => rfl
  | cons e s ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- Well-maskedness survives a generation step: it depends only on labels, and
    labels are invariant. The quarantine checked once (Checker.lean) covers
    every pass of the loop. -/
theorem genStep_preserves_wellMasked (m : Mask) (fs : List Combine)
    (e : Pos × Pos) {c : Context} (hwm : WellMasked m c) :
    WellMasked m (genStep m fs e c) := by
  intro p hp q hq
  simp only [genStep, writeAt] at hp ⊢
  exact hwm p hp q hq

end Attnni

namespace Attnni

/-! ### The two-label loop theorem -/

/-- **The generation-step lemma.** One loop iteration preserves low-equivalence,
    provided the emitting position is public. The heart: per-pass
    noninterference makes the run's value at the low source identical across
    the two runs, so the written token is identical; every other position is
    untouched. The emitted token is therefore itself secret-independent — safe
    to re-enter the context — which is exactly what the induction needs. -/
theorem genStep_preserves_lowEq (m : Mask) (fs : List Combine) (e : Pos × Pos)
    {c₁ c₂ : Context} (hwm : WellMasked m c₁) (h : LowEq c₁ c₂)
    (hsrc : c₁.label e.1 = .low) :
    LowEq (genStep m fs e c₁) (genStep m fs e c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [genStep, writeAt] at hp ⊢
  by_cases hpd : p = e.2
  · -- p is the destination slot: the written values are the run's values at
    -- the low source, identical across runs by the per-pass airgap.
    simp only [if_pos hpd]
    exact pub_noninterference m fs hwm ⟨hlab, hval⟩ e.1
      (by rw [run_label]; exact hsrc)
  · -- any other position is untouched by this step.
    simp only [if_neg hpd]
    exact hval p hp

/-- **Loop-level confidentiality noninterference.** Under a quarantine mask and
    a public-emission schedule, the whole autoregressive loop preserves
    low-equivalence: two contexts differing only in secret content generate
    IDENTICAL public context — every emitted token included — for any weights
    and any number of steps. "A secret S in the context provably influences no
    emitted token." -/
theorem gen_noninterference (m : Mask) (fs : List Combine) (s : Schedule)
    {c₁ c₂ : Context} (hwm : WellMasked m c₁) (h : LowEq c₁ c₂)
    (hpe : ∀ e ∈ s, c₁.label e.1 = .low) :
    LowEq (genLoop m fs s c₁) (genLoop m fs s c₂) := by
  unfold genLoop
  induction s generalizing c₁ c₂ with
  | nil => exact h
  | cons e s ih =>
    simp only [List.foldl_cons]
    refine ih (genStep_preserves_wellMasked m fs e hwm)
              (genStep_preserves_lowEq m fs e hwm h
                (hpe e List.mem_cons_self))
              (fun e' he' => ?_)
    -- the schedule condition survives the step: labels are invariant
    show (genStep m fs e c₁).label e'.1 = .low
    rw [genStep_label]
    exact hpe e' (List.mem_cons_of_mem e he')

/-- **The per-token corollary.** Each individual public slot — in particular,
    every emitted token — holds the same value across the two runs: flip the
    secret and every generated token stays exactly the same. -/
theorem emitted_token_noninterference (m : Mask) (fs : List Combine)
    (s : Schedule) {c₁ c₂ : Context} (hwm : WellMasked m c₁) (h : LowEq c₁ c₂)
    (hpe : ∀ e ∈ s, c₁.label e.1 = .low) (d : Pos)
    (hd : c₁.label d = .low) :
    (genLoop m fs s c₁).value d = (genLoop m fs s c₂).value d := by
  refine (gen_noninterference m fs s hwm h hpe).2 d ?_
  rw [genLoop_label]
  exact hd

end Attnni

#print axioms Attnni.gen_noninterference

/-!
## Multi-compartment generation

The lattice version. The emission discipline generalizes to: the emitted
token's label must dominate its source's — `flows (label src) (label dst)`.
Emission is thereby literally one more edge in the flow lattice, checked the
same way attention edges are. This is the label-propagation rule in its
declarative form. The two-label theorem is the instance at `flowsLH` with all
destination slots labeled low.
-/

namespace Attnni

variable {L : Type}

/-- Write at a position in a labeled context; labels unchanged. -/
def lwriteAt (c : LContext L) (dst : Pos) (v : Nat) : LContext L :=
  { value := fun p => if p = dst then v else c.value p
    label := c.label }

/-- One generation step over labeled contexts. -/
def lgenStep (m : Mask) (fs : List Combine) (e : Pos × Pos)
    (c : LContext L) : LContext L :=
  lwriteAt c e.2 ((lrun m fs c).value e.1)

/-- The loop over labeled contexts. -/
def lgenLoop (m : Mask) (fs : List Combine) (s : Schedule)
    (c : LContext L) : LContext L :=
  s.foldl (fun acc e => lgenStep m fs e acc) c

/-- **The emission discipline.** Every scheduled emission respects the lattice:
    the source's label flows into the destination's (pre-assigned) label.
    Emitted tokens are labeled at or above what they were computed from. -/
def EmissionFlows (flows : L → L → Prop) (c : LContext L) (s : Schedule) :
    Prop :=
  ∀ e ∈ s, flows (c.label e.1) (c.label e.2)

/-- Generation steps preserve labels. -/
theorem lgenStep_label (m : Mask) (fs : List Combine) (e : Pos × Pos)
    (c : LContext L) (p : Pos) :
    (lgenStep m fs e c).label p = c.label p := rfl

/-- The loop preserves labels. -/
theorem lgenLoop_label (m : Mask) (fs : List Combine) (s : Schedule)
    (c : LContext L) (p : Pos) :
    (lgenLoop m fs s c).label p = c.label p := by
  unfold lgenLoop
  induction s generalizing c with
  | nil => rfl
  | cons e s ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- Well-maskedness survives generation steps: labels are invariant. -/
theorem lgenStep_preserves_lWellMasked {flows : L → L → Prop}
    (m : Mask) (fs : List Combine) (e : Pos × Pos) {c : LContext L}
    (hwm : LWellMasked flows m c) :
    LWellMasked flows m (lgenStep m fs e c) := by
  intro p q hq
  simp only [lgenStep, lwriteAt] at *
  exact hwm p q hq

/-- **The generalized generation-step lemma.** One loop iteration preserves
    ℓ-equivalence for every observer ℓ, given the emission edge respects the
    lattice. The crux at the destination: if the destination is visible to ℓ,
    then by the emission discipline and transitivity the source is visible to
    ℓ, so the per-pass theorem makes the run's value there identical — for any
    weights. -/
theorem lgenStep_preserves_lEq {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (m : Mask) (fs : List Combine) (e : Pos × Pos)
    {c₁ c₂ : LContext L}
    (hwm : LWellMasked flows m c₁) (h : LEq flows ℓ c₁ c₂)
    (hem : flows (c₁.label e.1) (c₁.label e.2)) :
    LEq flows ℓ (lgenStep m fs e c₁) (lgenStep m fs e c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [lgenStep, lwriteAt] at hp ⊢
  by_cases hpd : p = e.2
  · simp only [if_pos hpd]
    -- destination visible to ℓ; emission edge + transitivity: source visible.
    have hsrcℓ : flows (c₁.label e.1) ℓ := by
      refine htrans _ _ _ hem ?_
      rw [hpd] at hp
      exact hp
    refine (lnoninterference htrans ℓ m fs hwm ⟨hlab, hval⟩).2 e.1 ?_
    rw [lrun_label]
    exact hsrcℓ
  · simp only [if_neg hpd]
    exact hval p hp

/-- **Multi-compartment generation noninterference.** For any transitive flows
    relation, any observer ℓ, a well-masked context, and a schedule whose every
    emission respects the lattice: the whole loop preserves ℓ-equivalence.
    Positions visible to ℓ — including every token emitted into an ℓ-visible
    slot — are identical across any two runs agreeing at ℓ-visible positions,
    for any weights, any number of steps, observed at every level
    simultaneously. -/
theorem lgen_noninterference {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (m : Mask) (fs : List Combine) (s : Schedule)
    {c₁ c₂ : LContext L}
    (hwm : LWellMasked flows m c₁) (h : LEq flows ℓ c₁ c₂)
    (hem : EmissionFlows flows c₁ s) :
    LEq flows ℓ (lgenLoop m fs s c₁) (lgenLoop m fs s c₂) := by
  unfold lgenLoop
  induction s generalizing c₁ c₂ with
  | nil => exact h
  | cons e s ih =>
    simp only [List.foldl_cons]
    refine ih (lgenStep_preserves_lWellMasked m fs e hwm)
              (lgenStep_preserves_lEq htrans ℓ m fs e hwm h
                (hem e List.mem_cons_self))
              (fun e' he' => ?_)
    show flows ((lgenStep m fs e c₁).label e'.1)
               ((lgenStep m fs e c₁).label e'.2)
    rw [lgenStep_label, lgenStep_label]
    exact hem e' (List.mem_cons_of_mem e he')

end Attnni

#print axioms Attnni.lgen_noninterference
