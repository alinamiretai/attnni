import Attnni.Model
import Attnni.Gate
import Attnni.Lattice
import Attnni.Generation

/-!
# Attnni.Session — the agent loop (noninterference across tool calls)

`Generation.lean` proves the airgap across one autoregressive generation. An
AGENT interleaves generations with TOOL EXECUTIONS: the model emits a tool
call, the environment runs it, the result re-enters the context, and the
model generates again. Tool results re-enter exactly the way emitted tokens
do — so the laundering channel now runs THROUGH the environment: a secret
could influence a tool's input, the tool's output re-enters as an innocuous-
looking value, and later generations read it. The session theorem closes
this channel.

## Tools as masked reads (the design decision)

A tool is modeled the way a layer is: a DECLARED read-set plus an opaque
compute function — `compute (reads.map c.value)`. The clearance condition
(`StepOk`, env case) is syntactic, checkable, and shaped exactly like
`LWellMasked`: every declared read's label flows into the destination
slot's (pre-assigned) label. Nothing is assumed about what the tool
computes: the theorem holds for ANY tool behavior, because the guarantee is
about which inputs the tool receives — the same universal quantification
the repo applies to weights, extended to the environment.

This is the trusted base made explicit: the serving stack must enforce that
a tool is fed only its declared spans (the tool-call region, not the raw
context). That enforcement is the interface obligation; everything after it
is proved.

## The three edge types, one discipline

Every inter-position channel in an agent session is now one of three edges,
each with a lattice condition stated on the FIXED label plan and auditable
once, before the session runs:
  attention  — mask       : `LWellMasked`
  emission   — schedule   : `EmissionFlows`
  environment — tool reads: `StepOk` (env case)

## Scope

One flows policy per session. Phased policies (the `Declassify.lean`
mechanism, where the lattice changes at a schedule boundary) compose with
sessions by chaining the phase argument manually; folding phase-indexed
policies into the session step type is the planned generalization. Read
sets, schedules, and the step list are fixed in advance — content-dependent
versions of any of them are implicit flows (`Dynamic.lean`'s territory).
Each env call writes one slot; a tool returning a span is a list of env
calls (or a follow-on with a region write).
-/

namespace Attnni

/-! ### Sessions -/

/-- A tool invocation: a declared read-set, an opaque compute function, and
    the destination slot for the result. The compute function is arbitrary —
    the guarantee never inspects it. -/
structure EnvCall where
  reads : List Pos
  compute : List Nat → Nat
  dst : Pos

/-- One session step: a generation phase (mask, layer stack, emission
    schedule) or a tool execution. Label-agnostic — the same step list runs
    over any label plan. -/
inductive SessionStep where
  | gen (m : Mask) (fs : List Combine) (s : Schedule)
  | env (e : EnvCall)

variable {L : Type}

/-- Execute one session step. A tool execution writes the compute function's
    output on the declared reads into the destination slot; labels are never
    touched (the fixed label plan spans the whole session). -/
def sessStep (st : SessionStep) (c : LContext L) : LContext L :=
  match st with
  | .gen m fs s => lgenLoop m fs s c
  | .env e => lwriteAt c e.dst (e.compute (e.reads.map c.value))

/-- A session: fold steps over the context. -/
def session (steps : List SessionStep) (c : LContext L) : LContext L :=
  steps.foldl (fun acc st => sessStep st acc) c

/-- Per-step policy obligation, stated on the (fixed) label plan:
    a generation phase must be well-masked with a lattice-respecting
    schedule; a tool execution must read only positions whose labels flow
    into its destination slot's label — the tool's clearance. -/
def StepOk (flows : L → L → Prop) (c : LContext L) : SessionStep → Prop
  | .gen m _fs s => LWellMasked flows m c ∧ EmissionFlows flows c s
  | .env e => ∀ q ∈ e.reads, flows (c.label q) (c.label e.dst)

end Attnni

namespace Attnni

/-! ### Label invariance and transport -/

variable {L : Type}

/-- No session step touches labels. -/
theorem sessStep_label (st : SessionStep) (c : LContext L) (p : Pos) :
    (sessStep st c).label p = c.label p := by
  cases st with
  | gen m fs s => exact lgenLoop_label m fs s c p
  | env e => rfl

/-- No session touches labels. -/
theorem session_label (steps : List SessionStep) (c : LContext L) (p : Pos) :
    (session steps c).label p = c.label p := by
  unfold session
  induction steps generalizing c with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact sessStep_label st c p

/-- Every step obligation survives every step: the obligations depend only
    on labels, and labels are invariant — so the whole session's policy is
    audited once, on the initial context. -/
theorem sessStep_preserves_stepOk {flows : L → L → Prop}
    (st st' : SessionStep) {c : LContext L} (h : StepOk flows c st') :
    StepOk flows (sessStep st c) st' := by
  cases st' with
  | gen m fs s =>
    obtain ⟨hwm, hem⟩ := h
    refine ⟨fun p q hq => ?_, fun e' he' => ?_⟩
    · rw [sessStep_label, sessStep_label]
      exact hwm p q hq
    · rw [sessStep_label, sessStep_label]
      exact hem e' he'
  | env e =>
    intro q hq
    rw [sessStep_label, sessStep_label]
    exact h q hq

end Attnni

namespace Attnni

/-! ### The session theorem -/

variable {L : Type}

/-- **The session-step lemma.** One step — generation phase or tool
    execution — preserves ℓ-equivalence, given its policy obligation. The
    gen case is the loop theorem. The env case is the layer-step argument
    replayed at the environment: if the destination slot is visible to ℓ,
    every declared read's label flows into the slot's label (clearance) and
    hence into ℓ (transitivity), so the read values agree, so the tool —
    whatever it computes — receives identical inputs and writes identical
    output. -/
theorem sessStep_preserves_lEq {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (st : SessionStep) {c₁ c₂ : LContext L}
    (hok : StepOk flows c₁ st) (h : LEq flows ℓ c₁ c₂) :
    LEq flows ℓ (sessStep st c₁) (sessStep st c₂) := by
  cases st with
  | gen m fs s =>
    obtain ⟨hwm, hem⟩ := hok
    exact lgen_noninterference htrans ℓ m fs s hwm h hem
  | env e =>
    obtain ⟨hlab, hval⟩ := h
    refine ⟨fun p => hlab p, fun p hp => ?_⟩
    show (if p = e.dst then e.compute (e.reads.map c₁.value) else c₁.value p)
       = (if p = e.dst then e.compute (e.reads.map c₂.value) else c₂.value p)
    by_cases hpd : p = e.dst
    · rw [if_pos hpd, if_pos hpd]
      rw [hpd] at hp
      have hlists : e.reads.map c₁.value = e.reads.map c₂.value := by
        apply List.map_congr_left
        intro q hq
        exact hval q (htrans _ _ _ (hok q hq) hp)
      rw [hlists]
    · rw [if_neg hpd, if_neg hpd]
      exact hval p hp

/-- **Agent-session noninterference.** For any transitive flows relation,
    any observer ℓ, and any session whose every step satisfies its policy
    obligation on the initial label plan: the whole session — generations
    and tool executions interleaved, any weights, ANY tool behaviors —
    preserves ℓ-equivalence. A secret invisible to ℓ influences no
    ℓ-visible position, no emitted token, and no tool result, across the
    entire agent loop. This is the system-level guarantee: the laundering
    channel through the environment is closed by the same induction that
    closed it through the context. -/
theorem session_noninterference {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (steps : List SessionStep) {c₁ c₂ : LContext L}
    (hok : ∀ st ∈ steps, StepOk flows c₁ st) (h : LEq flows ℓ c₁ c₂) :
    LEq flows ℓ (session steps c₁) (session steps c₂) := by
  unfold session
  induction steps generalizing c₁ c₂ with
  | nil => exact h
  | cons st rest ih =>
    simp only [List.foldl_cons]
    refine ih (fun st' hst' => sessStep_preserves_stepOk st st'
                 (hok st' (List.mem_cons_of_mem st hst')))
              (sessStep_preserves_lEq htrans ℓ st (hok st List.mem_cons_self) h)

/-- Per-position form: any single ℓ-visible slot — emitted token or tool
    result — holds the same value across the two runs after the whole
    session. -/
theorem session_token_noninterference {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (steps : List SessionStep) {c₁ c₂ : LContext L}
    (hok : ∀ st ∈ steps, StepOk flows c₁ st) (h : LEq flows ℓ c₁ c₂)
    (d : Pos) (hd : flows (c₁.label d) ℓ) :
    (session steps c₁).value d = (session steps c₂).value d := by
  refine (session_noninterference htrans ℓ steps hok h).2 d ?_
  rw [session_label]
  exact hd

end Attnni

#print axioms Attnni.session_noninterference
