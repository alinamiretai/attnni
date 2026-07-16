import Attnni.Model
import Attnni.Gate
import Attnni.Lattice
import Attnni.Generation

/-!
# Attnni.Declassify — mixed-trust integrity across generation

The spec: "untrusted span U may influence the summary region but not the
tool-call region, within one generation." Two readings, two theorems:

1. **Strict** — the tool-call region never reads the summary. Then the spec is
   an INSTANCE of `lgen_noninterference` at a four-point lattice (`flows1`)
   observed at `tool`: unconditional, one mask, one schedule, one line of
   proof. U provably influences no tool-call token, ever.

2. **Only-through** — the tool call DOES consume the summary. This is
   intransitive noninterference: the policy wants U ⊑ S and S ⊑ C but NOT
   U ⊑ C, which no transitive relation can express, so it CANNOT be an
   instance of the lattice theorem. The resolution formalized here is
   designated-channel declassification as a PHASE-BOUNDARY POLICY SWAP:
   the label plan stays fixed for the whole generation (the repo's core
   invariant is never touched); what changes at the boundary between the
   summary phase and the tool phase is the mask and the flows relation —
   `flows1` (no S→C edge) for phase one, `flows2` (S→C open, U→S closed)
   for phase two. The theorem (`only_through_summary`) is CONDITIONAL on the
   channel content: if the two runs' generated summaries agree, the
   tool-call region is identical — i.e. the tool call is a function of
   (trusted content, tool-region initial state, summary CONTENT), and U
   reaches it only through what the summary says.

## What the conditional theorem does and does not say

It says: fix the summary, and U cannot move the tool call — every bit of
U-influence on the tool region is routed through the declassified channel,
where it can be audited, constrained, or bounded by other means. It does NOT
bound HOW MUCH of U the summary carries (the summary may quote U wholesale);
that is a quantitative question about the channel, deliberately separated
from the routing guarantee proved here.

## Scope (the repo's discipline)

Regions are SCHEDULE-FIXED: which slots are summary and which are tool-call
is set in advance — operationally, what constrained decoding enforces. A
content-dependent region boundary is the loop-level analogue of
`Dynamic.lean`'s implicit flows and needs a `LowSound`-style condition; it is
out of scope here, exactly as content-dependent schedules are out of scope in
`Generation.lean`. Generation-order constraints are NOT a resolution: U is in
the context from step zero, so ordering removes no edge — the tool region's
mask must exclude U regardless of when it is emitted.
-/

namespace Attnni

/-! ### The four-point trust policy -/

/-- Trust labels for the mixed-context integrity spec: trusted content
    (system prompt, user instructions), the untrusted span U (e.g. the
    email), the summary region S, and the tool-call region C. -/
inductive TrustLabel where
  | trusted | untrusted | summary | tool
  deriving DecidableEq, Repr

/-- **Phase-one policy** (summary generation): trusted flows anywhere; every
    label flows to itself; U flows into the summary region — and NOTHING
    flows into the tool region except trusted (and itself). In particular
    there is no S→C edge: under `flows1` the tool region is unconditionally
    protected. -/
def flows1 (a b : TrustLabel) : Prop :=
  a = .trusted ∨ a = b ∨ (a = .untrusted ∧ b = .summary)

/-- **Phase-two policy** (tool-call generation): the declassified channel.
    The S→C edge is OPEN — the tool region may read the summary — and the
    U→S edge is CLOSED (the summary region is frozen; nothing untrusted may
    keep flowing into it while the tool call is being emitted). -/
def flows2 (a b : TrustLabel) : Prop :=
  a = .trusted ∨ a = b ∨ (a = .summary ∧ b = .tool)

theorem flows1_trans : ∀ a b c, flows1 a b → flows1 b c → flows1 a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [flows1]

theorem flows2_trans : ∀ a b c, flows2 a b → flows2 b c → flows2 a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;> simp_all [flows2]

/-- Visibility at the tool observer, phase one: only trusted and tool-region
    content is visible — U and the summary are not. (This is why the
    phase-one theorem protects the tool region even while U pours into the
    summary.) -/
theorem flows1_to_tool (x : TrustLabel) :
    flows1 x .tool ↔ (x = .trusted ∨ x = .tool) := by
  cases x <;> simp [flows1]

/-- Visibility at the tool observer, phase two: trusted, summary, and tool —
    the summary is now inside the observer's window. Declassification is
    literally this one extra disjunct. -/
theorem flows2_to_tool (x : TrustLabel) :
    flows2 x .tool ↔ (x = .trusted ∨ x = .summary ∨ x = .tool) := by
  cases x <;> simp [flows2]

end Attnni

namespace Attnni

/-! ### Transport across a completed phase

The loop never touches labels, so both policy-side conditions — mask
well-formedness and the emission discipline — transport verbatim across a
completed phase, even when the phase was run with a DIFFERENT mask and a
different flows relation. This is the payoff of the fixed label plan: the
phase-two policy can be audited against the INITIAL context, before any
token is generated. -/

variable {L : Type}

/-- Well-maskedness of any mask under any flows relation survives a loop run
    with any (other) mask: it depends only on labels, which are invariant. -/
theorem lgenLoop_preserves_lWellMasked {flows : L → L → Prop}
    (mrun mchk : Mask) (fs : List Combine) (s : Schedule) {c : LContext L}
    (hwm : LWellMasked flows mchk c) :
    LWellMasked flows mchk (lgenLoop mrun fs s c) := by
  intro p q hq
  rw [lgenLoop_label, lgenLoop_label]
  exact hwm p q hq

/-- The emission discipline for a later schedule survives a loop run: same
    label-invariance argument. -/
theorem lgenLoop_preserves_emissionFlows {flows : L → L → Prop}
    (m : Mask) (fs : List Combine) (s s' : Schedule) {c : LContext L}
    (hem : EmissionFlows flows c s') :
    EmissionFlows flows (lgenLoop m fs s c) s' := by
  intro e he
  rw [lgenLoop_label, lgenLoop_label]
  exact hem e he

/-- Schedule composition: running the concatenated schedule is running the
    phases in sequence. With a single mask, the two-phase view and the
    one-generation view literally coincide — the phase boundary is a proof
    artifact, not an architectural one. -/
theorem lgenLoop_append (m : Mask) (fs : List Combine) (s₁ s₂ : Schedule)
    (c : LContext L) :
    lgenLoop m fs (s₁ ++ s₂) c = lgenLoop m fs s₂ (lgenLoop m fs s₁ c) := by
  unfold lgenLoop
  rw [List.foldl_append]

end Attnni

namespace Attnni

/-! ### The strict theorem — the free instance -/

/-- **Strict mixed-trust integrity.** If the tool region never reads the
    summary (no S→C edge — the mask satisfies `flows1` throughout), then U
    provably influences no tool-call token, UNCONDITIONALLY: any two runs
    agreeing on trusted and tool-region initial content — differing
    arbitrarily in U and in summary initial content — agree at every
    trusted- and tool-labeled position after the whole generation, for any
    weights. The summary region meanwhile may depend on U freely: that edge
    is inside the policy. One mask, one schedule (summary and tool emissions
    may interleave arbitrarily), one instantiation. -/
theorem strict_tool_noninterference (m : Mask) (fs : List Combine)
    (s : Schedule) {c₁ c₂ : LContext TrustLabel}
    (hwm : LWellMasked flows1 m c₁) (h : LEq flows1 .tool c₁ c₂)
    (hem : EmissionFlows flows1 c₁ s) :
    LEq flows1 .tool (lgenLoop m fs s c₁) (lgenLoop m fs s c₂) :=
  lgen_noninterference flows1_trans .tool m fs s hwm h hem

/-- Per-token form: each individual tool-labeled slot is U-independent. -/
theorem strict_tool_token (m : Mask) (fs : List Combine) (s : Schedule)
    {c₁ c₂ : LContext TrustLabel}
    (hwm : LWellMasked flows1 m c₁) (h : LEq flows1 .tool c₁ c₂)
    (hem : EmissionFlows flows1 c₁ s) (d : Pos)
    (hd : c₁.label d = .tool) :
    (lgenLoop m fs s c₁).value d = (lgenLoop m fs s c₂).value d := by
  refine (strict_tool_noninterference m fs s hwm h hem).2 d ?_
  rw [lgenLoop_label, hd]
  exact Or.inr (Or.inl rfl)

end Attnni

#print axioms Attnni.strict_tool_noninterference

namespace Attnni

/-! ### The only-through theorem — conditional declassification -/

/-- **Only-through-the-summary integrity.** Phase one generates the summary
    under `flows1` (U may write the summary; nothing reaches the tool
    region); phase two generates the tool call under `flows2` (the tool
    region may read the summary; U is sealed off). The label plan is FIXED
    across both phases; only mask and policy change at the boundary.

    Conclusion: if the two runs' generated summaries AGREE (`hchannel` — the
    declassification condition, stated on the phase-one outputs), then the
    tool-call region is identical across the two runs, however U varies.
    Equivalently: the tool call is a function of trusted content, tool-region
    initial state, and summary CONTENT — U reaches the tool call only through
    what the summary says. Dropping `hchannel` makes the statement FALSE
    (see `DeclassifyDemo.lean`): a run whose summary differs moves the tool
    call even though the tool region's mask never touches U. The hypothesis
    is the exact price of the S→C edge — this is intransitive
    noninterference, not expressible as any single-lattice instance. -/
theorem only_through_summary
    (m₁ m₂ : Mask) (fs : List Combine) (s₁ s₂ : Schedule)
    {c₁ c₂ : LContext TrustLabel}
    (hwm₁ : LWellMasked flows1 m₁ c₁)
    (hem₁ : EmissionFlows flows1 c₁ s₁)
    (hwm₂ : LWellMasked flows2 m₂ c₁)
    (hem₂ : EmissionFlows flows2 c₁ s₂)
    (h : LEq flows1 .tool c₁ c₂)
    (hchannel : ∀ p, c₁.label p = .summary →
        (lgenLoop m₁ fs s₁ c₁).value p = (lgenLoop m₁ fs s₁ c₂).value p) :
    LEq flows2 .tool (lgenLoop m₂ fs s₂ (lgenLoop m₁ fs s₁ c₁))
                     (lgenLoop m₂ fs s₂ (lgenLoop m₁ fs s₁ c₂)) := by
  -- Phase one, observed at tool under flows1: trusted- and tool-labeled
  -- positions agree after the summary is generated — U touched only the
  -- summary region.
  have h1 : LEq flows1 .tool (lgenLoop m₁ fs s₁ c₁) (lgenLoop m₁ fs s₁ c₂) :=
    lgen_noninterference flows1_trans .tool m₁ fs s₁ hwm₁ h hem₁
  obtain ⟨hlab, hval⟩ := h1
  -- The bridge: phase-one agreement (trusted, tool) plus the channel
  -- condition (summary) is exactly phase-two input equivalence at the tool
  -- observer (trusted, summary, tool) — declassification is this upgrade.
  have h2 : LEq flows2 .tool (lgenLoop m₁ fs s₁ c₁) (lgenLoop m₁ fs s₁ c₂) := by
    refine ⟨hlab, fun p hp => ?_⟩
    rw [lgenLoop_label] at hp
    rw [flows2_to_tool] at hp
    obtain hl | hl | hl := hp
    · exact hval p (by rw [lgenLoop_label, hl]; exact Or.inl rfl)
    · exact hchannel p hl
    · exact hval p (by rw [lgenLoop_label, hl]; exact Or.inr (Or.inl rfl))
  -- Phase two under flows2: policy-side hypotheses transport across phase
  -- one by label invariance, then the loop theorem closes it.
  exact lgen_noninterference flows2_trans .tool m₂ fs s₂
    (lgenLoop_preserves_lWellMasked m₁ m₂ fs s₁ hwm₂) h2
    (lgenLoop_preserves_emissionFlows m₁ fs s₁ s₂ hem₂)

/-- Per-token form: each individual tool-labeled slot is pinned by the
    summary content — fix the summary and no variation of U moves it. -/
theorem tool_token_only_through_summary
    (m₁ m₂ : Mask) (fs : List Combine) (s₁ s₂ : Schedule)
    {c₁ c₂ : LContext TrustLabel}
    (hwm₁ : LWellMasked flows1 m₁ c₁)
    (hem₁ : EmissionFlows flows1 c₁ s₁)
    (hwm₂ : LWellMasked flows2 m₂ c₁)
    (hem₂ : EmissionFlows flows2 c₁ s₂)
    (h : LEq flows1 .tool c₁ c₂)
    (hchannel : ∀ p, c₁.label p = .summary →
        (lgenLoop m₁ fs s₁ c₁).value p = (lgenLoop m₁ fs s₁ c₂).value p)
    (d : Pos) (hd : c₁.label d = .tool) :
    (lgenLoop m₂ fs s₂ (lgenLoop m₁ fs s₁ c₁)).value d
      = (lgenLoop m₂ fs s₂ (lgenLoop m₁ fs s₁ c₂)).value d := by
  refine (only_through_summary m₁ m₂ fs s₁ s₂
    hwm₁ hem₁ hwm₂ hem₂ h hchannel).2 d ?_
  rw [lgenLoop_label, lgenLoop_label, hd]
  exact Or.inr (Or.inl rfl)

end Attnni

#print axioms Attnni.only_through_summary
