import Attnni.Model
import Attnni.Lattice
import Attnni.Generation
import Attnni.Session
import Attnni.Declassify

/-!
# Attnni.PhasedSession — mixed-trust integrity across the agent loop

`Declassify.lean` proves the two mixed-trust theorems for phases made of
generation loops. `Session.lean` proves single-policy noninterference for
sessions — generations and tool executions interleaved. This file joins
them: the SAME two integrity theorems, with each phase now a full session.
The untrusted span may influence the summary; the tool-call region — AND
THE TOOLS EXECUTED FROM IT — are protected, strictly or conditionally on
the summary content.

Nothing new is invented here, which is the point: the phase-boundary policy
swap (`flows1` → `flows2`) commutes with everything `Session.lean` built,
because every policy obligation is stated on the fixed label plan and
labels survive whole sessions. The one new lemma is the session-level
transport of `StepOk`, a fold of the per-step transport.

The phase constraint from `Declassify.lean` carries over unchanged and is
still load-bearing: all summary-writing steps precede all phase-two steps.
Within phase two, tool-call emission and tool EXECUTION may interleave
freely — the tool clearance (`StepOk`, env case, under `flows2`) is what
keeps executed tools inside the policy.
-/

namespace Attnni

variable {L : Type}

/-- `StepOk` transports across a whole session: policy obligations depend
    only on labels, and no session touches labels — so phase two's policy is
    audited on the INITIAL context, before phase one runs. -/
theorem session_preserves_stepOk {flows : L → L → Prop}
    (steps : List SessionStep) (st' : SessionStep) {c : LContext L}
    (h : StepOk flows c st') :
    StepOk flows (session steps c) st' := by
  unfold session
  induction steps generalizing c with
  | nil => exact h
  | cons st rest ih =>
    simp only [List.foldl_cons]
    exact ih (sessStep_preserves_stepOk st st' h)

end Attnni

namespace Attnni

/-- **Strict mixed-trust integrity, across the agent loop.** One policy
    (`flows1`: no S→C edge), one session — generations and tool executions
    interleaved in any order. U provably influences no tool-labeled
    position: not the tool-call tokens, and not the OUTPUTS of any executed
    tool. Unconditional; the free instance of `session_noninterference`. -/
theorem session_strict_tool_noninterference
    (steps : List SessionStep) {c₁ c₂ : LContext TrustLabel}
    (hok : ∀ st ∈ steps, StepOk flows1 c₁ st)
    (h : LEq flows1 .tool c₁ c₂) :
    LEq flows1 .tool (session steps c₁) (session steps c₂) :=
  session_noninterference flows1_trans .tool steps hok h

/-- **Only-through-the-summary integrity, across the agent loop.** Phase one
    (any session under `flows1`) generates the summary — U may shape it, and
    tools cleared at or below the summary may run. Phase two (any session
    under `flows2`) emits the tool call FROM the summary and EXECUTES it. If
    the two runs' phase-one summaries agree, then every tool-labeled
    position after the whole agent turn — tool-call tokens and executed-tool
    outputs alike — is identical, however U varies: U reaches the tool
    execution only through what the summary says. Dropping the channel
    condition is false (`PhasedSessionDemo.lean`): a differing summary moves
    the executed tool's output even though no mask row and no tool read-list
    on the phase-two side ever touches U. -/
theorem session_only_through_summary
    (steps₁ steps₂ : List SessionStep) {c₁ c₂ : LContext TrustLabel}
    (hok₁ : ∀ st ∈ steps₁, StepOk flows1 c₁ st)
    (hok₂ : ∀ st ∈ steps₂, StepOk flows2 c₁ st)
    (h : LEq flows1 .tool c₁ c₂)
    (hchannel : ∀ p, c₁.label p = .summary →
        (session steps₁ c₁).value p = (session steps₁ c₂).value p) :
    LEq flows2 .tool (session steps₂ (session steps₁ c₁))
                     (session steps₂ (session steps₁ c₂)) := by
  -- Phase one at the tool observer under flows1: trusted- and tool-labeled
  -- positions agree — U touched only the summary region (and its own).
  have h1 : LEq flows1 .tool (session steps₁ c₁) (session steps₁ c₂) :=
    session_noninterference flows1_trans .tool steps₁ hok₁ h
  obtain ⟨hlab, hval⟩ := h1
  -- The bridge: phase-one agreement (trusted, tool) + the channel condition
  -- (summary) = phase-two input equivalence at the tool observer.
  have h2 : LEq flows2 .tool (session steps₁ c₁) (session steps₁ c₂) := by
    refine ⟨hlab, fun p hp => ?_⟩
    rw [session_label] at hp
    rw [flows2_to_tool] at hp
    obtain hl | hl | hl := hp
    · exact hval p (by rw [session_label, hl]; exact Or.inl rfl)
    · exact hchannel p hl
    · exact hval p (by rw [session_label, hl]; exact Or.inr (Or.inl rfl))
  -- Phase two: obligations transport across phase one by label invariance.
  exact session_noninterference flows2_trans .tool steps₂
    (fun st hst => session_preserves_stepOk steps₁ st (hok₂ st hst)) h2

/-- Per-position form: each individual tool-labeled slot — a tool-call token
    or an executed tool's result — is pinned by the summary content. -/
theorem session_tool_token_only_through_summary
    (steps₁ steps₂ : List SessionStep) {c₁ c₂ : LContext TrustLabel}
    (hok₁ : ∀ st ∈ steps₁, StepOk flows1 c₁ st)
    (hok₂ : ∀ st ∈ steps₂, StepOk flows2 c₁ st)
    (h : LEq flows1 .tool c₁ c₂)
    (hchannel : ∀ p, c₁.label p = .summary →
        (session steps₁ c₁).value p = (session steps₁ c₂).value p)
    (d : Pos) (hd : c₁.label d = .tool) :
    (session steps₂ (session steps₁ c₁)).value d
      = (session steps₂ (session steps₁ c₂)).value d := by
  refine (session_only_through_summary steps₁ steps₂
    hok₁ hok₂ h hchannel).2 d ?_
  rw [session_label, session_label, hd]
  exact Or.inr (Or.inl rfl)

end Attnni

#print axioms Attnni.session_strict_tool_noninterference
#print axioms Attnni.session_only_through_summary
