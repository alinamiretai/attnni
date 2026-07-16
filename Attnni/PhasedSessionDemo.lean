import Attnni.Model
import Attnni.Lattice
import Attnni.Generation
import Attnni.Session
import Attnni.Declassify
import Attnni.PhasedSession

/-!
# Attnni.PhasedSessionDemo — the pitch, end to end

One model reads the untrusted email, summarizes it, emits a tool call
informed by the summary, and the tool EXECUTES — one agent turn, per-token
influence separation, no quarantine twin. Layout (fixed label plan):

  position 0 : TRUSTED prompt (value 10)
  position 1 : UNTRUSTED email
  position 2 : SUMMARY slot
  position 3 : TOOL-CALL slot
  position 4 : TOOL-RESULT slot (also .tool — the tool's clearance)
  positions ≥ 5 : trusted padding

Phase one (`flows1`, mask `psMask₁`): generate the summary from the email.
Phase two (`flows2`, mask `psMask₂`): generate the tool call FROM the
summary, then execute the tool on the tool-call region.

The emitter is sum-mod-4, so emails 7 and 999 are genuinely different
untrusted inputs whose summaries coincide — and the theorem then PINS the
tool call and the executed tool's output:

  email 7   → summary 1 → tool call 3 → tool result 6  ┐ identical:
  email 999 → summary 1 → tool call 3 → tool result 6  ┘ the theorem.
  email 8   → summary 2 → tool call 0 → tool result 0  — channel condition
              fails, and U's influence reaches the EXECUTED TOOL — through
              the summary and nothing else: no phase-two mask row and no
              tool read-list ever touches position 1.
-/

namespace Attnni

/-- The fixed label plan: tool-call and tool-result slots both `.tool`. -/
def psLabel : Pos → TrustLabel
  | 0 => .trusted
  | 1 => .untrusted
  | 2 => .summary
  | 3 => .tool
  | 4 => .tool
  | _ => .trusted

/-- Phase-one mask: the summary row reads prompt + email + itself; tool rows
    read prompt + themselves only (nothing untrusted, nothing summary). -/
def psMask₁ : Mask := fun p =>
  if p = 2 then [0, 1, 2]
  else if p = 1 then [0, 1]
  else if p = 3 then [0, 3]
  else if p = 4 then [0, 4]
  else [0]

/-- Phase-two mask: the tool-call row now reads the SUMMARY (the
    declassified channel); the result row reads the tool-call region;
    U→S is closed (the summary row is frozen to trusted + itself). -/
def psMask₂ : Mask := fun p =>
  if p = 3 then [0, 2, 3]
  else if p = 2 then [0, 2]
  else if p = 1 then [0, 1]
  else if p = 4 then [0, 3, 4]
  else [0]

/-- The emitter: sum mod 4. -/
def psC : Combine := fun _ vs => (vs.foldl (· + ·) 0) % 4

/-- The tool: reads the tool-call slot (its declared span), doubles it,
    writes the result slot. Clearance: tool → tool. -/
def psTool : EnvCall :=
  { reads := [3], compute := fun vs => (vs.foldl (· + ·) 0) * 2, dst := 4 }

/-- Phase one: generate the summary. -/
def psSteps₁ : List SessionStep := [.gen psMask₁ [psC] [(2, 2)]]

/-- Phase two: generate the tool call from the summary, then EXECUTE it. -/
def psSteps₂ : List SessionStep :=
  [.gen psMask₂ [psC] [(3, 3)], .env psTool]

/-- The context, parameterized by the email. -/
def psCtx (email : Nat) : LContext TrustLabel :=
  { value := fun p => if p = 1 then email else if p = 0 then 10 else 0
    label := psLabel }

-- === Summaries coincide ⇒ tool call AND executed tool pinned ===
#eval (session psSteps₁ (psCtx 7)).value 2                          -- summary: 1
#eval (session psSteps₁ (psCtx 999)).value 2                        -- summary: 1
#eval (session psSteps₂ (session psSteps₁ (psCtx 7))).value 3       -- tool call: 3
#eval (session psSteps₂ (session psSteps₁ (psCtx 999))).value 3     -- tool call: 3 (SAME)
#eval (session psSteps₂ (session psSteps₁ (psCtx 7))).value 4       -- tool result: 6
#eval (session psSteps₂ (session psSteps₁ (psCtx 999))).value 4     -- tool result: 6 (SAME)

-- === Summary differs ⇒ U reaches the executed tool — through S only ===
#eval (session psSteps₁ (psCtx 8)).value 2                          -- summary: 2 (differs)
#eval (session psSteps₂ (session psSteps₁ (psCtx 8))).value 3       -- tool call: 0 (moved)
#eval (session psSteps₂ (session psSteps₁ (psCtx 8))).value 4       -- tool result: 0 (moved)

end Attnni

namespace Attnni

/-! ### Discharging the premises -/

/-- Phase-one mask satisfies `flows1` at every row. -/
theorem psMask₁_wellMasked (email : Nat) :
    LWellMasked flows1 psMask₁ (psCtx email) := by
  intro p q hq
  by_cases h2 : p = 2
  · subst h2
    have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by simpa [psMask₁] using hq
    obtain h | h | h := hq' <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · by_cases h1 : p = 1
    · subst h1
      have hq' : q = 0 ∨ q = 1 := by simpa [psMask₁, h2] using hq
      obtain h | h := hq' <;> subst h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases h3 : p = 3
      · subst h3
        have hq' : q = 0 ∨ q = 3 := by simpa [psMask₁, h2, h1] using hq
        obtain h | h := hq' <;> subst h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · by_cases h4 : p = 4
        · subst h4
          have hq' : q = 0 ∨ q = 4 := by simpa [psMask₁, h2, h1, h3] using hq
          obtain h | h := hq' <;> subst h
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · have hq' : q = 0 := by simpa [psMask₁, h2, h1, h3, h4] using hq
          subst hq'
          exact Or.inl rfl

/-- Phase-two mask satisfies `flows2` at every row. -/
theorem psMask₂_wellMasked (email : Nat) :
    LWellMasked flows2 psMask₂ (psCtx email) := by
  intro p q hq
  by_cases h3 : p = 3
  · subst h3
    have hq' : q = 0 ∨ q = 2 ∨ q = 3 := by simpa [psMask₂] using hq
    obtain h | h | h := hq' <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · by_cases h2 : p = 2
    · subst h2
      have hq' : q = 0 ∨ q = 2 := by simpa [psMask₂, h3] using hq
      obtain h | h := hq' <;> subst h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases h1 : p = 1
      · subst h1
        have hq' : q = 0 ∨ q = 1 := by simpa [psMask₂, h3, h2] using hq
        obtain h | h := hq' <;> subst h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · by_cases h4 : p = 4
        · subst h4
          have hq' : q = 0 ∨ q = 3 ∨ q = 4 := by simpa [psMask₂, h3, h2, h1] using hq
          obtain h | h | h := hq' <;> subst h
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inl rfl)
        · have hq' : q = 0 := by simpa [psMask₂, h3, h2, h1, h4] using hq
          subst hq'
          exact Or.inl rfl

/-- The summary emission respects `flows1` (S→S). -/
theorem psEmission₁ (email : Nat) :
    EmissionFlows flows1 (psCtx email) [(2, 2)] := by
  intro e he
  have h : e = (2, 2) := by simpa using he
  subst h
  exact Or.inr (Or.inl rfl)

/-- The tool-call emission respects `flows2` (C→C). -/
theorem psEmission₂ (email : Nat) :
    EmissionFlows flows2 (psCtx email) [(3, 3)] := by
  intro e he
  have h : e = (3, 3) := by simpa using he
  subst h
  exact Or.inr (Or.inl rfl)

/-- The tool respects its clearance under `flows2`: its one declared read
    (the tool-call slot, `.tool`) flows into its result slot (`.tool`). -/
theorem psTool_ok (email : Nat) :
    ∀ q ∈ psTool.reads,
      flows2 ((psCtx email).label q) ((psCtx email).label psTool.dst) := by
  intro q hq
  have h : q = 3 := by simpa [psTool] using hq
  subst h
  exact Or.inr (Or.inl rfl)

/-- Phase one's obligations. -/
theorem psSteps₁_ok (email : Nat) :
    ∀ st ∈ psSteps₁, StepOk flows1 (psCtx email) st := by
  intro st hst
  have h : st = SessionStep.gen psMask₁ [psC] [(2, 2)] := by
    simpa [psSteps₁] using hst
  subst h
  exact ⟨psMask₁_wellMasked email, psEmission₁ email⟩

/-- Phase two's obligations. -/
theorem psSteps₂_ok (email : Nat) :
    ∀ st ∈ psSteps₂, StepOk flows2 (psCtx email) st := by
  intro st hst
  have h : st = SessionStep.gen psMask₂ [psC] [(3, 3)]
         ∨ st = SessionStep.env psTool := by
    simpa [psSteps₂] using hst
  obtain h | h := h <;> subst h
  · exact ⟨psMask₂_wellMasked email, psEmission₂ email⟩
  · exact psTool_ok email

/-- Input equivalence at the tool observer: any two emails agree at every
    trusted- and tool-labeled position. -/
theorem psCtx_lEq (a b : Nat) : LEq flows1 .tool (psCtx a) (psCtx b) := by
  refine ⟨fun p => rfl, fun p hp => ?_⟩
  have hp1 : p ≠ 1 := by
    intro hpe
    subst hpe
    rw [flows1_to_tool] at hp
    have hlab : (psCtx a).label 1 = .untrusted := rfl
    rw [hlab] at hp
    obtain h | h := hp <;> exact absurd h (by decide)
  show (if p = 1 then a else if p = 0 then 10 else 0)
     = (if p = 1 then b else if p = 0 then 10 else 0)
  rw [if_neg hp1, if_neg hp1]

/-- Only position 2 carries the summary label. -/
theorem psLabel_summary (p : Pos) (hp : psLabel p = .summary) : p = 2 :=
  match p, hp with
  | 2, _ => rfl
  | 0, h => nomatch h
  | 1, h => nomatch h
  | 3, h => nomatch h
  | 4, h => nomatch h
  | (_ + 5), h => nomatch h

/-- The channel condition, by computation: emails 7 and 999 generate the
    same summary. -/
theorem ps_channel :
    ∀ p, (psCtx 7).label p = .summary →
      (session psSteps₁ (psCtx 7)).value p
        = (session psSteps₁ (psCtx 999)).value p := by
  intro p hp
  have h2 : p = 2 := psLabel_summary p hp
  subst h2
  decide

/-- **The pitch, as a theorem.** One model, one agent turn: it read the
    untrusted email, summarized it, emitted a tool call from the summary,
    and executed the tool — and the tool-labeled region, executed tool
    output included, is provably identical across the two emails, because
    their summaries coincide. U reached the execution only through the
    summary content. -/
theorem demo_phased_session :
    LEq flows2 .tool
      (session psSteps₂ (session psSteps₁ (psCtx 7)))
      (session psSteps₂ (session psSteps₁ (psCtx 999))) :=
  session_only_through_summary psSteps₁ psSteps₂
    (psSteps₁_ok 7) (psSteps₂_ok 7) (psCtx_lEq 7 999) ps_channel

/-- The executed tool's output, pinned. -/
theorem demo_tool_result_pinned :
    (session psSteps₂ (session psSteps₁ (psCtx 7))).value 4
      = (session psSteps₂ (session psSteps₁ (psCtx 999))).value 4 :=
  session_tool_token_only_through_summary psSteps₁ psSteps₂
    (psSteps₁_ok 7) (psSteps₂_ok 7) (psCtx_lEq 7 999) ps_channel 4 rfl

end Attnni

#print axioms Attnni.demo_phased_session
