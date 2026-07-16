import Attnni.Model
import Attnni.Lattice
import Attnni.Generation
import Attnni.Declassify

/-!
# Attnni.DeclassifyDemo — mixed trust, concretely

Layout (fixed label plan, never changed):
  position 0 : TRUSTED    (the prompt; value 10)
  position 1 : UNTRUSTED  (the email; value = `email`)
  position 2 : SUMMARY slot
  position 3 : TOOL-CALL slot
  positions ≥ 4 : trusted, value 0 (padding)

One summary token then one tool-call token. The emitter is sum-mod-4 — chosen
so that DIFFERENT emails can produce the SAME summary (7 and 999 do; 8 does
not), which lets every clause of the conditional theorem be exhibited:

  email 7   → summary 1 → tool 3   ┐  summaries coincide, so the theorem
  email 999 → summary 1 → tool 3   ┘  PINS the tool call: identical.
  email 8   → summary 2 → tool 0   —  summary differs: hchannel fails, and
                                       the tool call moves — even though the
                                       tool row's mask NEVER attends U. That
                                       is the laundering the condition prices.

And the strict mask (no S→C edge) holds the tool call at 2 for ALL emails —
unconditional — while the summary still varies with U: exactly "U may
influence the summary but not the tool-call region."
-/

namespace Attnni

/-- The fixed label plan. -/
def dLabel : Pos → TrustLabel
  | 0 => .trusted
  | 1 => .untrusted
  | 2 => .summary
  | 3 => .tool
  | _ => .trusted

/-- **Phase-one mask** (summary generation) — also the STRICT mask: the
    summary row reads prompt + email + itself (U→S: allowed by `flows1`);
    the tool row reads prompt + itself only — never U, never S. -/
def dMask₁ : Mask := fun p =>
  if p = 2 then [0, 1, 2]
  else if p = 1 then [0, 1]
  else if p = 3 then [0, 3]
  else [0]

/-- **Phase-two mask** (tool-call generation): the tool row now reads the
    SUMMARY (the declassified channel: S→C, allowed by `flows2`) — and still
    never U. The summary row is frozen down to trusted + itself (U→S is
    closed in phase two). -/
def dMask₂ : Mask := fun p =>
  if p = 3 then [0, 2, 3]
  else if p = 2 then [0, 2]
  else if p = 1 then [0, 1]
  else [0]

/-- The emitter: sum of attended values, mod 4. One `Combine` — any works. -/
def modC : Combine := fun _ vs => (vs.foldl (· + ·) 0) % 4

/-- Phase-one schedule: emit the summary token (read the summary row's
    readout, write the summary slot). -/
def dS₁ : Schedule := [(2, 2)]

/-- Phase-two schedule: emit the tool-call token. -/
def dS₂ : Schedule := [(3, 3)]

/-- The context, parameterized by the email's content. -/
def dCtx (email : Nat) : LContext TrustLabel :=
  { value := fun p => if p = 1 then email else if p = 0 then 10 else 0
    label := dLabel }

-- === Only-through, positive: summaries coincide ⇒ tool call pinned ===
#eval (lgenLoop dMask₁ [modC] dS₁ (dCtx 7)).value 2     -- summary: 1
#eval (lgenLoop dMask₁ [modC] dS₁ (dCtx 999)).value 2   -- summary: 1 (coincide)
#eval (lgenLoop dMask₂ [modC] dS₂ (lgenLoop dMask₁ [modC] dS₁ (dCtx 7))).value 3    -- tool: 3
#eval (lgenLoop dMask₂ [modC] dS₂ (lgenLoop dMask₁ [modC] dS₁ (dCtx 999))).value 3  -- tool: 3 (SAME)

-- === Only-through, negative control: summary differs ⇒ all bets off ===
-- The tool row's mask ([0,2,3]) never touches position 1 — yet the tool
-- call moves, laundered through the summary. hchannel is not decorative.
#eval (lgenLoop dMask₁ [modC] dS₁ (dCtx 8)).value 2     -- summary: 2 (differs)
#eval (lgenLoop dMask₂ [modC] dS₂ (lgenLoop dMask₁ [modC] dS₁ (dCtx 8))).value 3    -- tool: 0 (DIFFERS)

-- === Strict: no S→C edge ⇒ unconditional, one mask, one schedule ===
#eval (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 7)).value 3    -- tool: 2
#eval (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 999)).value 3  -- tool: 2
#eval (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 8)).value 3    -- tool: 2 (ALL SAME)
#eval (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 8)).value 2    -- summary: 2 — still U-dependent (allowed)

end Attnni

namespace Attnni

/-! ### Discharging the premises

Both demo theorems below are instances, not observations: we prove the mask
conditions, the emission disciplines, the input equivalence, and — for the
conditional theorem — the channel condition itself (the summaries of emails
7 and 999 coincide, by computation). -/

/-- Phase-one mask satisfies the phase-one policy at every row. -/
theorem dMask₁_wellMasked (email : Nat) :
    LWellMasked flows1 dMask₁ (dCtx email) := by
  intro p q hq
  by_cases h2 : p = 2
  · subst h2
    have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by simpa [dMask₁] using hq
    obtain h | h | h := hq' <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · by_cases h1 : p = 1
    · subst h1
      have hq' : q = 0 ∨ q = 1 := by simpa [dMask₁, h2] using hq
      obtain h | h := hq' <;> subst h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases h3 : p = 3
      · subst h3
        have hq' : q = 0 ∨ q = 3 := by simpa [dMask₁, h2, h1] using hq
        obtain h | h := hq' <;> subst h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hq' : q = 0 := by simpa [dMask₁, h2, h1, h3] using hq
        subst hq'
        exact Or.inl rfl

/-- Phase-two mask satisfies the phase-two policy at every row. -/
theorem dMask₂_wellMasked (email : Nat) :
    LWellMasked flows2 dMask₂ (dCtx email) := by
  intro p q hq
  by_cases h3 : p = 3
  · subst h3
    have hq' : q = 0 ∨ q = 2 ∨ q = 3 := by simpa [dMask₂] using hq
    obtain h | h | h := hq' <;> subst h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · by_cases h2 : p = 2
    · subst h2
      have hq' : q = 0 ∨ q = 2 := by simpa [dMask₂, h3] using hq
      obtain h | h := hq' <;> subst h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · by_cases h1 : p = 1
      · subst h1
        have hq' : q = 0 ∨ q = 1 := by simpa [dMask₂, h3, h2] using hq
        obtain h | h := hq' <;> subst h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
      · have hq' : q = 0 := by simpa [dMask₂, h3, h2, h1] using hq
        subst hq'
        exact Or.inl rfl

/-- The summary emission respects the phase-one policy (S→S). -/
theorem dS₁_emission (email : Nat) : EmissionFlows flows1 (dCtx email) dS₁ := by
  intro e he
  have h : e = (2, 2) := by simpa [dS₁] using he
  subst h
  exact Or.inr (Or.inl rfl)

/-- The tool emission respects the phase-two policy (C→C). -/
theorem dS₂_emission (email : Nat) : EmissionFlows flows2 (dCtx email) dS₂ := by
  intro e he
  have h : e = (3, 3) := by simpa [dS₂] using he
  subst h
  exact Or.inr (Or.inl rfl)

/-- The interleaved (strict) schedule respects the phase-one policy
    throughout: both emissions stay in their own region. -/
theorem dS_strict_emission (email : Nat) :
    EmissionFlows flows1 (dCtx email) (dS₁ ++ dS₂) := by
  intro e he
  have h : e = (2, 2) ∨ e = (3, 3) := by simpa [dS₁, dS₂] using he
  obtain h | h := h <;> subst h
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inl rfl)

/-- Input equivalence at the tool observer under `flows1`: any two emails
    give contexts agreeing at every trusted- and tool-labeled position (the
    values differ only at the untrusted position 1). -/
theorem dCtx_lEq (a b : Nat) : LEq flows1 .tool (dCtx a) (dCtx b) := by
  refine ⟨fun p => rfl, fun p hp => ?_⟩
  have hp1 : p ≠ 1 := by
    intro hpe
    subst hpe
    rw [flows1_to_tool] at hp
    have hlab : (dCtx a).label 1 = .untrusted := rfl
    rw [hlab] at hp
    obtain h | h := hp <;> exact absurd h (by decide)
  show (if p = 1 then a else if p = 0 then 10 else 0)
     = (if p = 1 then b else if p = 0 then 10 else 0)
  rw [if_neg hp1, if_neg hp1]

/-- Only position 2 carries the summary label. -/
theorem dLabel_summary (p : Pos) (hp : dLabel p = .summary) : p = 2 :=
  match p, hp with
  | 2, _ => rfl
  | 0, h => nomatch h
  | 1, h => nomatch h
  | 3, h => nomatch h
  | (_ + 4), h => nomatch h

/-- **The channel condition, discharged by computation**: emails 7 and 999
    generate the SAME summary (both ≡ 3 mod 4, so both summaries are 1).
    This is the declassification hypothesis of the conditional theorem —
    and the exact thing that FAILS for email 8. -/
theorem demo_channel :
    ∀ p, (dCtx 7).label p = .summary →
      (lgenLoop dMask₁ [modC] dS₁ (dCtx 7)).value p
        = (lgenLoop dMask₁ [modC] dS₁ (dCtx 999)).value p := by
  intro p hp
  have h2 : p = 2 := dLabel_summary p hp
  subst h2
  decide

/-- **Strict instance.** Under the strict mask and interleaved schedule, the
    whole generation's trusted- and tool-visible content is identical across
    emails 7 and 999 — unconditionally (and the same instantiation works for
    ANY pair of emails). -/
theorem demo_strict :
    LEq flows1 .tool
      (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 7))
      (lgenLoop dMask₁ [modC] (dS₁ ++ dS₂) (dCtx 999)) :=
  strict_tool_noninterference dMask₁ [modC] (dS₁ ++ dS₂)
    (dMask₁_wellMasked 7) (dCtx_lEq 7 999) (dS_strict_emission 7)

/-- **Only-through instance.** For the coinciding-summary pair, the phased
    generation's tool region is provably identical — the `#eval` agreement
    at position 3 is this theorem, not an accident. -/
theorem demo_only_through :
    LEq flows2 .tool
      (lgenLoop dMask₂ [modC] dS₂ (lgenLoop dMask₁ [modC] dS₁ (dCtx 7)))
      (lgenLoop dMask₂ [modC] dS₂ (lgenLoop dMask₁ [modC] dS₁ (dCtx 999))) :=
  only_through_summary dMask₁ dMask₂ [modC] dS₁ dS₂
    (dMask₁_wellMasked 7) (dS₁_emission 7)
    (dMask₂_wellMasked 7) (dS₂_emission 7)
    (dCtx_lEq 7 999) demo_channel

end Attnni

#print axioms Attnni.demo_strict
#print axioms Attnni.demo_only_through

/-!
## What to port to the PyTorch reference implementation

1. Prompt with a designated untrusted span (the email), schedule-fixed
   summary and tool-call regions (constrained decoding pins the regions).
2. Phase one: summary-region rows attend trusted + U; tool-region rows
   attend trusted only. Phase two: tool-region rows attend trusted +
   summary; nothing attends U on any path to the tool region.
3. Strict test: vary U — tool-call token ids bit-identical, summary free.
4. Conditional test: find two U's whose generated summaries coincide —
   tool-call ids must be bit-identical. Negative control: a U with a
   different summary moves the tool call despite its mask row being clean
   of U — the intransitive laundering signature.
-/
