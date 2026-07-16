import Attnni.Model
import Attnni.Gate
import Attnni.Lattice
import Attnni.Session

/-!
# Attnni.SessionDemo — an agent turn, concretely

One agent turn: generate a token, hand it to a tool, generate again reading
the tool's result. Layout (fixed label plan across the whole session):

  position 0 : PUBLIC prompt (value 100)
  position 1 : SECRET
  position 2 : PUBLIC slot — the emitted token (the "tool call")
  position 3 : PUBLIC slot — the tool's result
  position 4 : PUBLIC slot — the final answer
  positions ≥ 5 : high (outside the window)

Steps: emit into 2, run a tool that reads [2] and doubles it into 3, emit
the answer into 4. The two-point lattice (`flowsLH`, observer `low`) makes
this the confidentiality spec extended across the agent loop: flip the
secret, and the emitted token, the TOOL'S OUTPUT, and the final answer are
all provably unchanged.

The negative control launders the secret through the ENVIRONMENT: corrupt
one mask row so the first emission reads the secret; the tool then dutifully
doubles a secret-dependent value, and the final answer — whose own mask row
and whose tool's read-list never touch position 1 — diverges. Two re-entries
(one through the context, one through a tool execution) between the secret
and the observable divergence: exactly the channel `session_noninterference`
closes.
-/

namespace Attnni

/-- The fixed label plan for the session. -/
def sLabel : Pos → Label
  | 0 => .low
  | 1 => .high
  | 2 => .low
  | 3 => .low
  | 4 => .low
  | _ => .high

/-- SAFE mask: the secret row reads what it likes; every other row reads
    only {0,2,3} — prompt, emitted token, tool result. Never the secret. -/
def sMaskSafe : Mask := fun p => if p = 1 then [0, 1] else [0, 2, 3]

/-- LEAKY mask: the first emission's source row (position 0) also reads the
    secret. One corrupted attention row, two hops upstream of the answer. -/
def sMaskLeak : Mask := fun p => if p ≤ 1 then [0, 1] else [0, 2, 3]

/-- The layer: sum of attended values. -/
def sSum : Combine := fun _ vs => vs.foldl (· + ·) 0

/-- The tool: reads the emitted token (position 2 — its declared span) and
    doubles it. The compute function is opaque to the theorem; only the
    read-list matters. -/
def sTool : EnvCall :=
  { reads := [2], compute := fun vs => (vs.foldl (· + ·) 0) * 2, dst := 3 }

/-- The session, parameterized by the mask: emit, execute the tool, emit. -/
def sSteps (m : Mask) : List SessionStep :=
  [ .gen m [sSum] [(0, 2)]
  , .env sTool
  , .gen m [sSum] [(3, 4)] ]

/-- The context, parameterized by the secret. -/
def sCtx (secret : Nat) : LContext Label :=
  { value := fun p => if p = 1 then secret else if p = 0 then 100 else 0
    label := sLabel }

-- === Confidentiality across the agent loop, under the SAFE mask ===
-- Token, tool result, answer: all identical across secret = 42 vs 999.
#eval (session (sSteps sMaskSafe) (sCtx 42)).value 2    -- token: 100
#eval (session (sSteps sMaskSafe) (sCtx 999)).value 2   -- token: 100 (SAME)
#eval (session (sSteps sMaskSafe) (sCtx 42)).value 3    -- tool result: 200
#eval (session (sSteps sMaskSafe) (sCtx 999)).value 3   -- tool result: 200 (SAME)
#eval (session (sSteps sMaskSafe) (sCtx 42)).value 4    -- answer: 400
#eval (session (sSteps sMaskSafe) (sCtx 999)).value 4   -- answer: 400 (SAME)

-- === The environment-laundered leak, under the LEAKY mask ===
-- The tool's read-list ([2]) and the answer's mask row ([0,2,3]) are both
-- clean of the secret — yet everything downstream diverges.
#eval (session (sSteps sMaskLeak) (sCtx 42)).value 2    -- 142  (token carries secret)
#eval (session (sSteps sMaskLeak) (sCtx 999)).value 2   -- 1099
#eval (session (sSteps sMaskLeak) (sCtx 42)).value 3    -- 284  (TOOL launders it)
#eval (session (sSteps sMaskLeak) (sCtx 999)).value 3   -- 2198
#eval (session (sSteps sMaskLeak) (sCtx 42)).value 4    -- 526  (answer diverges)
#eval (session (sSteps sMaskLeak) (sCtx 999)).value 4   -- 3397 (leak, two hops removed)

end Attnni

namespace Attnni

/-! ### Discharging the premises for the safe session -/

/-- The safe mask quarantines under `flowsLH`: every non-secret row reads
    only low positions; the secret row is unconstrained upward. -/
theorem sMaskSafe_wellMasked (secret : Nat) :
    LWellMasked flowsLH sMaskSafe (sCtx secret) := by
  intro p q hq
  by_cases h1 : p = 1
  · subst h1
    have hq' : q = 0 ∨ q = 1 := by simpa [sMaskSafe] using hq
    obtain h | h := hq' <;> subst h
    · exact Or.inl rfl
    · exact Or.inr rfl
  · have hq' : q = 0 ∨ q = 2 ∨ q = 3 := by simpa [sMaskSafe, h1] using hq
    obtain h | h | h := hq' <;> subst h <;> exact Or.inl rfl

/-- Both emissions read from public sources into public slots. -/
theorem sEmission₁ (secret : Nat) :
    EmissionFlows flowsLH (sCtx secret) [(0, 2)] := by
  intro e he
  have h : e = (0, 2) := by simpa using he
  subst h
  exact Or.inl rfl

theorem sEmission₂ (secret : Nat) :
    EmissionFlows flowsLH (sCtx secret) [(3, 4)] := by
  intro e he
  have h : e = (3, 4) := by simpa using he
  subst h
  exact Or.inl rfl

/-- The tool respects its clearance: its one declared read (the emitted
    token, low) flows into its destination slot (the result slot, low). -/
theorem sTool_ok (secret : Nat) :
    ∀ q ∈ sTool.reads, flowsLH ((sCtx secret).label q) ((sCtx secret).label sTool.dst) := by
  intro q hq
  have h : q = 2 := by simpa [sTool] using hq
  subst h
  exact Or.inl rfl

/-- Every step of the safe session satisfies its policy obligation. -/
theorem sSteps_ok (secret : Nat) :
    ∀ st ∈ sSteps sMaskSafe, StepOk flowsLH (sCtx secret) st := by
  intro st hst
  have h : st = SessionStep.gen sMaskSafe [sSum] [(0, 2)]
         ∨ st = SessionStep.env sTool
         ∨ st = SessionStep.gen sMaskSafe [sSum] [(3, 4)] := by
    simpa [sSteps] using hst
  obtain h | h | h := h <;> subst h
  · exact ⟨sMaskSafe_wellMasked secret, sEmission₁ secret⟩
  · exact sTool_ok secret
  · exact ⟨sMaskSafe_wellMasked secret, sEmission₂ secret⟩

/-- Low-equivalence: any two secrets give contexts agreeing at every low
    position. -/
theorem sCtx_lEq (a b : Nat) : LEq flowsLH .low (sCtx a) (sCtx b) := by
  refine ⟨fun p => rfl, fun p hp => ?_⟩
  rw [flowsLH_to_low] at hp
  have hp1 : p ≠ 1 := by
    intro hpe
    subst hpe
    have hlab : (sCtx a).label 1 = .high := rfl
    rw [hlab] at hp
    exact absurd hp (by decide)
  show (if p = 1 then a else if p = 0 then 100 else 0)
     = (if p = 1 then b else if p = 0 then 100 else 0)
  rw [if_neg hp1, if_neg hp1]

/-- **The session instance.** The whole agent turn — both generations and
    the tool execution — is identical at every public position across the
    two secrets. The `#eval` agreements above are this theorem. -/
theorem demo_session_noninterference :
    LEq flowsLH .low
      (session (sSteps sMaskSafe) (sCtx 42))
      (session (sSteps sMaskSafe) (sCtx 999)) :=
  session_noninterference flowsLH_trans .low (sSteps sMaskSafe)
    (sSteps_ok 42) (sCtx_lEq 42 999)

/-- The tool's OUTPUT is secret-independent — the environment cannot be used
    to launder what never reached it. -/
theorem demo_tool_result_clean :
    (session (sSteps sMaskSafe) (sCtx 42)).value 3
      = (session (sSteps sMaskSafe) (sCtx 999)).value 3 :=
  session_token_noninterference flowsLH_trans .low (sSteps sMaskSafe)
    (sSteps_ok 42) (sCtx_lEq 42 999) 3 (Or.inl rfl)

end Attnni

#print axioms Attnni.demo_session_noninterference

/-!
## What to port to the reference implementation

The session harness: (1) fixed label plan over prompt + secret span +
tool-call region + tool-result region + answer region; (2) masks audited
once; (3) the tool adapter enforces the declared read-list — the tool
process receives ONLY the tool-call region's tokens, never the raw context
(this is the interface obligation the proof makes explicit); (4) run the
turn with secret = A and secret = B: tool-call tokens, tool INPUT bytes,
and answer tokens must be bit-identical. Negative control: corrupt one
attention row upstream and watch the divergence propagate through the tool.
-/
