import Attnni.Model
import Attnni.Gate
import Attnni.Checker
import Attnni.Generation

/-!
# Attnni.GenerationDemo — confidentiality across the loop, concretely

`Demo.lean` shows the single-pass airgap on 3 positions. Here we show the same
guarantee *surviving generation*: we emit several tokens, each re-entering the
context and being read by later passes, and the secret still never influences
any emitted token — the property `gen_noninterference` proves in general.

Layout (fixed label plan — output slots carry their labels before being filled):
  position 0 : PUBLIC   (public prompt token)
  position 1 : SECRET   (the thing that must not leak)
  positions 2,3,4 : PUBLIC output slots (pre-assigned; written by the loop)
  positions ≥ 5 : high  (outside the window — audit convention)

The schedule emits three tokens: read the run's value at the last public
position, write it into the next slot — `[(0,2), (2,3), (3,4)]`. Under the safe
mask every non-secret position attends only to {0,2,3} (prompt + output slots),
so each emitted token re-enters the context and is read by later steps —
exactly the transitive channel the loop theorem must close.

Finally the counterexample: a mask where position 0 also reads the secret. The
FIRST emitted token then depends on the secret — and so does the THIRD, whose
own attention never touches position 1: the leak launders forward through the
context. The theorem's public-source + well-masked hypotheses are exactly what
rule this out.
-/

namespace Attnni

/-- The fixed label plan: prompt public, secret at 1, output slots 2–4 public
    (pre-assigned, never changed), everything beyond the window high. -/
def gLabel : Pos → Label
  | 0 => .low
  | 1 => .high
  | 2 => .low
  | 3 => .low
  | 4 => .low
  | _ => .high

/-- A SAFE mask: the secret position may read what it likes (it is not public);
    every other position attends only to the prompt and the output slots — all
    public, and including previously-emitted tokens (re-entry). -/
def gMaskSafe : Mask := fun p => if p = 1 then [0, 1] else [0, 2, 3]

/-- An UNSAFE mask: position 0 — the first emission's source — also reads the
    secret. Quarantine violated at one edge. -/
def gMaskLeak : Mask := fun p => if p ≤ 1 then [0, 1] else [0, 2, 3]

/-- A concrete one-layer stack: each position's new value is the sum of the
    values it attends to (any deterministic function works; this is one
    `Combine`, and the run is `[gEmit]`). -/
def gEmit : Combine := fun _ vs => vs.foldl (· + ·) 0

/-- The generation schedule, fixed in advance: read the run at the last public
    position, write the next output slot. Three tokens. -/
def gSchedule : Schedule := [(0, 2), (2, 3), (3, 4)]

/-- Two contexts identical on public data, differing only in the SECRET. -/
def gCtxA : Context :=
  { value := fun p => if p = 1 then 7 else if p = 0 then 100 else 0
    label := gLabel }
def gCtxB : Context :=
  { value := fun p => if p = 1 then 999 else if p = 0 then 100 else 0
    label := gLabel }

-- === Confidentiality across the loop, under the SAFE mask ===
-- Three emitted tokens land at 2, 3, 4. Each must be IDENTICAL across
-- secret = 7 vs secret = 999 — including tokens 3 and 4, which READ token 2.

#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxA).value 2   -- expect 100
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxB).value 2   -- expect 100 (SAME)
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxA).value 3   -- expect 200
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxB).value 3   -- expect 200 (SAME)
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxA).value 4   -- expect 400
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxB).value 4   -- expect 400 (SAME)

-- Sanity: the secret position itself still differs (it is allowed to).
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxA).value 1   -- 7
#eval (genLoop gMaskSafe [gEmit] gSchedule gCtxB).value 1   -- 999 (differs, fine)

-- === The transitive leak, under the UNSAFE mask ===
-- Position 0 now reads the secret, so the FIRST emitted token differs — and
-- because later steps read the emitted tokens, the divergence launders
-- forward: token 4 differs even though ITS mask ([0,2,3]) never touches the
-- secret. This is exactly the channel `gen_noninterference` closes.

#eval (genLoop gMaskLeak [gEmit] gSchedule gCtxA).value 2   -- 107  (contains secret 7)
#eval (genLoop gMaskLeak [gEmit] gSchedule gCtxB).value 2   -- 1099 (contains secret 999) — DIFFERS
#eval (genLoop gMaskLeak [gEmit] gSchedule gCtxA).value 4   -- 414  — laundered
#eval (genLoop gMaskLeak [gEmit] gSchedule gCtxB).value 4   -- 2398 — laundered (leak, one hop removed!)

-- === The checker sees the difference (one audit covers the whole loop) ===
-- Labels are a fixed plan and never change, so ONE well-maskedness check
-- covers every pass of every step — this is the point of the fixed plan.
#eval wellMaskedCheck gMaskSafe gCtxA [0, 1, 2, 3, 4]   -- expect: true
#eval wellMaskedCheck gMaskLeak gCtxA [0, 1, 2, 3, 4]   -- expect: false (pos 0 reads secret)

end Attnni

namespace Attnni

/-! ### Discharging the theorem's hypotheses for the safe demo

The identical outputs above are instances of `gen_noninterference`, not
accidents: we discharge all three premises — low-equivalence, well-maskedness,
and the public-source schedule condition — and instantiate the theorem. -/

/-- The two demo contexts are low-equivalent: same labels, and equal values at
    every public position (all positions except the secret at 1). -/
theorem gCtx_lowEq : LowEq gCtxA gCtxB := by
  refine ⟨fun p => rfl, fun p hp => ?_⟩
  have hp1 : p ≠ 1 := by
    intro h; subst h; exact absurd hp (by decide)
  show (if p = 1 then 7 else if p = 0 then 100 else 0)
     = (if p = 1 then 999 else if p = 0 then 100 else 0)
  rw [if_neg hp1, if_neg hp1]

/-- The safe mask is well-masked: every position other than the secret reads
    only {0,2,3}, all public. (The secret position is unconstrained.) -/
theorem gMaskSafe_wellMasked : WellMasked gMaskSafe gCtxA := by
  intro p hp q hq
  by_cases hp1 : p = 1
  · subst hp1; exact absurd hp (by decide)
  · simp only [gMaskSafe, if_neg hp1] at hq
    have hq' : q = 0 ∨ q = 2 ∨ q = 3 := by simpa using hq
    obtain h | h | h := hq' <;> subst h <;> rfl

/-- Every scheduled emission reads from a public source: 0, 2, 3 are all low.
    Decidable — the schedule and the label plan are concrete. -/
theorem gSchedule_public : ∀ e ∈ gSchedule, gCtxA.label e.1 = .low := by decide

/-- **The demo instance of the loop theorem.** The whole generated context —
    every emitted token included — is identical across the two secrets. -/
theorem demo_gen_noninterference :
    LowEq (genLoop gMaskSafe [gEmit] gSchedule gCtxA)
          (genLoop gMaskSafe [gEmit] gSchedule gCtxB) :=
  gen_noninterference gMaskSafe [gEmit] gSchedule
    gMaskSafe_wellMasked gCtx_lowEq gSchedule_public

/-- The per-token instance: the LAST emitted token — the one two re-entries
    downstream of the first — is secret-independent. -/
theorem demo_last_token :
    (genLoop gMaskSafe [gEmit] gSchedule gCtxA).value 4
      = (genLoop gMaskSafe [gEmit] gSchedule gCtxB).value 4 :=
  emitted_token_noninterference gMaskSafe [gEmit] gSchedule
    gMaskSafe_wellMasked gCtx_lowEq gSchedule_public 4 rfl

end Attnni

#print axioms Attnni.demo_gen_noninterference

/-!
## What to port to the PyTorch reference implementation

The `#eval` block above is the exact test the reference implementation must
pass, scaled to a real model:

1. Fix a prompt with a designated secret span; build the (fixed) label vector,
   output slots pre-labeled public.
2. Build the attention mask so no public position — including every output
   slot — ever attends the secret span; audit it ONCE (`wellMaskedCheck`).
3. Generate k tokens with secret = A, then secret = B (A ≠ B).
4. Assert the emitted token ids are **bit-identical** across the two runs.

That assertion is `gen_noninterference` made empirical. The unsafe-mask block
is the negative control — and note its shape: the divergence at token 4, whose
own attention row is clean, is the transitive laundering that a per-pass check
cannot see and the loop theorem rules out.
-/
