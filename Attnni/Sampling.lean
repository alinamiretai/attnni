import Attnni.Model
import Attnni.Gate
import Attnni.Generation

/-!
# Attnni.Sampling — sampled decoding under shared randomness

`Generation.lean`'s readout is deterministic. Real decoding SAMPLES: the
emitted token is a function of the logits AND a random draw. This file
records the observation that sampling is ALREADY inside the loop theorem's
scope, states the corollary in the form the paper needs, and demos it.

## The modeling argument

Thread the randomness as a PUBLIC POSITION: the seed occupies a low-labeled
slot, the frontier's mask may attend it, and the per-position sampler is
just a `Combine` that reads (logits-summary, seed) — an arbitrary function,
like everything else in the model. Then:

* **Pointwise (this file).** For every FIXED seed, the emitted tokens are
  secret-independent — `gen_noninterference` verbatim, with the seed among
  the public data the two runs share. The proof is one application per
  seed; the content is the modeling, and that is the point: no new channel
  analysis is needed, because the sampler is just one more combine and the
  seed is just one more public position.
* **Distributional (the reading).** "For every seed, outputs are equal" is
  the determinized form of "the output DISTRIBUTION is secret-independent":
  sample the seed from any distribution, and the induced distributions over
  token sequences coincide exactly, because they agree pointwise on the
  sample space. The ∀-seed statement is the coupling argument made
  machine-checkable without formalizing probability.

## The load-bearing hypothesis

The seed must be LOW — shared across the two runs and independent of the
secret. A secret-DEPENDENT seed (or a sampler whose randomness source the
secret can influence) is an implicit flow, exactly analogous to a
secret-dependent mask in `Dynamic.lean`, and the theorem is silent about
it. Operationally: the RNG state is part of the public trusted input, which
matches how reproducible serving stacks already treat it.
-/

namespace Attnni

/-- **Seeded generation noninterference.** For families of contexts indexed
    by the seed — each pair low-equivalent (same public data, same seed,
    secrets differing), each well-masked, each schedule public-sourced —
    every seed yields identical generated public context across the secret
    variation. Pointwise over seeds = distributional invariance under
    shared randomness. -/
theorem seeded_gen_noninterference (m : Mask) (fs : List Combine)
    (s : Schedule) (c₁ c₂ : Nat → Context)
    (hwm : ∀ seed, WellMasked m (c₁ seed))
    (h : ∀ seed, LowEq (c₁ seed) (c₂ seed))
    (hpe : ∀ seed, ∀ e ∈ s, (c₁ seed).label e.1 = .low) :
    ∀ seed, LowEq (genLoop m fs s (c₁ seed)) (genLoop m fs s (c₂ seed)) :=
  fun seed => gen_noninterference m fs s (hwm seed) (h seed) (hpe seed)

/-- Per-token form: for every seed, each public slot — every sampled token —
    is identical across the secret variation. -/
theorem seeded_token_noninterference (m : Mask) (fs : List Combine)
    (s : Schedule) (c₁ c₂ : Nat → Context)
    (hwm : ∀ seed, WellMasked m (c₁ seed))
    (h : ∀ seed, LowEq (c₁ seed) (c₂ seed))
    (hpe : ∀ seed, ∀ e ∈ s, (c₁ seed).label e.1 = .low)
    (d : Pos) (hd : ∀ seed, (c₁ seed).label d = .low) :
    ∀ seed, (genLoop m fs s (c₁ seed)).value d
              = (genLoop m fs s (c₂ seed)).value d :=
  fun seed => emitted_token_noninterference m fs s
    (hwm seed) (h seed) (hpe seed) d (hd seed)

end Attnni

#print axioms Attnni.seeded_gen_noninterference

namespace Attnni

/-! ### Demo — sampled tokens move with the seed, never with the secret

Layout: 0 public prompt (100), 1 PUBLIC SEED, 2 secret, 3–4 sampled output
slots, ≥ 5 high. The "sampler" is sum-mod-7 over (prompt, seed, prior
token) — an arbitrary seed-consuming `Combine`, which is all a sampler is
to this model. -/

def sampLabel : Pos → Label
  | 0 => .low
  | 1 => .low     -- the seed: public, shared across runs
  | 2 => .high    -- the secret
  | 3 => .low
  | 4 => .low
  | _ => .high

/-- The secret row reads what it likes; every other row reads prompt, seed,
    and the prior output — never the secret. -/
def sampMask : Mask := fun p => if p = 2 then [0, 2] else [0, 1, 3]

/-- The sampler: an opaque seed-consuming combine. -/
def samp : Combine := fun _ vs => (vs.foldl (· + ·) 0) % 7

def sampSched : Schedule := [(0, 3), (3, 4)]

def sampCtx (seed secret : Nat) : Context :=
  { value := fun p =>
      if p = 2 then secret else if p = 1 then seed else if p = 0 then 100 else 0
    label := sampLabel }

-- Same seed, different secrets: tokens IDENTICAL.
#eval (genLoop sampMask [samp] sampSched (sampCtx 0 42)).value 3    -- 2
#eval (genLoop sampMask [samp] sampSched (sampCtx 0 999)).value 3   -- 2 (SAME)
#eval (genLoop sampMask [samp] sampSched (sampCtx 0 42)).value 4    -- 4
#eval (genLoop sampMask [samp] sampSched (sampCtx 0 999)).value 4   -- 4 (SAME)
-- Different seeds: tokens MOVE — the sampling is real.
#eval (genLoop sampMask [samp] sampSched (sampCtx 1 42)).value 3    -- 3
#eval (genLoop sampMask [samp] sampSched (sampCtx 1 42)).value 4    -- 6
#eval (genLoop sampMask [samp] sampSched (sampCtx 5 42)).value 3    -- 0
#eval (genLoop sampMask [samp] sampSched (sampCtx 5 999)).value 4   -- 0 (still secret-blind)

/-- Well-masked for every seed and secret: labels are seed-independent. -/
theorem sampCtx_wellMasked (seed secret : Nat) :
    WellMasked sampMask (sampCtx seed secret) := by
  intro p hp q hq
  by_cases h2 : p = 2
  · subst h2
    have hlab : (sampCtx seed secret).label 2 = .high := rfl
    rw [hlab] at hp
    exact absurd hp (by decide)
  · have hq' : q = 0 ∨ q = 1 ∨ q = 3 := by simpa [sampMask, h2] using hq
    obtain h | h | h := hq' <;> subst h <;> rfl

/-- Low-equivalence for every seed: SAME seed on both sides — the coupling —
    with only the secret differing. -/
theorem sampCtx_lowEq (seed a b : Nat) :
    LowEq (sampCtx seed a) (sampCtx seed b) := by
  refine ⟨fun p => rfl, fun p hp => ?_⟩
  have hp2 : p ≠ 2 := by
    intro hpe
    subst hpe
    have hlab : (sampCtx seed a).label 2 = .high := rfl
    rw [hlab] at hp
    exact absurd hp (by decide)
  show (if p = 2 then a else if p = 1 then seed else if p = 0 then 100 else 0)
     = (if p = 2 then b else if p = 1 then seed else if p = 0 then 100 else 0)
  rw [if_neg hp2, if_neg hp2]

/-- Both emissions source from public positions, for every seed. -/
theorem sampSched_public (seed secret : Nat) :
    ∀ e ∈ sampSched, (sampCtx seed secret).label e.1 = .low := by
  intro e he
  have h : e = (0, 3) ∨ e = (3, 4) := by simpa [sampSched] using he
  obtain h | h := h <;> subst h <;> rfl

/-- **The demo instance**: for EVERY seed, the sampled generation is
    identical across secrets 42 and 999 — distributional invariance under
    shared randomness, made pointwise. -/
theorem demo_seeded_noninterference :
    ∀ seed, LowEq (genLoop sampMask [samp] sampSched (sampCtx seed 42))
                  (genLoop sampMask [samp] sampSched (sampCtx seed 999)) :=
  seeded_gen_noninterference sampMask [samp] sampSched
    (fun seed => sampCtx seed 42) (fun seed => sampCtx seed 999)
    (fun seed => sampCtx_wellMasked seed 42)
    (fun seed => sampCtx_lowEq seed 42 999)
    (fun seed => sampSched_public seed 42)

end Attnni

#print axioms Attnni.demo_seeded_noninterference
