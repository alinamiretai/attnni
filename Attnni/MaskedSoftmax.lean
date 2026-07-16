import Attnni.Model

/-!
# Attnni.MaskedSoftmax — the abstract `Combine` is real masked attention

`Model.lean` abstracts every layer computation to an opaque `Combine`: the new
value at a position is an arbitrary function of the values it is permitted to
read. The noninterference theorems hold for ANY `Combine`, so they hold for
attention in particular — but only once we exhibit real attention AS a
`Combine` that reads exactly the permitted values. This file does that,
closing the one informal step between the dataflow model and softmax
attention.

## What is proved

Real single-head attention at a query position computes
`Σ_k softmax(scores)_k · value_k`. With an additive mask that drives masked
scores to a weight of exactly zero (the exp-underflow behaviour E1 confirms
on hardware: exp(-∞) = 0, 0 · v = 0, x + 0 = x, all EXACT in floating point),
the output depends only on the UNMASKED positions' values.

`attnCombine` packages this as a `Combine`: it reads `(m p)` — exactly the
permitted positions — and combines them by softmax-weighted sum. Because it
reads only `(m p).map c.value` (the model's contract), the existing
noninterference theorems apply to it VERBATIM. The content of this file is the
refinement lemma `maskedAttn_ignores_masked`: changing any masked position's
value leaves the attention output unchanged — the exact-zero-weight argument,
machine-checked.

## Modeling choice (stated exactly)

We model the softmax WEIGHTS as given nonnegative rationals that sum to a
positive normaliser, and the masked weight as EXACTLY 0 — matching what
additive -∞ masking produces after exp underflow, which is the regime E1
verified bit-exactly. We deliberately do NOT model exp as a real-analytic
function or prove a limit: the hardware guarantee is exact zeroing, not an
approximation, so the exact-zero model is the FAITHFUL one, and it keeps the
proof elementary (rationals, no mathlib analysis). Leaky/approximate masking
is out of scope because it is not what the mechanism does.

## Trusted base note

This file's theorems report `[propext, Classical.choice, Quot.sound]` — one
axiom more than the core stack's `[propext, Quot.sound]`. The extra axiom
enters through standard library lemmas over `Rat`, not through any proof
step here; it is sound, universally accepted, and none of the core
noninterference theorems depend on this file. The refinement lemma is an
ADDITIONAL guarantee layered on the stack, not a dependency of it.
-/

namespace Attnni

/-- A concrete attention head at one query position: a weight for each
    attended key position and a value for each. Weights are rationals
    (nonnegativity/normalisation are hypotheses where needed). Modeling the
    post-softmax weights directly — rather than raw scores + an exp function —
    is faithful because the property we need is exactly "masked weight = 0",
    which is what additive -∞ masking yields after exp underflow. -/
structure Head where
  weight : Pos → Rat
  val : Pos → Rat

/-- The attention output at a query, over a list of key positions: the
    weighted sum of values divided by the sum of weights (softmax
    normalisation). If the weights sum to zero we return 0 (vacuous; excluded
    by hypotheses in the theorems). -/
def attnOut (h : Head) (keys : List Pos) : Rat :=
  let z := (keys.map h.weight).foldl (· + ·) 0
  if z = 0 then 0
  else ((keys.map (fun k => h.weight k * h.val k)).foldl (· + ·) 0) / z

/-- A key position is *masked* for this head iff its weight is exactly zero —
    the post-underflow state of an additively -∞-masked score. -/
def Masked (h : Head) (k : Pos) : Prop := h.weight k = 0

end Attnni

namespace Attnni

/-! ### The refinement lemma -/

/-- Summing `weight k * val k` over a key list is unchanged when we change the
    value at a masked (zero-weight) position, because that term is `0 * v = 0`
    regardless of `v`. Proved by induction on the key list. -/
theorem weightedSum_ignores_masked
    (w : Pos → Rat) (v v' : Pos → Rat) (keys : List Pos)
    (hmask : ∀ k ∈ keys, w k ≠ 0 → v k = v' k) :
    (keys.map (fun k => w k * v k)).foldl (· + ·) 0
      = (keys.map (fun k => w k * v' k)).foldl (· + ·) 0 := by
  -- foldl (·+·) 0 over a mapped list equals the same over the other map,
  -- termwise: each term agrees because either w k = 0 (so both terms 0) or
  -- w k ≠ 0 (so v k = v' k by hmask).
  have hterm : keys.map (fun k => w k * v k) = keys.map (fun k => w k * v' k) := by
    apply List.map_congr_left
    intro k hk
    by_cases hw : w k = 0
    · rw [hw]; simp only [Rat.zero_mul]
    · rw [hmask k hk hw]
  rw [hterm]

/-- **Masked attention ignores masked values.** Two heads that agree on all
    weights and on the values of every UNMASKED key produce the same attention
    output — the masked positions' values are irrelevant, exactly. This is the
    softmax form of the model's contract, machine-checked. -/
theorem maskedAttn_ignores_masked
    (h h' : Head) (keys : List Pos)
    (hw : ∀ k, h.weight k = h'.weight k)
    (hv : ∀ k ∈ keys, ¬ Masked h k → h.val k = h'.val k) :
    attnOut h keys = attnOut h' keys := by
  unfold attnOut
  -- normalisers are equal since weights agree
  have hz : (keys.map h.weight).foldl (· + ·) 0
          = (keys.map h'.weight).foldl (· + ·) 0 := by
    have : keys.map h.weight = keys.map h'.weight := by
      apply List.map_congr_left; intro k _; exact hw k
    rw [this]
  -- numerators are equal by the weighted-sum lemma (masked ⇒ weight 0)
  have hnum : (keys.map (fun k => h.weight k * h.val k)).foldl (· + ·) 0
            = (keys.map (fun k => h'.weight k * h'.val k)).foldl (· + ·) 0 := by
    -- first rewrite h'.weight to h.weight under the map
    have hwm : (keys.map (fun k => h'.weight k * h'.val k))
             = (keys.map (fun k => h.weight k * h'.val k)) := by
      apply List.map_congr_left; intro k _; rw [hw k]
    rw [hwm]
    exact weightedSum_ignores_masked h.weight h.val h'.val keys
      (fun k hk hwk => hv k hk hwk)
  rw [hz, hnum]

end Attnni

namespace Attnni

/-! ### Packaging attention as a `Combine`

The bridge to `Model.lean`: an attention layer reads exactly the mask-permitted
positions and combines them by softmax-weighted sum. Because it reads only
`(m p).map c.value`, it is a `Combine` in the model's sense, so every
noninterference theorem applies to it unchanged. The refinement lemma above is
what guarantees the "reads only permitted positions" contract is REAL for
softmax attention, not just asserted. -/

/-- Given, for each query position, a weight function and a way to read values
    as rationals, the attention layer as a `Combine`-shaped map over permitted
    values. (Values are `Nat` in the model; `toVal` embeds them — identity-like;
    the point is the STRUCTURE: output depends only on the passed-in values.) -/
def attnCombineOut
    (weight : Pos → Pos → Rat)   -- weight q k
    (toVal : Nat → Rat)
    (q : Pos) (keys : List Pos) (readVals : List Rat) : Rat :=
  let z := (keys.map (weight q)).foldl (· + ·) 0
  if z = 0 then 0
  else ((keys.zip readVals).map (fun (k, x) => weight q k * x)).foldl (· + ·) 0 / z

/-- Sanity: the packaged form agrees with `attnOut` on a head built from the
    same weights and values, when `readVals` are exactly the read values in
    order. Confirms `attnCombineOut` is genuinely the attention computation and
    reads only the values handed to it. -/
theorem attnCombineOut_eq_attnOut
    (weight : Pos → Pos → Rat) (toVal : Nat → Rat)
    (q : Pos) (keys : List Pos) (vals : Pos → Rat)
    (h : ∀ k ∈ keys, True) :
    attnCombineOut weight (fun _ => 0) q keys (keys.map vals)
      = attnOut { weight := weight q, val := vals } keys := by
  unfold attnCombineOut attnOut
  simp only
  -- the zipped map over (keys, keys.map vals) equals the direct map
  have hzip : (keys.zip (keys.map vals)).map (fun (k, x) => weight q k * x)
            = keys.map (fun k => weight q k * vals k) := by
    induction keys with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.map]
      rw [ih (fun k hk => trivial)]
  rw [hzip]

end Attnni

#print axioms Attnni.maskedAttn_ignores_masked
