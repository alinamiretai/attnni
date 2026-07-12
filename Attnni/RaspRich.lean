import Attnni.Model
import Attnni.Gate
import Attnni.Noninterference
import Attnni.Rasp

/-!
# Attnni.RaspRich — an enriched RASP layer matching real transformer structure

A real transformer layer is: multi-head attention, then a position-wise MLP, with
residual connections. This file models all three explicitly and shows
noninterference still holds — so AttnNI's guarantee covers the actual architecture,
not just a single opaque combine function.

Key fact: none of the three adds an inter-position channel.
- Multi-head attention: several masked reads; each safe by the masking argument.
- Position-wise MLP: reads only its own position; trivially safe.
- Residual: per-position add of old and new value (both at the same position); safe.
Attention remains the ONLY inter-position channel, so masking still cuts all flow.
-/

namespace Attnni

/-- A multi-head selector: a list of heads, each a selector (mask). All heads share
    the same well-maskedness requirement (public reads only public). -/
abbrev MultiHead := List Selector

/-- A rich layer: multiple attention heads (each its own selector + aggregator),
    a position-wise MLP, and residual mixing. All the per-position computations
    (head aggregators, MLP, residual combine) are arbitrary — any weights. -/
structure RichLayer where
  heads   : List (Selector × Aggregator)   -- multi-head attention
  mlp     : Pos → Nat → Nat                 -- position-wise: (pos, value) → value
  residual: Nat → Nat → Nat                 -- combine (old value) (attention+mlp out)

/-- All heads of a rich layer are well-masked at context c: every head's selector
    quarantines public from secret. -/
def RichWellMasked (r : RichLayer) (c : Context) : Prop :=
  ∀ s ∈ (r.heads.map Prod.fst), WellMasked s c

/-- Apply a rich layer. For each position p:
    1. each head reads its masked positions and aggregates;
    2. the head outputs are summed (the multi-head combine);
    3. the MLP is applied position-wise;
    4. the residual mixes p's OLD value with the new one. -/
def RichLayer.apply (r : RichLayer) (c : Context) : Context :=
  { label := c.label
    value := fun p =>
      let attnOut := (r.heads.map (fun hd => hd.2 p ((hd.1 p).map c.value))).foldl (· + ·) 0
      let mlpOut  := r.mlp p attnOut
      r.residual (c.value p) mlpOut }

end Attnni

namespace Attnni

/-- **The rich layer-step lemma.** A rich layer (multi-head attention + MLP +
    residual) preserves low-equivalence, given all heads are well-masked. At a
    public position p: each head reads only public positions (well-masked), whose
    values agree (low-equivalence), so each head's aggregation agrees; the summed
    attention output agrees; the MLP (position-wise) applied to equal inputs agrees;
    the residual mixes p's OLD value (agrees, p is low) with the equal MLP output.
    Every step preserves agreement — for ANY head aggregators, MLP, and residual. -/
theorem richLayer_preserves_lowEq (r : RichLayer)
    {c₁ c₂ : Context} (hwm : RichWellMasked r c₁) (h : LowEq c₁ c₂) :
    LowEq (r.apply c₁) (r.apply c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [RichLayer.apply]
  -- The residual and MLP are functions applied to p's old value and the attn out;
  -- p is low so c₁.value p = c₂.value p; suffices the attention outputs agree.
  have hpval : c₁.value p = c₂.value p := hval p hp
  -- Each head's read list agrees: head selector is well-masked, so reads are low.
  have hheads : (r.heads.map (fun hd => hd.2 p ((hd.1 p).map c₁.value)))
              = (r.heads.map (fun hd => hd.2 p ((hd.1 p).map c₂.value))) := by
    apply List.map_congr_left
    intro hd hhd
    -- this head's selector is well-masked
    have hsel : WellMasked hd.1 c₁ := hwm hd.1 (List.mem_map_of_mem hhd)
    have hlists : (hd.1 p).map c₁.value = (hd.1 p).map c₂.value := by
      apply List.map_congr_left
      intro q hq
      have hqlow : c₁.label q = .low := hsel p hp q hq
      exact hval q hqlow
    rw [hlists]
  rw [hpval, hheads]

end Attnni

namespace Attnni

/-- Rich well-maskedness is preserved: labels never change. -/
theorem richApply_preserves_wellMasked (r r' : RichLayer) {c : Context}
    (hwm : RichWellMasked r' c) : RichWellMasked r' (r.apply c) := by
  intro s hs
  intro p hp q hq
  exact hwm s hs p hp q hq

/-- Run a stack of rich layers. -/
def richRun (prog : List RichLayer) (c : Context) : Context :=
  prog.foldl (fun acc r => r.apply acc) c

/-- **Rich-architecture noninterference.** A stack of realistic transformer layers
    (multi-head attention + MLP + residual), each with well-masked heads, leaks
    nothing from secret to public — for any weights. This states AttnNI's guarantee
    over the actual per-layer transformer architecture, not an opaque combine. -/
theorem rich_noninterference (prog : List RichLayer) {c₁ c₂ : Context}
    (hwm : ∀ r ∈ prog, RichWellMasked r c₁) (h : LowEq c₁ c₂) :
    LowEq (richRun prog c₁) (richRun prog c₂) := by
  unfold richRun
  induction prog generalizing c₁ c₂ with
  | nil => exact h
  | cons r rs ih =>
    apply ih
    · intro r' hr'
      exact richApply_preserves_wellMasked r r' (hwm r' (List.mem_cons_of_mem r hr'))
    · exact richLayer_preserves_lowEq r (hwm r List.mem_cons_self) h

end Attnni

#print axioms Attnni.rich_noninterference
