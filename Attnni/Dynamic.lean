import Attnni.Model
import Attnni.Gate
import Attnni.Noninterference

/-!
# Attnni.Dynamic — data-dependent masks and implicit flows (B2)

Here the mask is COMPUTED from the context: `genMask : Context → Mask`. This is
where implicit flows live — if the attention structure depends on secrets, then
*which positions a public position reads* can itself encode a secret, even when no
secret VALUE flows directly.

The unconditional claim "dynamic masks are safe" is FALSE (that is the whole point
of implicit flows). The theorem is conditional: a mask generator is safe exactly
when it is `LowSound` — public positions' attention patterns do not depend on
secrets. Under low-soundness the two runs regain lockstep and noninterference holds.
-/

namespace Attnni

/-- A data-dependent mask generator. -/
abbrev MaskGen := Context → Mask

/-- **The central definition.** A generator is low-sound if, on any two
    low-equivalent contexts, every PUBLIC position gets the same attention pattern.
    (Public positions' masks may not depend on secret data — otherwise the choice
    of which positions to read would itself leak the secret: an implicit flow.) -/
def LowSound (gen : MaskGen) : Prop :=
  ∀ c₁ c₂, LowEq c₁ c₂ → ∀ p, c₁.label p = .low → gen c₁ p = gen c₂ p

/-- A dynamic layer step: compute the mask from the current context, then apply it.
    The aggregator f is arbitrary (any weights). -/
def dynStep (gen : MaskGen) (f : Combine) (c : Context) : Context :=
  layerStep (gen c) f c

/-- A dynamic run: fold dynamic steps. The mask is RECOMPUTED at each layer as the
    context evolves — so low-soundness must be maintained across layers. -/
def dynRun (gen : MaskGen) (fs : List Combine) (c : Context) : Context :=
  fs.foldl (fun acc f => dynStep gen f acc) c

/-- The dynamic well-maskedness condition at a context: the generated mask
    quarantines public from secret. Because the mask depends on c, this is stated
    at the specific context. -/
def DynWellMasked (gen : MaskGen) (c : Context) : Prop :=
  WellMasked (gen c) c

end Attnni

namespace Attnni

/-- **The dynamic step lemma.** One dynamic layer preserves low-equivalence, given
    the generator is low-sound and well-masked at c₁. The crux: at a public
    position p, low-soundness gives gen c₁ p = gen c₂ p (same positions read in
    both runs), well-maskedness gives those positions are low, low-equivalence
    gives their values agree — so f receives identical inputs and agrees. -/
theorem dynStep_preserves_lowEq (gen : MaskGen) (f : Combine)
    (hls : LowSound gen) {c₁ c₂ : Context}
    (hwm : DynWellMasked gen c₁) (h : LowEq c₁ c₂) :
    LowEq (dynStep gen f c₁) (dynStep gen f c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [dynStep, layerStep] at hp ⊢
  -- p is low. Low-soundness: gen c₁ p = gen c₂ p (same read positions).
  have hmask : gen c₁ p = gen c₂ p := hls c₁ c₂ ⟨hlab, hval⟩ p hp
  -- The read lists must be equal. gen c₁ p and gen c₂ p are the same list;
  -- and each read position q is low (well-masked) so its values agree.
  have hlists : (gen c₁ p).map c₁.value = (gen c₂ p).map c₂.value := by
    rw [← hmask]
    apply List.map_congr_left
    intro q hq
    have hqlow : c₁.label q = .low := hwm p hp q hq
    exact hval q hqlow
  rw [hlists]

end Attnni

namespace Attnni

/-- **Dynamic (implicit-flow) noninterference.** A low-sound mask generator that is
    well-masked on every context preserves low-equivalence across any dynamic run —
    for any weights. This is the implicit-flow result: even though the attention
    structure is COMPUTED from the data, no secret leaks, precisely because
    low-soundness forbids the public attention pattern from depending on secrets.
    (Drop low-soundness and the theorem is false — that is the implicit-flow
    channel.) -/
theorem dyn_noninterference (gen : MaskGen) (fs : List Combine)
    (hls : LowSound gen) (hwm : ∀ c, DynWellMasked gen c)
    {c₁ c₂ : Context} (h : LowEq c₁ c₂) :
    LowEq (dynRun gen fs c₁) (dynRun gen fs c₂) := by
  unfold dynRun
  induction fs generalizing c₁ c₂ with
  | nil => exact h
  | cons f fs ih =>
    exact ih (dynStep_preserves_lowEq gen f hls (hwm c₁) h)

end Attnni

#print axioms Attnni.dyn_noninterference
