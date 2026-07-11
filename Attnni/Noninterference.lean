import Attnni.Model
import Attnni.Gate

/-!
# Attnni.Noninterference — the airgap theorem

Under a well-formed (quarantine) mask, a masked transformer's public outputs are
identical regardless of secret content — for ANY per-layer computation. The
combining functions are universally quantified, so the guarantee holds for any
weights: it is a property of the dataflow, not the learned function.
-/

namespace Attnni

/-- **The layer-step lemma.** One masked layer preserves low-equivalence,
    provided the mask is well-formed. The heart of the airgap: a low position
    reads only low positions (well-masked), whose values agree across the two
    runs (low-equivalence), so the combining function receives identical inputs
    and produces identical output — for ANY combining function `f`. -/
theorem layerStep_preserves_lowEq (m : Mask) (f : Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) :
    LowEq (layerStep m f c₁) (layerStep m f c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  -- p is low in (layerStep .. c₁); labels unchanged, so p is low in c₁
  simp only [layerStep] at hp ⊢
  -- goal: f p ((m p).map c₁.value) = f p ((m p).map c₂.value)
  -- suffices: the two mapped lists are equal
  have hlists : (m p).map c₁.value = (m p).map c₂.value := by
    apply List.map_congr_left
    intro q hq
    -- q ∈ m p, and p is low, so by well-maskedness q is low, so values agree
    have hqlow : c₁.label q = .low := hwm p hp q hq
    exact hval q hqlow
  rw [hlists]

end Attnni

namespace Attnni

/-- WellMasked is preserved by a layer step: labels don't change, so the
    quarantine structure is invariant across layers. -/
theorem layerStep_preserves_wellMasked (m : Mask) (f : Combine) {c : Context}
    (hwm : WellMasked m c) : WellMasked m (layerStep m f c) := by
  intro p hp q hq
  simp only [layerStep] at hp ⊢
  exact hwm p hp q hq

/-- **Airgap noninterference.** Under a well-formed quarantine mask, running any
    stack of layers (any per-layer computations) preserves low-equivalence: two
    contexts that agree at public positions and differ only in secret content
    produce identical public outputs. The combining functions are universally
    quantified, so the guarantee holds for ANY weights. -/
theorem noninterference (m : Mask) (fs : List Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) :
    LowEq (run m fs c₁) (run m fs c₂) := by
  unfold run
  induction fs generalizing c₁ c₂ with
  | nil => exact h
  | cons f fs ih =>
    exact ih (layerStep_preserves_wellMasked m f hwm)
             (layerStep_preserves_lowEq m f hwm h)

/-- **The headline corollary.** Public output values are identical across the two
    runs: a public position's final value does not depend on any secret content. -/
theorem pub_noninterference (m : Mask) (fs : List Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) (p : Pos)
    (hp : (run m fs c₁).label p = .low) :
    (run m fs c₁).value p = (run m fs c₂).value p :=
  (noninterference m fs hwm h).2 p hp

end Attnni

#print axioms Attnni.noninterference
