import Attnni.Model

/-!
# Attnni.Lattice — multi-compartment noninterference

Generalizes the two-label airgap to an arbitrary label preorder. The quarantine
constraint: every position attends only to positions whose labels flow into its
own. The theorem: for EVERY observer level ℓ, positions visible to ℓ compute
identical values across any two runs agreeing at ℓ-visible positions — for any
weights. The two-label theorem is the instance L = Label, observer = low.
-/

namespace Attnni

variable {L : Type}

/-- A labeled context over an arbitrary label type. -/
structure LContext (L : Type) where
  value : Pos → Nat
  label : Pos → L

/-- One layer step over labeled contexts (same dataflow as Model.lean). -/
def lstep (m : Mask) (f : Combine) (c : LContext L) : LContext L :=
  { value := fun p => f p ((m p).map c.value)
    label := c.label }

/-- Run a stack of layers. -/
def lrun (m : Mask) (fs : List Combine) (c : LContext L) : LContext L :=
  fs.foldl (fun acc f => lstep m f acc) c

/-- Quarantine over a flows relation: p may attend q only if q's label flows
    into p's label. -/
def LWellMasked (flows : L → L → Prop) (m : Mask) (c : LContext L) : Prop :=
  ∀ p, ∀ q ∈ m p, flows (c.label q) (c.label p)

/-- Equivalence at observer level ℓ: labels agree everywhere; values agree at
    every position visible to ℓ (label flows into ℓ). -/
def LEq (flows : L → L → Prop) (ℓ : L) (c₁ c₂ : LContext L) : Prop :=
  (∀ p, c₁.label p = c₂.label p) ∧
  (∀ p, flows (c₁.label p) ℓ → c₁.value p = c₂.value p)

end Attnni

namespace Attnni

/-- **The generalized layer-step lemma.** With a transitive flows relation and a
    well-masked context, one layer preserves ℓ-equivalence for every observer ℓ.
    The heart: a position p visible to ℓ (label p ⊑ ℓ) reads only positions q with
    label q ⊑ label p; transitivity gives label q ⊑ ℓ, so q's values agree, so the
    read lists are equal, so f agrees — for any f. -/
theorem lstep_preserves_lEq {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (m : Mask) (f : Combine) {c₁ c₂ : LContext L}
    (hwm : LWellMasked flows m c₁) (h : LEq flows ℓ c₁ c₂) :
    LEq flows ℓ (lstep m f c₁) (lstep m f c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [lstep] at hp ⊢
  have hlists : (m p).map c₁.value = (m p).map c₂.value := by
    apply List.map_congr_left
    intro q hq
    -- q ∈ m p, p visible to ℓ; well-masked gives label q ⊑ label p; transitivity ⊑ ℓ
    have hqp : flows (c₁.label q) (c₁.label p) := hwm p q hq
    have hqℓ : flows (c₁.label q) ℓ := htrans _ _ _ hqp hp
    exact hval q hqℓ
  rw [hlists]

end Attnni

namespace Attnni

/-- Well-maskedness is preserved: labels never change. -/
theorem lstep_preserves_lWellMasked {flows : L → L → Prop}
    (m : Mask) (f : Combine) {c : LContext L}
    (hwm : LWellMasked flows m c) : LWellMasked flows m (lstep m f c) := by
  intro p q hq
  simp only [lstep] at *
  exact hwm p q hq

/-- **Multi-compartment noninterference.** For any transitive flows relation, any
    observer level ℓ, and a well-masked context, running any stack of layers (any
    weights) preserves ℓ-equivalence: positions visible to ℓ compute identical
    values across any two runs that agree at ℓ-visible positions. -/
theorem lnoninterference {flows : L → L → Prop}
    (htrans : ∀ a b c, flows a b → flows b c → flows a c)
    (ℓ : L) (m : Mask) (fs : List Combine) {c₁ c₂ : LContext L}
    (hwm : LWellMasked flows m c₁) (h : LEq flows ℓ c₁ c₂) :
    LEq flows ℓ (lrun m fs c₁) (lrun m fs c₂) := by
  unfold lrun
  induction fs generalizing c₁ c₂ with
  | nil => exact h
  | cons f fs ih =>
    exact ih (lstep_preserves_lWellMasked m f hwm)
             (lstep_preserves_lEq htrans ℓ m f hwm h)

end Attnni

#print axioms Attnni.lnoninterference
