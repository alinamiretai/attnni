import Attnni.Model
import Attnni.Gate

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

namespace Attnni

/-- The two-point lattice as a flows relation: low flows anywhere, high only to
    high. `flowsLH a b` means "a may flow to b". -/
def flowsLH (a b : Label) : Prop := a = .low ∨ b = .high

theorem flowsLH_trans : ∀ a b c, flowsLH a b → flowsLH b c → flowsLH a c := by
  intro a b c hab hbc
  cases a <;> cases b <;> cases c <;>
    simp_all [flowsLH]

/-- Sanity check: `flowsLH x low` holds iff x is low (secrets cannot flow to a
    low observer). This is why observer ℓ = low recovers confidentiality. -/
theorem flowsLH_to_low (x : Label) : flowsLH x .low ↔ x = .low := by
  cases x <;> simp [flowsLH]

end Attnni

namespace Attnni

/-- Convert an original Context into a labeled context over `Label`. -/
def toLContext (c : Context) : LContext Label :=
  { value := c.value, label := c.label }

/-- The original WellMasked implies the lattice WellMasked under flowsLH:
    if public positions attend only to public, then every attended pair satisfies
    flowsLH (attended label flows to attender label). -/
theorem wellMasked_toLContext {m : Mask} {c : Context}
    (hwm : WellMasked m c) : LWellMasked flowsLH m (toLContext c) := by
  intro p q hq
  show flowsLH (c.label q) (c.label p)
  simp only [flowsLH]
  by_cases hp : c.label p = .low
  · exact Or.inl (hwm p hp q hq)
  · right
    cases hpl : c.label p with
    | low => exact absurd hpl hp
    | high => rfl

/-- The original LowEq implies lattice LEq at observer low. -/
theorem lowEq_toLContext {c₁ c₂ : Context} (h : LowEq c₁ c₂) :
    LEq flowsLH .low (toLContext c₁) (toLContext c₂) := by
  obtain ⟨hlab, hval⟩ := h
  refine ⟨fun p => hlab p, fun p hp => ?_⟩
  simp only [toLContext] at *
  -- hp : flowsLH (c₁.label p) low, which gives c₁.label p = low
  rw [flowsLH_to_low] at hp
  exact hval p hp

end Attnni

namespace Attnni

/-- lrun preserves labels (layers never change labels). -/
theorem lrun_label (m : Mask) (fs : List Combine) (c : LContext L) (p : Pos) :
    (lrun m fs c).label p = c.label p := by
  unfold lrun
  induction fs generalizing c with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons]; rw [ih]; rfl

/-- **The original two-label confidentiality guarantee, as a corollary of
    multi-compartment noninterference.** Instantiating the general theorem at the
    two-point lattice (flowsLH) with observer `low` recovers: under a well-masked
    context, low positions compute identical values across runs differing only in
    secrets — for any weights. This shows the general theorem subsumes the
    original airgap. -/
theorem noninterference_via_lattice (m : Mask) (fs : List Combine) {c₁ c₂ : Context}
    (hwm : WellMasked m c₁) (h : LowEq c₁ c₂) (p : Pos)
    (hp : c₁.label p = .low) :
    (lrun m fs (toLContext c₁)).value p = (lrun m fs (toLContext c₂)).value p := by
  have hgen := lnoninterference flowsLH_trans .low m fs
                 (wellMasked_toLContext hwm) (lowEq_toLContext h)
  have hlab : (lrun m fs (toLContext c₁)).label p = .low := by
    rw [lrun_label]; exact hp
  exact hgen.2 p ((flowsLH_to_low _).mpr hlab)

end Attnni

#print axioms Attnni.noninterference_via_lattice
