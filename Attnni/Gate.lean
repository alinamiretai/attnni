import Attnni.Model

/-!
# Attnni.Gate — the quarantine constraint and low-equivalence

The mask is *well-formed* (satisfies quarantine) when every public position
attends only to public positions. Under this constraint, no public position ever
reads a secret value, at any layer — which is exactly what makes the airgap hold.

Low-equivalence relates two contexts that agree at every public position (same
label, same value) — they may differ arbitrarily at secret positions.
-/

namespace Attnni

/-- Quarantine: every public position attends only to public positions.
    (A public position's mask contains no secret position.) -/
def WellMasked (m : Mask) (c : Context) : Prop :=
  ∀ p, c.label p = .low → ∀ q ∈ m p, c.label q = .low

/-- Low-equivalence: two contexts agree on labels everywhere, and on values at
    every low position. Secret (high) values may differ. -/
def LowEq (c₁ c₂ : Context) : Prop :=
  (∀ p, c₁.label p = c₂.label p) ∧
  (∀ p, c₁.label p = .low → c₁.value p = c₂.value p)

end Attnni
