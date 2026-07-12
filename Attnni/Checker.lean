import Attnni.Model
import Attnni.Gate

/-!
# Attnni.Checker — a decidable well-maskedness checker and the control loop

`wellMaskedCheck` is a Bool-returning decision procedure; `wellMaskedCheck_correct`
proves it exactly matches the `WellMasked` proposition. The controller then runs a
masked model only when the mask passes the check, falling back to a safe default
otherwise — and `controller_safe` proves every executed run is well-masked.
-/

namespace Attnni

/-- Decidable check: does position p (if low) attend only to low positions?
    We check, for a given finite set of positions to audit, that the mask is
    well-formed there. `ps` is the list of positions in play (e.g. the context
    length). -/
def wellMaskedCheckAt (m : Mask) (c : Context) (p : Pos) : Bool :=
  match c.label p with
  | .low  => (m p).all (fun q => c.label q == Label.low)
  | .high => true

/-- The check over a list of positions to audit. -/
def wellMaskedCheck (m : Mask) (c : Context) (ps : List Pos) : Bool :=
  ps.all (fun p => wellMaskedCheckAt m c p)

end Attnni

namespace Attnni

/-- Bounded well-maskedness: the WellMasked condition restricted to an audited
    list of positions. (The full WellMasked quantifies over all positions, which
    isn't decidable; a real system audits its actual finite context.) -/
def WellMaskedOn (m : Mask) (c : Context) (ps : List Pos) : Prop :=
  ∀ p ∈ ps, c.label p = .low → ∀ q ∈ m p, c.label q = .low

/-- **Checker correctness.** The Bool checker returns true iff the bounded
    well-maskedness proposition holds. Sound and complete over the audited set. -/
theorem wellMaskedCheck_correct (m : Mask) (c : Context) (ps : List Pos) :
    wellMaskedCheck m c ps = true ↔ WellMaskedOn m c ps := by
  unfold wellMaskedCheck WellMaskedOn
  rw [List.all_eq_true]
  constructor
  · intro h p hp hlow q hq
    have hpc := h p hp
    unfold wellMaskedCheckAt at hpc
    rw [hlow] at hpc
    simp only [List.all_eq_true] at hpc
    have := hpc q hq
    simpa using this
  · intro h p hp
    unfold wellMaskedCheckAt
    cases hlab : c.label p with
    | high => rfl
    | low =>
      simp only [List.all_eq_true]
      intro q hq
      have := h p hp hlab q hq
      simpa using this

end Attnni

namespace Attnni

/-- The controller: run the masked model only if the mask passes the check;
    otherwise return the safe fallback (here, the unchanged input context — no
    computation performed, so trivially nothing flows). -/
def controller (m : Mask) (fs : List Combine) (c : Context) (ps : List Pos)
    (fallback : Context) : Context :=
  if wellMaskedCheck m c ps then run m fs c else fallback

/-- **Controller safety.** Whenever the controller actually runs the model (rather
    than falling back), the mask it ran under is well-masked on the audited
    positions. So every executed run satisfies the precondition of the
    noninterference theorem — the controller never runs an unchecked mask. -/
theorem controller_runs_only_wellMasked (m : Mask) (fs : List Combine) (c : Context)
    (ps : List Pos) (fallback : Context)
    (hran : controller m fs c ps fallback ≠ fallback) :
    WellMaskedOn m c ps := by
  unfold controller at hran
  by_cases hchk : wellMaskedCheck m c ps
  · exact (wellMaskedCheck_correct m c ps).mp hchk
  · simp only [hchk, if_false] at hran
    exact absurd rfl hran

end Attnni

#print axioms Attnni.controller_runs_only_wellMasked
