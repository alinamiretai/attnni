import Attnni.Model
import Attnni.Gate
import Attnni.Noninterference

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

namespace Attnni

/-- **The audit-window bridge.** If every position outside the audited list is
    labeled high (the conservative encoding of "the real context is finite"),
    then bounded well-maskedness implies full well-maskedness: outside the
    window the condition is vacuous (only low positions are constrained), and
    inside it the checker covered it. -/
theorem wellMaskedOn_to_wellMasked {m : Mask} {c : Context} {ps : List Pos}
    (hout : ∀ p, p ∉ ps → c.label p = .high)
    (hon : WellMaskedOn m c ps) : WellMasked m c := by
  intro p hlow q hq
  by_cases hp : p ∈ ps
  · exact hon p hp hlow q hq
  · exact absurd hlow (by rw [hout p hp]; simp)

/-- **End-to-end controller guarantee.** If the controller executed (didn't fall
    back) and the context is high outside the audit window, then the executed
    run is fully well-masked — so the noninterference theorem applies to it:
    the output at low positions is identical across secret variations. -/
theorem controller_noninterference (m : Mask) (fs : List Combine)
    {c₁ c₂ : Context} (ps : List Pos) (fallback : Context)
    (hout : ∀ p, p ∉ ps → c₁.label p = .high)
    (hran : controller m fs c₁ ps fallback ≠ fallback)
    (h : LowEq c₁ c₂) :
    LowEq (run m fs c₁) (run m fs c₂) :=
  noninterference m fs
    (wellMaskedOn_to_wellMasked hout (controller_runs_only_wellMasked m fs c₁ ps fallback hran))
    h

end Attnni

#print axioms Attnni.controller_noninterference
