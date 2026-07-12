import Attnni.Model
import Attnni.Gate
import Attnni.Noninterference

/-!
# Attnni.Rasp — a RASP-style surface language, and its correspondence to Model

RASP (Weiss et al. 2021) models transformer computation with two primitives:
`select` builds an attention pattern (which positions attend to which), and
`aggregate` combines the selected values. Tracr (Lindner et al. 2023) compiles
RASP to real transformer weights, so a correspondence between AttnNI's abstract
`Model` and a RASP-style layer is the bridge from the abstract theorem to real
transformers.

Here we define a minimal RASP-style layer: a `Selector` (per-position: which
positions it attends to) and an `Aggregator` (per-position: how to combine the
attended values). We then show a RASP layer *elaborates to* exactly Model's
`layerStep` — so noninterference over Model is noninterference over RASP layers.
-/

namespace Attnni

/-- A RASP selector: for each query position, the list of key positions it
    attends to. This is exactly a `Mask` — select IS the attention pattern. -/
abbrev Selector := Pos → List Pos

/-- A RASP aggregator: for each position, how to combine the list of attended
    values into a new value. This is exactly a `Combine`. -/
abbrev Aggregator := Pos → List Nat → Nat

/-- A RASP layer is a selector paired with an aggregator. -/
structure RaspLayer where
  sel : Selector
  agg : Aggregator

/-- Elaborate a RASP layer into a Model step: the selector becomes the mask, the
    aggregator becomes the combine function. -/
def RaspLayer.toStep (r : RaspLayer) (c : Context) : Context :=
  layerStep r.sel r.agg c

end Attnni


namespace Attnni

/-- Run a RASP program: a list of layers, each with its OWN selector/mask.
    (More general than Model.run, which fixes one mask across layers.) -/
def raspRun (prog : List RaspLayer) (c : Context) : Context :=
  prog.foldl (fun acc r => r.toStep acc) c

/-- A RASP program is well-masked for the public/secret lattice if EVERY layer's
    selector is well-masked: public positions attend only to public positions.
    (Labels are preserved by layerStep, so one condition per layer suffices.) -/
def RaspWellMasked (prog : List RaspLayer) (c : Context) : Prop :=
  ∀ r ∈ prog, WellMasked r.sel c

end Attnni

namespace Attnni

/-- Label preservation for a RASP step (labels never change). -/
theorem toStep_label (r : RaspLayer) (c : Context) (p : Pos) :
    (r.toStep c).label p = c.label p := rfl

/-- One RASP layer preserves low-equivalence, given its selector is well-masked.
    (Reuses the Model layer-step lemma via toStep = layerStep.) -/
theorem toStep_preserves_lowEq (r : RaspLayer) {c₁ c₂ : Context}
    (hwm : WellMasked r.sel c₁) (h : LowEq c₁ c₂) :
    LowEq (r.toStep c₁) (r.toStep c₂) :=
  layerStep_preserves_lowEq r.sel r.agg hwm h

/-- One RASP layer preserves well-maskedness (labels unchanged). -/
theorem toStep_preserves_wellMasked (r r' : RaspLayer) {c : Context}
    (hwm : WellMasked r'.sel c) : WellMasked r'.sel (r.toStep c) := by
  intro p hp q hq
  exact hwm p hp q hq

/-- **RASP noninterference.** A well-masked RASP program (every layer's selector
    quarantines public from secret) leaks nothing from secret to public — for any
    aggregators (any weights). This is AttnNI's guarantee stated over the RASP
    surface language, which Tracr compiles to real transformer weights. -/
theorem rasp_noninterference (prog : List RaspLayer) {c₁ c₂ : Context}
    (hwm : RaspWellMasked prog c₁) (h : LowEq c₁ c₂) :
    LowEq (raspRun prog c₁) (raspRun prog c₂) := by
  unfold raspRun
  induction prog generalizing c₁ c₂ with
  | nil => exact h
  | cons r rs ih =>
    apply ih
    · intro r' hr'
      exact toStep_preserves_wellMasked r r' (hwm r' (List.mem_cons_of_mem r hr'))
    · exact toStep_preserves_lowEq r (hwm r (List.mem_cons_self)) h

end Attnni

#print axioms Attnni.rasp_noninterference
