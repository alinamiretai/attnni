/-!
# Attnni.Model — abstract layered dataflow for attention noninterference

The smallest model of a transformer's *information flow* that can state
noninterference. We do NOT model tensor arithmetic — noninterference is about
which positions can influence which, so we abstract every computation to an
opaque combining function and track only the dataflow structure.

A context is a vector of positions, each carrying a value and a security label
(low = public, high = secret). A layer updates every position from the values it
is permitted to attend to. The mask is the policy: which positions each position
may read. The quarantine constraint (Gate.lean) forbids public positions from
attending to secret positions. The theorem (Noninterference.lean) proves that
under that constraint, public outputs are identical regardless of secret content.

Design rule (as in LowEq): every entity is carried through a relational proof, so
the model is deliberately minimal.
-/

namespace Attnni

/-- Security labels: low = public, high = secret. -/
inductive Label where
  | low | high
  deriving DecidableEq, Repr

/-- Positions are indexed by Nat. -/
abbrev Pos := Nat

/-- A context: for each position, its current value and its (fixed) label.
    Values are Nat — an opaque payload; the proof never inspects them
    arithmetically, only tracks equality. -/
structure Context where
  value : Pos → Nat
  label : Pos → Label

/-- A mask: for each position, the list of positions it may attend to.
    (A layer at position p may read value q only if q ∈ mask p.) -/
abbrev Mask := Pos → List Pos

/-- The per-layer update is abstracted as an opaque combining function: given a
    position and the list of values it is permitted to read, it produces the new
    value. Modeling it as an arbitrary function is the key strength — the theorem
    holds for ANY such function, i.e. for any weights/computation, because the
    guarantee is about which inputs the function receives, not what it computes. -/
abbrev Combine := Pos → List Nat → Nat

/-- One layer step under mask `m` and combining function `f`: every position's
    new value is `f p (values it may read)`. Labels are unchanged. -/
def layerStep (m : Mask) (f : Combine) (c : Context) : Context :=
  { value := fun p => f p ((m p).map c.value)
    label := c.label }

/-- Run a stack of layers. Each layer has its own combining function; the mask is
    fixed across layers (a fixed quarantine structure). -/
def run (m : Mask) (fs : List Combine) (c : Context) : Context :=
  fs.foldl (fun acc f => layerStep m f acc) c

end Attnni
