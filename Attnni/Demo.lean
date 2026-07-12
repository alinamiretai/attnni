import Attnni.Model
import Attnni.Gate
import Attnni.Checker

/-!
# Attnni.Demo — the airgap, concretely

A 3-position context:
  position 0 : PUBLIC  (the visible output stream)
  position 1 : PUBLIC  (some public input)
  position 2 : SECRET  (the thing that must not leak)

A well-formed mask lets position 0 attend to {0,1} (public only). We run a
concrete layer (sum of attended values) and show: flipping the SECRET at
position 2 leaves position 0's output UNCHANGED. Then we corrupt the mask so
position 0 attends to the secret, and watch the checker reject it.
-/

namespace Attnni

-- Labels: positions 0,1 public; position 2 secret.
def demoLabel : Pos → Label
  | 0 => .low
  | 1 => .low
  | 2 => .high
  | _ => .high        -- everything else: high (outside the window)

-- A well-formed mask: public position 0 attends to {0,1} only (no secret).
def goodMask : Mask
  | 0 => [0, 1]
  | 1 => [1]
  | 2 => [0, 1, 2]    -- the secret position may read anything; it's not public
  | _ => []

-- A BROKEN mask: position 0 now also attends to the secret (2). Quarantine violated.
def badMask : Mask
  | 0 => [0, 1, 2]
  | 1 => [1]
  | 2 => [0, 1, 2]
  | _ => []

-- A concrete layer: each position's new value = sum of the values it attends to.
def sumLayer : Combine := fun _ vs => vs.foldl (· + ·) 0

-- Two contexts identical on public data, differing only in the SECRET (pos 2).
def ctx_secretA : Context := { value := fun p => if p == 2 then 42 else p, label := demoLabel }
def ctx_secretB : Context := { value := fun p => if p == 2 then 999 else p, label := demoLabel }

-- The audited positions (the finite context window).
def demoPositions : List Pos := [0, 1, 2]

-- === The airgap, under the GOOD mask ===
-- Position 0's output after one sumLayer, with secret = 42 vs secret = 999.
-- These MUST be equal: position 0 never attends to the secret.
#eval (run goodMask [sumLayer] ctx_secretA).value 0   -- expect: 0 + 1 = 1
#eval (run goodMask [sumLayer] ctx_secretB).value 0   -- expect: 0 + 1 = 1  (SAME)

-- Sanity: the SECRET position itself DOES differ (it's allowed to).
#eval (run goodMask [sumLayer] ctx_secretA).value 2   -- 0+1+42 = 43
#eval (run goodMask [sumLayer] ctx_secretB).value 2   -- 0+1+999 = 1000 (differs, fine)

-- === The checker bites the BAD mask ===
#eval wellMaskedCheck goodMask ctx_secretA demoPositions   -- expect: true
#eval wellMaskedCheck badMask  ctx_secretA demoPositions   -- expect: false (pos 0 reads secret)

-- === The controller falls back on the bad mask ===
-- With the good mask it runs; with the bad mask it returns the fallback unchanged.
#eval (controller goodMask [sumLayer] ctx_secretA demoPositions ctx_secretA).value 0  -- ran: 1
#eval (controller badMask  [sumLayer] ctx_secretA demoPositions ctx_secretB).value 0  -- fell back to ctx_secretB: value 0 = 0

end Attnni
