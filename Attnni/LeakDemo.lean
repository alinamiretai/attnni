import Attnni.Model
import Attnni.Gate
import Attnni.Dynamic

/-!
# Attnni.LeakDemo — why LowSound is necessary (the implicit-flow channel, made visible)

`dyn_noninterference` requires the mask generator to be `LowSound`. This file shows
the theorem is FALSE without it: a generator whose public attention pattern depends
on a secret leaks that secret, even though no secret VALUE is ever read directly.
The leak is an *implicit flow* — through the choice of which positions to attend to.
-/

namespace Attnni

-- 3 positions: 0 public (the output), 1 public, 2 SECRET.
def leakLabel : Pos → Label
  | 2 => .high
  | _ => .low

-- Two contexts, low-equivalent (identical public data), differing ONLY in the
-- secret at position 2: one even (42), one odd (43).
def ctxEven : Context := { value := fun p => if p == 2 then 42 else 0, label := leakLabel }
def ctxOdd  : Context := { value := fun p => if p == 2 then 43 else 0, label := leakLabel }

-- These are low-equivalent: same labels, same low values (all 0), secret differs.
-- (Position 2's value 42 vs 43 is high, so LowEq permits the difference.)

-- A MALICIOUS generator: the public output position 0 attends to the SECRET (2)
-- only when the secret is even. Its attention PATTERN depends on the secret — so it
-- is NOT low-sound. (Public position 0's mask differs between ctxEven and ctxOdd.)
def leakyGen : MaskGen := fun c =>
  fun p =>
    if p == 0 then
      (match c.value 2 % 2 with
       | 0 => [2]      -- secret even: attend to the secret
       | _ => [])      -- secret odd: don't
    else [1]

-- A layer that sums attended values.
def sumL : Combine := fun _ vs => vs.foldl (· + ·) 0

-- === The leak ===
-- Public output (position 0) after one dynamic step, on two contexts that differ
-- ONLY in the secret. If the theorem held without low-soundness, these would match.
#eval (dynRun leakyGen [sumL] ctxEven).value 0   -- secret even: reads secret 42 -> 42
#eval (dynRun leakyGen [sumL] ctxOdd).value 0    -- secret odd: reads nothing   -> 0

-- 42 vs 0: the PUBLIC output differs based on the SECRET's parity. An observer
-- watching position 0 learns whether the secret is even — a leak — even though the
-- secret's VALUE (42/43) was never directly placed in the public stream. This is
-- the implicit flow, and it is exactly what `LowSound` forbids: leakyGen is not
-- low-sound, so `dyn_noninterference` does not apply, and indeed noninterference
-- FAILS. The hypothesis is necessary, not decorative.

end Attnni
