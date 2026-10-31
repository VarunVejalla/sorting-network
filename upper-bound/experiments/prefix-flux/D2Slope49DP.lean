import Mathlib.Data.Fin.Basic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Chvatal.D2Slope49DP

abbrev Height := Fin 65

def negSentinel : Int := -10000

/-- The shifted unary contribution to `out[0] - out[delta]`, plus one. -/
def unary (delta c h : Nat) : Int :=
  (if (17 * ((64 - c) % 64)) % 64 < h then 1 else 0) +
    (if h ≤ (17 * ((delta + 64 - c) % 64)) % 64 then 1 else 0)

/-- Suffix maxima, in one pass from right to left. -/
def suffixMax : List Int → List Int
  | [] => []
  | x :: xs =>
      let tail := suffixMax xs
      match tail with
      | [] => [x]
      | y :: _ => max x y :: tail

/-- Advance one position in the max-plus DP. The profile constraint is
`nextHeight <= previousHeight + 1`. -/
def step (delta c : Nat) (dp : List Int) : List Int :=
  let suffix := suffixMax dp
  let prior := suffix.headD negSentinel :: suffix.take 64
  List.zipWith (fun h best => unary delta c h + best)
    (List.range 65) prior

def initial (delta start : Nat) : List Int :=
  List.ofFn fun h : Height =>
    if h.val = start then unary delta 0 start else negSentinel

def dpAfter (delta start : Nat) : List Int :=
  (List.range 63).foldl
    (fun dp k => step delta ((35 * (k + 1)) % 64) dp)
    (initial delta start)

def closedMaximum (start : Nat) (dp : List Int) : Int :=
  (List.range 65).foldl
    (fun best last =>
      if start ≤ last + 1 then max best (dp.getD last negSentinel) else best)
    negSentinel

def dpBoundFor (delta : Nat) : Bool :=
  (List.range 65).all fun start =>
    decide (closedMaximum start (dpAfter delta start) ≤ 77)

theorem dpBound_delta_1 : dpBoundFor 1 = true := by
  unfold dpBoundFor
  decide

end Chvatal.D2Slope49DP
