import AKS.Chvatal.FlowSizes7

/-! Finite diagnostic only: list all remainders of nonzero next-stage receiver
packet counts for dimensions 7 through 40. This is not a uniform theorem. -/

open Chvatal

def packetResidues (d : Nat) (hd : 7 ≤ d) : List Nat := Id.run do
  let mut out := []
  for t in List.range (tf7 d) do
    if 2 ≤ t then
      for l in List.range d do
        let m := flowA7 d hd l (t + 1) / 64
        if m > 0 then out := m % 64 :: out
  return out

#eval (List.range 34).map fun k =>
  let d := k + 7
  let rs := packetResidues d (by omega)
  (d, rs.length, rs.eraseDups.mergeSort (· ≤ ·))
