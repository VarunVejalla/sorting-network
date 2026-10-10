import AKS.Chvatal.FlowSizes7
open Chvatal
def dumpD (d : Nat) (hd : 7 ≤ d) : IO Unit := do
  for t in List.range (tf7 d + 1) do
    for l in List.range (d + 1) do
      let a := flowA7 d hd l t
      if a ≠ 0 then IO.println s!"{d} {t} {l} {a} {flowUp7 d hd l t} {flowDown7 d hd l t}"
#eval dumpD 14 (by omega)
#eval dumpD 15 (by omega)
#eval dumpD 16 (by omega)
#eval dumpD 17 (by omega)
#eval dumpD 18 (by omega)
#eval dumpD 20 (by omega)
#eval dumpD 24 (by omega)
#eval dumpD 30 (by omega)
