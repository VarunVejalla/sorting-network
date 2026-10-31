#!/usr/bin/env python3
"""Emit a small, standalone Lean checker for one exact dual certificate."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).parent
certs = json.loads((HERE / "d2_slope25_potentials.json").read_text(encoding="utf-8"))
delta = int(sys.argv[1]) if len(sys.argv) > 1 else 61
cert = certs[delta]


def int_array(values):
    return "#[" + ",".join(f"({int(x)} : Int)" for x in values) + "]"


suffixes = []
for row in cert["potentials"]:
    suffix = [0] * len(row)
    suffix[-1] = int(row[-1])
    for h in range(len(row) - 2, -1, -1):
        suffix[h] = min(int(row[h]), suffix[h + 1])
    suffixes.append(suffix)

potentials = "#[" + ",\n".join(int_array(row) for row in cert["potentials"]) + "]"
suffix_table = "#[" + ",\n".join(int_array(row) for row in suffixes) + "]"
budgets = int_array(cert["budgets"])

source = f'''import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import D2Slope25Abstract

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Chvatal.D2Slope25Certificate{delta}

def potentials : Array (Array Int) := {potentials}
def suffixes : Array (Array Int) := {suffix_table}
def budgets : Array Int := {budgets}

def unary (layer height : Nat) : Int :=
  (if (41 * ((64 - (35 * layer) % 64) % 64)) % 64 < height then 1 else 0) +
    (if height ≤ (41 * (({delta} + 64 - (35 * layer) % 64) % 64)) % 64 then 1 else 0)

def suffixStepCheck (layer height : Nat) : Bool :=
  if height < 64 then
    decide ((suffixes[layer]!)[height]! =
      min ((potentials[layer]!)[height]!) ((suffixes[layer]!)[height + 1]!))
  else decide ((suffixes[layer]!)[64]! = (potentials[layer]!)[64]!)

def localCheck (layer current : Nat) : Bool :=
  let threshold := if current = 0 then 0 else current - 1
  decide (unary layer current ≤
    budgets[layer]! + (suffixes[(layer + 63) % 64]!)[threshold]! - (potentials[layer]!)[current]!)

def layerCheck (layer : Nat) : Bool :=
  (List.range 65).all (suffixStepCheck layer) &&
  (List.range 65).all (localCheck layer)

'''

for layer in range(64):
    source += f'''theorem certificate_layer_{layer} : layerCheck {layer} = true := by
  unfold layerCheck
  decide

'''

source += '''theorem certificate_layer_all (layer : Fin 64) :
    layerCheck layer.val = true := by
  fin_cases layer
'''
for layer in range(64):
    source += f"  · exact certificate_layer_{layer}\n"

source += '''
theorem suffix_step_check_all (layer : Fin 64) (height : Fin 65) :
    suffixStepCheck layer.val height.val = true := by
  have h := certificate_layer_all layer
  have hparts :
      (List.range 65).all (suffixStepCheck layer.val) = true ∧
      (List.range 65).all (localCheck layer.val) = true := by
    simpa [layerCheck, Bool.and_eq_true] using h
  have hall := (List.all_eq_true.mp hparts.1) height.val (by simp)
  exact hall

theorem local_check_all (layer : Fin 64) (current : Fin 65) :
    localCheck layer.val current.val = true := by
  have h := certificate_layer_all layer
  have hparts :
      (List.range 65).all (suffixStepCheck layer.val) = true ∧
      (List.range 65).all (localCheck layer.val) = true := by
    simpa [layerCheck, Bool.and_eq_true] using h
  exact (List.all_eq_true.mp hparts.2) current.val (by simp)

theorem suffix_step_eq (layer : Fin 64) (height : Fin 65)
    (hh : height.val < 64) :
    (suffixes[layer.val]!)[height.val]! =
      min ((potentials[layer.val]!)[height.val]!)
        ((suffixes[layer.val]!)[height.val + 1]!) := by
  have h := suffix_step_check_all layer height
  unfold suffixStepCheck at h
  simp only [if_pos hh] at h
  exact of_decide_eq_true h

theorem suffix_terminal_eq (layer : Fin 64) :
    (suffixes[layer.val]!)[64]! = (potentials[layer.val]!)[64]! := by
  have h := suffix_step_check_all layer ⟨64, by omega⟩
  unfold suffixStepCheck at h
  simp only [if_neg (by omega : ¬ 64 < 64)] at h
  exact of_decide_eq_true h

theorem unary_local_ineq (layer : Fin 64) (current : Fin 65) :
    unary layer.val current.val ≤
      budgets[layer.val]! +
        (suffixes[(layer.val + 63) % 64]!)[if current.val = 0 then 0 else current.val - 1]! -
          (potentials[layer.val]!)[current.val]! := by
  have h := local_check_all layer current
  unfold localCheck at h
  exact of_decide_eq_true h

'''

source += f'''end Chvatal.D2Slope25Certificate{delta}
'''
source = source.replace(
    f"end Chvatal.D2Slope25Certificate{delta}\n",
    f'''theorem delta_edge_inequality (layer : Fin 64) (current previous : Fin 65)
    (htransition : current.val ≤ previous.val + 1) :
    unary layer.val current.val ≤
      budgets[layer.val]! +
        (potentials[(layer.val + 63) % 64]!)[previous.val]! -
          (potentials[layer.val]!)[current.val]! := by
  let prior : Fin 64 := ⟨(layer.val + 63) % 64, Nat.mod_lt _ (by omega)⟩
  have hstep : ∀ h, h < 64 →
      (suffixes[prior.val]!)[h]! =
        min ((potentials[prior.val]!)[h]!) ((suffixes[prior.val]!)[h + 1]!) := by
    intro h hh
    have hs := suffix_step_eq prior ⟨h, by omega⟩ hh
    simpa using hs
  have hend : (suffixes[prior.val]!)[64]! = (potentials[prior.val]!)[64]! := by
    simpa using suffix_terminal_eq prior
  have hlocal : ∀ t : Fin 65,
      unary layer.val t.val ≤
        budgets[layer.val]! +
          (suffixes[prior.val]!)[if t.val = 0 then 0 else t.val - 1]! -
            (potentials[layer.val]!)[t.val]! := by
    intro t
    simpa using unary_local_ineq layer t
  exact Chvatal.D2Slope25Abstract.dual_edge_of_suffix_certificate
    (fun t => unary layer.val t.val)
    budgets[layer.val]!
    (fun h => (potentials[layer.val]!)[h]!)
    (fun h => (potentials[prior.val]!)[h]!)
    (fun h => (suffixes[prior.val]!)[h]!)
    hstep hend hlocal current previous htransition

end Chvatal.D2Slope25Certificate{delta}
''')
out = HERE / f"D2Slope25Certificate{delta:02}.lean"
out.write_text(source, encoding="utf-8")
print(f"wrote {out.name}: {len(source)} bytes")
