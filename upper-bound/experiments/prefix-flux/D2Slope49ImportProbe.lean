import D2Slope49Abstract
import D2Slope49Certificate61

#check Chvatal.D2Slope49Abstract.suffix_table_le_potential

open scoped BigOperators

namespace Chvatal.D2Slope49ImportProbe

open Chvatal.D2Slope49Abstract
open Chvatal.D2Slope49Certificate61

theorem delta61_edge_inequality (layer : Fin 64) (current previous : Fin 65)
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
  exact dual_edge_of_suffix_certificate
    (fun t => unary layer.val t.val)
    budgets[layer.val]!
    (fun h => (potentials[layer.val]!)[h]!)
    (fun h => (potentials[prior.val]!)[h]!)
    (fun h => (suffixes[prior.val]!)[h]!)
    hstep hend hlocal current previous htransition

end Chvatal.D2Slope49ImportProbe
