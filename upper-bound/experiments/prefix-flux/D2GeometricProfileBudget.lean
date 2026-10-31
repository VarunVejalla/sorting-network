import Lean

namespace Chvatal.D2GeometricProfileBudget

/-- If the number of profile tiles doubles at each stage, and the aggregate
profile error gains at most 448 units per input tile, then a 512-per-tile
initial allowance sharpens to 448 per current tile plus a fixed startup term.
This is the all-time arithmetic closure for the one-step `448 * tiles`
transfer; it does not assert that the actual D2 schedule realizes that
transfer. -/
theorem error_le_448_tiles_add_initial_allowance
    (tiles error : Nat → Nat)
    (hdouble : ∀ t, tiles (t + 1) = 2 * tiles t)
    (hinitial : error 0 ≤ 512 * tiles 0)
    (hstep : ∀ t, error (t + 1) ≤ error t + 448 * tiles t) :
    ∀ t, error t ≤ 448 * tiles t + 64 * tiles 0 := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
      rw [hdouble t]
      calc
        error (t + 1) ≤ error t + 448 * tiles t := hstep t
        _ ≤ (448 * tiles t + 64 * tiles 0) + 448 * tiles t := by omega
        _ = 448 * (2 * tiles t) + 64 * tiles 0 := by omega

/-- After six tile doublings, the fixed startup allowance is at most one unit
per current tile, so the aggregate profile error is at most 449 per tile. -/
theorem error_le_449_tiles_after_six
    (tiles error : Nat → Nat)
    (hdouble : ∀ t, tiles (t + 1) = 2 * tiles t)
    (hinitial : error 0 ≤ 512 * tiles 0)
    (hstep : ∀ t, error (t + 1) ≤ error t + 448 * tiles t) :
    ∀ t, 6 ≤ t → error t ≤ 449 * tiles t := by
  have hbase : tiles 6 = 64 * tiles 0 := by
    calc
      tiles 6 = 2 * tiles 5 := hdouble 5
      _ = 2 * (2 * tiles 4) := by rw [hdouble 4]
      _ = 2 * (2 * (2 * tiles 3)) := by rw [hdouble 3]
      _ = 2 * (2 * (2 * (2 * tiles 2))) := by rw [hdouble 2]
      _ = 2 * (2 * (2 * (2 * (2 * tiles 1)))) := by rw [hdouble 1]
      _ = 2 * (2 * (2 * (2 * (2 * (2 * tiles 0))))) := by rw [hdouble 0]
      _ = 64 * tiles 0 := by omega
  have hgrowth : ∀ k, 64 * tiles 0 ≤ tiles (k + 6) := by
    intro k
    induction k with
    | zero => rw [hbase]; exact Nat.le_refl _
    | succ k ih =>
        have hnext : k + 1 + 6 = (k + 6) + 1 := by omega
        rw [hnext, hdouble (k + 6)]
        omega
  intro t ht
  have herror := error_le_448_tiles_add_initial_allowance
    tiles error hdouble hinitial hstep t
  have htdecomp : (t - 6) + 6 = t := Nat.sub_add_cancel ht
  have hlarge : 64 * tiles 0 ≤ tiles t := by
    rw [← htdecomp]
    exact hgrowth (t - 6)
  calc
    error t ≤ 448 * tiles t + 64 * tiles 0 := herror
    _ ≤ 448 * tiles t + tiles t := Nat.add_le_add_left hlarge _
    _ = 449 * tiles t := by omega

end Chvatal.D2GeometricProfileBudget
