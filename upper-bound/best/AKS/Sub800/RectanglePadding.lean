import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace Tapered945

/-- A nearby rectangle with bounded row count and a power-of-two column count.
The padding is strictly less than one row. For counts below this threshold,
a fixed-size exact sorter can be used instead. -/
theorem nearby_rectangle (a : Nat) (ha : 2 ^ 38 ≤ a) :
    ∃ m n : Nat, (∃ e : Nat, n = 2 ^ e) ∧ 16 ≤ n ∧
      2 ^ 34 ≤ m ∧ m ≤ 2 ^ 35 ∧ a ≤ m * n ∧ m * n - a < n := by
  let e := Nat.log 2 a - 34
  let n := 2 ^ e
  let m := (a + n - 1) / n
  have halog : 38 ≤ Nat.log 2 a := Nat.le_log_of_pow_le (by norm_num) ha
  have he : 4 ≤ e := by dsimp [e]; omega
  have hn : 0 < n := by dsimp [n]; positivity
  have hn16 : 16 ≤ n := by
    calc
      16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hexp : e + 34 = Nat.log 2 a := by dsimp [e]; omega
  have hlo : 2 ^ 34 * n ≤ a := by
    have h := Nat.pow_log_le_self 2 (by omega : a ≠ 0)
    calc
      2 ^ 34 * n = 2 ^ (e + 34) := by dsimp [n]; rw [pow_add]; ring
      _ = 2 ^ Nat.log 2 a := by rw [hexp]
      _ ≤ a := h
  have hhi : a < 2 ^ 35 * n := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
    calc
      a < 2 ^ (Nat.log 2 a + 1) := h
      _ = 2 ^ (e + 35) := by congr 1; omega
      _ = 2 ^ 35 * n := by dsimp [n]; rw [pow_add]; ring
  have hdiv := Nat.mod_add_div (a + n - 1) n
  have hmod := Nat.mod_lt (a + n - 1) hn
  have hmn : a ≤ m * n ∧ m * n < a + n := by
    have hprod : n * ((a + n - 1) / n) = m * n := by dsimp [m]; ring
    rw [hprod] at hdiv
    omega
  have hmlo : 2 ^ 34 ≤ m := by
    have hd : 2 ^ 34 ≤ a / n := by
      exact (Nat.le_div_iff_mul_le hn).mpr hlo
    have hmon : a / n ≤ m := Nat.div_le_div_right (by omega : a ≤ a + n - 1)
    exact hd.trans hmon
  have hmhi : m ≤ 2 ^ 35 := by
    by_contra h
    have hmul : (2 ^ 35 + 1) * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  exact ⟨m, n, ⟨e, rfl⟩, hn16, hmlo, hmhi, hmn.1, by omega⟩

end Tapered945
