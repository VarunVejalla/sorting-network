import Mathlib.Data.Nat.Basic

namespace Chvatal.D2TerminalBlockCounts

/-- Number of zeroes sent to the left block when two sorted Boolean blocks
of width `B` are compare-split. -/
def leftZeros (B x y : Nat) : Nat := min B (x + y)

/-- Number of zeroes sent to the right block under the same compare-split. -/
def rightZeros (B x y : Nat) : Nat := x + y - leftZeros B x y

theorem leftZeros_eq_of_sum_le {B x y : Nat} (h : x + y <= B) :
    leftZeros B x y = x + y := by
  simp [leftZeros, Nat.min_eq_right h]

theorem rightZeros_eq_zero_of_sum_le {B x y : Nat} (h : x + y <= B) :
    rightZeros B x y = 0 := by
  simp [rightZeros, leftZeros_eq_of_sum_le h]

theorem leftZeros_eq_width_of_width_le_sum {B x y : Nat} (h : B <= x + y) :
    leftZeros B x y = B := by
  simp [leftZeros, Nat.min_eq_left h]

theorem rightZeros_eq_remainder {B x y r : Nat}
    (hsum : x + y = B + r) : rightZeros B x y = r := by
  simp [rightZeros, leftZeros, hsum, Nat.min_eq_left (by omega : B <= B + r)]

/-- The even-boundary alternating pair pass canonicalizes an admissible
three-block threshold profile. -/
theorem even_boundary_two_pass
    {B r a b c : Nat}
    (ha : r <= a)
    (htotal : a + b + c = B + r) :
    leftZeros B a (leftZeros B b c) = B /\
    rightZeros B a (leftZeros B b c) = r /\
    rightZeros B b c = 0 := by
  have hbc : b + c <= B := by omega
  have hleftBC : leftZeros B b c = b + c := leftZeros_eq_of_sum_le hbc
  have hrightBC : rightZeros B b c = 0 := rightZeros_eq_zero_of_sum_le hbc
  have habc : a + (b + c) = B + r := by omega
  have hsumge : B <= a + leftZeros B b c := by rw [hleftBC]; omega
  refine ⟨leftZeros_eq_width_of_width_le_sum hsumge, ?_, hrightBC⟩
  rw [rightZeros_eq_remainder (by rw [hleftBC]; exact habc)]

/-- The odd-boundary alternating pair pass gives the same canonical profile,
with the pair order reversed. -/
theorem odd_boundary_two_pass
    {B r a b c : Nat}
    (hr : r <= B) (hc : c <= r)
    (htotal : a + b + c = B + r) :
    leftZeros B a b = B /\
    leftZeros B (rightZeros B a b) c = r /\
    rightZeros B (rightZeros B a b) c = 0 /\
    rightZeros B a b = r - c := by
  have habge : B <= a + b := by omega
  have hleftAB : leftZeros B a b = B := leftZeros_eq_width_of_width_le_sum habge
  have hrightAB : rightZeros B a b = r - c := by
    apply rightZeros_eq_remainder
    omega
  have hsecond : leftZeros B (rightZeros B a b) c = r := by
    rw [hrightAB]
    unfold leftZeros
    rw [show r - c + c = r by omega, Nat.min_eq_right hr]
  have hrightSecond : rightZeros B (rightZeros B a b) c = 0 := by
    rw [hrightAB]
    apply rightZeros_eq_zero_of_sum_le
    omega
  exact ⟨hleftAB, hsecond, hrightSecond, hrightAB⟩

end Chvatal.D2TerminalBlockCounts
