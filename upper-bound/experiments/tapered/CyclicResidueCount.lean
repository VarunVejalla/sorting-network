import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Nat

namespace Tapered945

set_option maxHeartbeats 500000

/-- In a contiguous interval of length `h`, one residue class mod 16 occurs
at most `ceil(h/16)` times. -/
theorem card_residue_in_range_le (h a residue : Nat) :
    ((Finset.range h).filter (fun t => (a+t)%16 = residue)).card * 16 ≤ h+15 := by
  classical
  let s := (Finset.range h).filter (fun t => (a+t)%16 = residue)
  have hcard : s.card ≤ (Finset.range ((h+15)/16)).card := by
    refine Finset.card_le_card_of_injOn (fun t => t/16) ?_ ?_
    · intro t ht
      have ht' : t < h := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
      have htdecomp := Nat.mod_add_div t 16
      have hhdecomp := Nat.mod_add_div (h+15) 16
      have hrem : (h+15)%16 < 16 := Nat.mod_lt _ (by norm_num)
      have hblock : h ≤ ((h+15)/16)*16 := by omega
      have htblock : (t/16)*16 ≤ t := Nat.div_mul_le_self t 16
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 16)]
      omega
    · intro x hx y hy heq
      have hx' : x < h := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hy' : y < h := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
      have hres : (a+x)%16 = (a+y)%16 := by
        rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
      have hmod : x%16 = y%16 := by
        rw [Nat.add_mod, Nat.add_mod] at hres
        omega
      have hdiv : x/16 = y/16 := heq
      have ex := Nat.mod_add_div x 16
      have ey := Nat.mod_add_div y 16
      omega
  simp only [s, Finset.card_range] at hcard
  omega

/-- The same residue bound on any translated interval of length `h`. -/
theorem card_residue_in_Ico_le (L h a residue : Nat) :
    ((Finset.Ico L (L+h)).filter (fun t => (a+t)%16 = residue)).card * 16 ≤ h+15 := by
  classical
  let s := (Finset.Ico L (L+h)).filter (fun t => (a+t)%16 = residue)
  have hcard : s.card ≤ (Finset.range ((h+15)/16)).card := by
    refine Finset.card_le_card_of_injOn (fun t => (t-L)/16) ?_ ?_
    · intro t ht
      have htlo : L ≤ t := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).1
      have hthi : t < L+h := (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).2
      have hlen : t-L < h := by omega
      have hdecomp := Nat.mod_add_div (t-L) 16
      have hhdecomp := Nat.mod_add_div (h+15) 16
      have hrem : (h+15)%16 < 16 := Nat.mod_lt _ (by norm_num)
      have hblock : h ≤ ((h+15)/16)*16 := by omega
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 16)]
      have hdiv : ((t-L)/16)*16 ≤ t-L := Nat.div_mul_le_self _ _
      omega
    · intro x hx y hy heq
      have hxlo : L ≤ x := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).1
      have hylo : L ≤ y := (Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).1
      have hres : (a+x)%16 = (a+y)%16 := by
        rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2]
      have hmodxy : x%16 = y%16 := by
        rw [Nat.add_mod, Nat.add_mod] at hres
        omega
      have hmod : (x-L)%16 = (y-L)%16 := by
        have hx : L + (x-L) = x := Nat.add_sub_of_le hxlo
        have hy : L + (y-L) = y := Nat.add_sub_of_le hylo
        rw [← hx, ← hy, Nat.add_mod, Nat.add_mod] at hmodxy
        omega
      have hdiv : (x-L)/16 = (y-L)/16 := heq
      have ex := Nat.mod_add_div (x-L) 16
      have ey := Nat.mod_add_div (y-L) 16
      omega
  simp only [s, Nat.card_Ico, Finset.card_range] at hcard
  omega

end Tapered945
