import AKS.Bounds.Minimum
import AKS.Sort.Shrink

namespace SortingDepth

/-- Sorting-network depth is monotone in the wire count: restrict a sorter on
the larger set of wires to its first `m` wires. -/
theorem minimum_mono {m n : Nat} (hmn : m ≤ n) :
    minimum m ≤ minimum n := by
  classical
  obtain ⟨net, hsort, hdepth⟩ := Nat.find_spec (exists_sorting_depth n)
  have hrestricted : ComparatorNetwork.Sorts.{0} (net.restrictWires m hmn) :=
    restrictWires_sorts net m hmn (fun v => hsort (α := Bool) v)
  calc
    minimum m ≤ (net.restrictWires m hmn).depth := minimum_le _ hrestricted
    _ ≤ net.depth := restrictWires_depth_le _ _ _
    _ = minimum n := hdepth

/-- The fixed 4096-by-64 core divides every sufficiently large power-of-eight
wire count, so a proof on these sizes has no ragged final core tile. -/
theorem d2CoreWidth_dvd_eight_pow {d : Nat} (hd : 6 ≤ d) :
    4096 * 64 ∣ 8 ^ d := by
  have hwidth : 4096 * 64 = 8 ^ 6 := by norm_num
  rw [hwidth]
  have hd' : d = 6 + (d - 6) := by omega
  rw [hd', pow_add]
  exact ⟨8 ^ (d - 6), rfl⟩

/-- A uniform affine depth bound on the cofinal powers of eight transfers to
all sufficiently large wire counts, with the ceiling exponent `clog 8 n`.
This is the discrete padding step before converting to the logarithmic
limsup. -/
theorem minimum_le_linear_clog_of_pow8_bound
    (A B d₀ : Nat)
    (hpow : ∀ d, d₀ ≤ d → minimum (8 ^ d) ≤ A * d + B)
    {n : Nat} (hn : 8 ^ d₀ ≤ n) :
    minimum n ≤ A * Nat.clog 8 n + B := by
  have hd₀ : d₀ ≤ Nat.clog 8 n := by
    have hmono := Nat.clog_mono_right 8 hn
    rw [Nat.clog_pow 8 d₀ (by norm_num)] at hmono
    exact hmono
  have hnle : n ≤ 8 ^ Nat.clog 8 n := Nat.le_pow_clog (by norm_num) n
  calc
    minimum n ≤ minimum (8 ^ Nat.clog 8 n) := minimum_mono hnle
    _ ≤ A * Nat.clog 8 n + B := hpow (Nat.clog 8 n) hd₀

end SortingDepth
