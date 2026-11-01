import D2ClippedFlowProfileTransfer

open scoped BigOperators

namespace Chvatal.D2ClippedTilePrefixAllocation

open Chvatal.D2ClippedFlowProfileTransfer
open Chvatal.D2RankAlignment

theorem prefixIntervalMass_eq_min_sub_min
    (H lo hi : Nat) (hlo : lo <= hi) :
    prefixIntervalMass H lo hi = min H hi - min H lo := by
  by_cases hHlo : H <= lo
  · have hHhi : H <= hi := le_trans hHlo hlo
    have hsub : H - lo = 0 := Nat.sub_eq_zero_of_le hHlo
    simp [prefixIntervalMass, hsub, Nat.min_eq_left hHlo,
      Nat.min_eq_left hHhi]
  · have hloH : lo <= H := by omega
    by_cases hHhi : H <= hi
    · have hwidth : H - lo <= hi - lo := by omega
      simp [prefixIntervalMass, Nat.min_eq_left hwidth,
        Nat.min_eq_left hHhi, Nat.min_eq_right hloH]
    · have hhiH : hi <= H := by omega
      have hwidth : hi - lo <= H - lo := by omega
      simp [prefixIntervalMass, Nat.min_eq_right hwidth,
        Nat.min_eq_right hhiH, Nat.min_eq_right hloH]

theorem prefixIntervalMass_add
    (H lo mid hi : Nat) (hlm : lo <= mid) (hmh : mid <= hi) :
    prefixIntervalMass H lo mid + prefixIntervalMass H mid hi =
      prefixIntervalMass H lo hi := by
  rw [prefixIntervalMass_eq_min_sub_min H lo mid hlm,
    prefixIntervalMass_eq_min_sub_min H mid hi hmh,
    prefixIntervalMass_eq_min_sub_min H lo hi (le_trans hlm hmh)]
  omega

theorem prefixIntervalMass_partition_between
    (H : Nat) (cuts : Nat → Nat) (n : Nat)
    (hmono : ∀ i, cuts i <= cuts (i + 1)) :
    (Finset.sum (Finset.range n) fun i =>
      prefixIntervalMass H (cuts i) (cuts (i + 1))) =
      prefixIntervalMass H (cuts 0) (cuts n) := by
  have h0n : ∀ n, cuts 0 <= cuts n := by
    intro n
    induction n with
    | zero => exact Nat.le_refl _
    | succ n ih0 => exact le_trans ih0 (hmono n)
  induction n with
  | zero => simp [prefixIntervalMass]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact prefixIntervalMass_add H (cuts 0) (cuts n) (cuts (n + 1))
        (h0n n)
        (hmono n)

theorem min_prefix_right_translate (G S x : Nat) (hSG : S <= G) :
    min G (S + x) = S + min (G - S) x := by
  by_cases htail : G - S <= x
  · have hG : G <= S + x := by omega
    rw [Nat.min_eq_left hG, Nat.min_eq_left htail]
    omega
  · have hx : x <= G - S := by omega
    have hxG : S + x <= G := by omega
    rw [Nat.min_eq_right hxG, Nat.min_eq_right hx]

/-- Restricting a global initial prefix to one tile and then taking a local
subinterval gives the same mass as taking that subinterval in global rank
coordinates. -/
theorem prefixIntervalMass_tile_local
    (G S W lo hi : Nat) (hlohi : lo <= hi) (hhi : hi <= W) :
    prefixIntervalMass (prefixIntervalMass G S (S + W)) lo hi =
      prefixIntervalMass G (S + lo) (S + hi) := by
  rw [prefixIntervalMass_eq_min_sub_min
      (prefixIntervalMass G S (S + W)) lo hi hlohi,
    prefixIntervalMass_eq_min_sub_min G (S + lo) (S + hi) (by omega)]
  by_cases hGS : G <= S
  · have hTile : prefixIntervalMass G S (S + W) = 0 := by
      unfold prefixIntervalMass
      rw [Nat.sub_eq_zero_of_le hGS]
      simp
    rw [hTile]
    have hSlo : S <= S + lo := by omega
    have hShi : S <= S + hi := by omega
    rw [Nat.min_eq_left (Nat.zero_le _), Nat.min_eq_left (Nat.zero_le _),
      Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
    omega
  · have hSG : S <= G := by omega
    by_cases hGE : G <= S + W
    · have hTile : prefixIntervalMass G S (S + W) = G - S := by
        unfold prefixIntervalMass
        rw [Nat.min_eq_left (by omega)]
      rw [hTile,
        min_prefix_right_translate G S hi hSG,
        min_prefix_right_translate G S lo hSG]
      omega
    · have hEW : S + W <= G := by omega
      have hTile : prefixIntervalMass G S (S + W) = W := by
        unfold prefixIntervalMass
        rw [Nat.min_eq_right (by omega)]
        simp
      rw [hTile]
      rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      omega

theorem tile_local_offset_eq_clamp (S W x : Nat) :
    S + min W (x - S) = min (S + W) (max x S) := by
  by_cases hx : x <= S
  · have hsub : x - S = 0 := Nat.sub_eq_zero_of_le hx
    simp [hsub, Nat.max_eq_right hx]
  · have hSx : S <= x := by omega
    by_cases hwidth : W <= x - S
    · have hright : S + W <= x := by omega
      rw [Nat.min_eq_left hwidth, Nat.max_eq_left hSx,
        Nat.min_eq_left hright]
    · have hwidth' : x - S <= W := by omega
      have hleft : x <= S + W := by omega
      have hsub : S + (x - S) = x := Nat.add_sub_of_le hSx
      rw [Nat.min_eq_right hwidth', Nat.max_eq_left hSx,
        Nat.min_eq_right hleft, hsub]

/-- A tile's clipped piece of a global interval is exactly the intersection
of that interval with the tile's rank span. -/
theorem prefixIntervalMass_clip_tile_interval
    (G a b S W : Nat) (hab : a <= b) :
    prefixIntervalMass G
        (S + min W (a - S)) (S + min W (b - S)) =
      prefixIntervalMass G
        (min b (max a S)) (min b (max a (S + W))) := by
  rw [tile_local_offset_eq_clamp S W a,
    tile_local_offset_eq_clamp S W b]
  by_cases hbefore : S + W <= a
  · have hcut0 : min b (max a S) = a := by
      rw [Nat.max_eq_left (by omega), Nat.min_eq_right hab]
    have hcut1 : min b (max a (S + W)) = a := by
      simp [Nat.max_eq_left hbefore, Nat.min_eq_right hab]
    have hleft : min (S + W) (max a S) = S + W := by
      apply Nat.min_eq_left
      exact le_trans hbefore (Nat.le_max_left a S)
    have hright : min (S + W) (max b S) = S + W := by
      apply Nat.min_eq_left
      exact le_trans (by omega) (Nat.le_max_left b S)
    rw [hleft, hright, hcut0, hcut1]
    simp [prefixIntervalMass]
  · by_cases hafter : b <= S
    · have hleft : min (S + W) (max a S) = S := by
        rw [Nat.max_eq_right (by omega)]
        exact Nat.min_eq_right (Nat.le_add_right S W)
      have hright : min (S + W) (max b S) = S := by
        rw [Nat.max_eq_right hafter]
        exact Nat.min_eq_right (Nat.le_add_right S W)
      have hcut0 : min b (max a S) = b := by
        rw [Nat.max_eq_right (by omega)]
        exact Nat.min_eq_left (by omega)
      have hcut1 : min b (max a (S + W)) = b := by
        rw [Nat.max_eq_right (by omega)]
        exact Nat.min_eq_left (by omega)
      rw [hleft, hright, hcut0, hcut1]
      simp [prefixIntervalMass]
    · have haEnd : a <= S + W := by omega
      have hSBeforeB : S <= b := by omega
      have hA : min (S + W) (max a S) = max a S := by
        apply Nat.min_eq_right
        exact max_le_iff.mpr ⟨haEnd, Nat.le_add_right S W⟩
      have hB : min (S + W) (max b S) = min b (S + W) := by
        rw [Nat.max_eq_left (Nat.le_of_lt (by omega))]
        exact Nat.min_comm _ _
      have hC0 : min b (max a S) = max a S := by
        apply Nat.min_eq_right
        exact max_le_iff.mpr ⟨hab, hSBeforeB⟩
      have hC1 : min b (max a (S + W)) = min b (S + W) := by
        rw [Nat.max_eq_right haEnd]
      rw [hA, hB, hC0, hC1]

/-- Prefix mass over the pieces of one global interval, clipped to equal
tiles, adds back to the interval's full prefix mass. -/
theorem prefixIntervalMass_tiled_interval_sum
    (G a b W tiles : Nat) (hab : a <= b) (hb : b <= tiles * W) :
    (Finset.sum (Finset.range tiles) fun t =>
      prefixIntervalMass (prefixIntervalMass G (t * W) ((t + 1) * W))
        (min W (a - t * W)) (min W (b - t * W))) =
      prefixIntervalMass G a b := by
  let cuts : Nat → Nat := fun k => min b (max a (k * W))
  have hmono : ∀ k, cuts k <= cuts (k + 1) := by
    intro k
    apply min_le_min le_rfl
    exact max_le_max le_rfl (Nat.mul_le_mul_right W (Nat.le_succ k))
  have hcut0 : cuts 0 = a := by
    simp [cuts, Nat.min_eq_right hab]
  have hcutEnd : cuts tiles = b := by
    simp only [cuts]
    rw [Nat.max_eq_right (Nat.le_trans hab hb), Nat.min_eq_left hb]
  have hpieces : ∀ t < tiles,
      prefixIntervalMass (prefixIntervalMass G (t * W) ((t + 1) * W))
        (min W (a - t * W)) (min W (b - t * W)) =
      prefixIntervalMass G (cuts t) (cuts (t + 1)) := by
    intro t ht
    have hlocal := prefixIntervalMass_tile_local G (t * W) W
      (min W (a - t * W)) (min W (b - t * W))
      (by exact min_le_min le_rfl (Nat.sub_le_sub_right hab (t * W)))
      (Nat.min_le_left _ _)
    have hclipped := prefixIntervalMass_clip_tile_interval G a b
      (t * W) W hab
    have hsucc : (t + 1) * W = t * W + W := by ring
    simpa [cuts, hsucc] using hlocal.trans hclipped
  have hpart := prefixIntervalMass_partition_between G cuts tiles hmono
  rw [hcut0, hcutEnd] at hpart
  rw [Finset.sum_congr rfl (fun t ht => hpieces t (Finset.mem_range.mp ht))]
  exact hpart

end Chvatal.D2ClippedTilePrefixAllocation
