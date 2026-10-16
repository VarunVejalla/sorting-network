import AKS.Chvatal.FlowSizes7
import AKS.Chvatal.WireFlow
import AKS.Bitonic.Sorts

namespace Chvatal.PacketAlignment

open Chvatal
open Classical

private theorem dvd64_pow_pos {k : Nat} (hk : 0 < k) : 64 ∣ 64 ^ k := by
  exact dvd_pow (by norm_num) (by omega)

private theorem residue_4095_half (e : Nat) :
    (4095 * 32 * 64 ^ e) % 64 = 32 ∨ (4095 * 32 * 64 ^ e) % 64 = 0 := by
  cases e with
  | zero => norm_num
  | succ e =>
      right
      apply Nat.mod_eq_zero_of_dvd
      have hp : 64 ∣ 64 ^ (e + 1) := dvd64_pow_pos (by omega)
      exact dvd_mul_of_dvd_right hp _

private theorem residue_half_diff (g h : Nat) (hgh : h ≤ g) :
    (64 ^ (g + 1) - 64 ^ (h + 1)) / 2 % 64 = 0 ∨
      (64 ^ (g + 1) - 64 ^ (h + 1)) / 2 % 64 = 32 := by
  have hhalf : (64 ^ (g + 1) - 64 ^ (h + 1)) / 2 =
      32 * (64 ^ g - 64 ^ h) := by
    have hpowg : 64 ^ (g + 1) = 64 * 64 ^ g := by rw [pow_succ]; ring
    have hpowh : 64 ^ (h + 1) = 64 * 64 ^ h := by rw [pow_succ]; ring
    have hle : 64 ^ h ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) hgh
    rw [hpowg, hpowh]
    omega
  by_cases hh : h = 0
  · subst h
    by_cases hg : g = 0
    · subst g; norm_num
    · have hgpos : 0 < g := by omega
      have hdiv : 64 ∣ 64 ^ g := dvd64_pow_pos hgpos
      have hmod : 64 ^ g % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      rcases hdiv with ⟨k, hk⟩
      have hraw : 64 ^ g - 1 = 64 * (k - 1) + 63 := by
        rw [hk]
        have hp : 0 < 64 ^ g := Nat.pow_pos (by norm_num)
        rw [hk] at hp
        have hkpos : 0 < k := by omega
        omega
      rw [hhalf]
      right
      rw [show 64 ^ 0 = 1 by norm_num, hraw]
      norm_num [Nat.add_mod, Nat.mul_mod]
  · have hhpos : 0 < h := by omega
    have hdivg : 64 ∣ 64 ^ g := dvd64_pow_pos (by omega)
    have hdivh : 64 ∣ 64 ^ h := dvd64_pow_pos hhpos
    have hdiff : 64 ∣ 64 ^ g - 64 ^ h := Nat.dvd_sub hdivg hdivh
    rw [hhalf]
    left
    apply Nat.mod_eq_zero_of_dvd
    exact dvd_mul_of_dvd_right hdiff _

/-- Scratch refinement of `NodeShape` retaining the exponent discarded by the
existing `botRise` constructor. -/
inductive RefinedNodeShape (d t i : Nat) : Nat → Nat → Nat → Prop
  | off : RefinedNodeShape d t i 0 0 0
  | topDesc (g : Nat) (e : d + 2 * i = t + 3 + g) (hi : Inner d t i)
      (h : i = 0 ∨ g ≤ 4) :
      RefinedNodeShape d t i (64 ^ (g + 1)) 0 (64 ^ g)
  | topRise (f : Nat) (e : d + 2 * i = t + 8 + f)
      (h : Inner d t i ∨ (t = 1 ∧ i = 1)) :
      RefinedNodeShape d t i (64 ^ (6 + f)) (2 * (32 * 64 ^ (1 + f)))
        (16777215 * 64 ^ (1 + f))
  | mid (g : Nat) (e : d + 2 * i = t + 9 + g) (h : Inner d t i) :
      RefinedNodeShape d t i (64 ^ (7 + g) - 64 ^ (1 + g))
        (2 * (4095 * 32 * 64 ^ g)) (16777215 * 64 ^ (2 + g))
  | botDesc (g h : Nat) (hgh : h + 2 ≤ g) (hg : g ≤ h + 6)
      (e : d + 2 * i = t + 9 + h) (hd : d = i + (g + 1)) :
      RefinedNodeShape d t i (64 ^ (g + 1) - 64 ^ (h + 1))
        (2 * (4095 * 32 * 64 ^ h)) (64 ^ g - 64 ^ (h + 2))
  | botRise (g h : Nat) (hgh : h ≤ g)
      (e : d + 2 * i = t + 9 + h) (hd : d = i + (g + 1))
      (hi : i = omega7 d t) :
      RefinedNodeShape d t i (64 ^ (g + 1) - 64 ^ (h + 1))
        (64 ^ (g + 1) - 64 ^ (h + 1)) 0

/-- Refined form of `shape_rat`: the bottom-rising case keeps its exponent. -/
theorem shape_rat_refined (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ∃ a u n : Nat, allocation d i t = a ∧ flowUp d i t = u ∧ flowDown d i t = n ∧
      RefinedNodeShape d t i a u n := by
  by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exact ⟨0, 0, 0, by simp [allocation_inactive _ _ _ hact],
      by simp [flowUp_inactive _ hact], by simp [flowDown_inactive _ hact], .off⟩
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  have hq1 := omega7_parity d t
  have hq2 := omega7_parity d (t + 1)
  have hqt := omega7_step d t hd ht
  have hact' := hact
  obtain ⟨-, hαle, hωle, hpar⟩ := hact'
  by_cases hα : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 3 + g :=
        ⟨d + 2 * i - (t + 3), by have := exp_top d t ht2 ht.le; omega⟩
      have hc := capacity_eq_pow d i t (g + 1) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .topDesc g hg ⟨ht2, by omega, by omega, by omega⟩ ?_⟩
      · rw [alloc_top d hact hα, hc]
      · rw [flowUp_top_desc d hact hα hs]; simp
      · rw [flowDown_top_desc d hact hα hs, hc]; push_cast; ring
      · rcases lemma32_schedule7 d hd t hs with h0 | h
        · left; omega
        · right
          rw [← hα, hc] at h
          by_contra hg5
          have : ((64 ^ 6 : Nat) : Rat) ≤ ((64 ^ (g + 1) : Nat) : Rat) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
          push_cast at h this
          linarith
    · obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f :=
        ⟨d + 2 * i - (t + 8), by have := exp_top_rise d t ht2 ht (by omega); omega⟩
      have hc := capacity_eq_pow d i t (6 + f) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .topRise f hf (Or.inl ⟨ht2, by omega, by omega, by omega⟩)⟩
      · rw [alloc_top d hact hα, hc]
      · rw [flowUp_top_rise d hact hα hs, hc]; push_cast; ring
      · rw [flowDown_mid d hact (fun _ => hs) (by omega), hc]; push_cast; ring
  · have hne := exp_nontop d t i ht2 ht (by omega) hpar
    by_cases hω : i = omega7 d t
    · obtain ⟨g, hgi⟩ : ∃ g, d = i + (g + 1) :=
        ⟨d - i - 1, by have := omega7_lt_d d t hd ht.le; omega⟩
      obtain ⟨h, hh⟩ : ∃ h, d + 2 * i = t + 9 + h :=
        ⟨d + 2 * i - (t + 9), by omega⟩
      have hb := omega7_bounds d t ht2
      have hc := capacity_eq_pow d i t (7 + h) (by omega)
      have hle : 64 ^ (h + 1) ≤ 64 ^ (g + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hA : allocation d i t = ((64 ^ (g + 1) - 64 ^ (h + 1) : Nat) : Rat) := by
        rw [alloc_bot d hact hα hω, hc, capacityRatio_eq, Nat.cast_sub hle]
        show ((64 ^ d : Nat) : Rat) / ((64 : Nat) : Rat) ^ i - _ = _
        rw [hgi]; push_cast
        simp only [pow_add]
        field_simp
      by_cases hs : omega7 d t < omega7 d (t + 1)
      · have hU : flowUp d i t = ((2 * (4095 * 32 * 64 ^ h) : Nat) : Rat) := by
          rw [flowUp_mid d hact hα (fun _ => hs), hc, capacityRatio_eq]; push_cast; ring
        refine ⟨_, _, _, hA, hU, ?_, .botDesc g h (by omega) (by omega) hh hgi⟩
        have hsend := flow_send7 d hd t ht2 ht i
        rw [hA, hU, Nat.cast_sub hle] at hsend
        rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
        push_cast at hsend ⊢
        ring_nf at hsend ⊢
        linarith
      · refine ⟨_, _, _, hA, ?_, ?_, .botRise g h (by omega) hh hgi hω⟩
        · rw [flowUp_bot_rise d hact hα hω hs, hA]
        · rw [flowDown_bot_rise d hact hα hω hs]; simp
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g :=
        ⟨d + 2 * i - (t + 9), by omega⟩
      have hc := capacity_eq_pow d i t (7 + g) (by omega)
      have hle : 64 ^ (1 + g) ≤ 64 ^ (7 + g) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .mid g hg ⟨ht2, by omega, by omega, by omega⟩⟩
      · rw [alloc_mid d hact hα hω, hc, capacityRatio_eq, Nat.cast_sub hle]
        push_cast; rw [pow_add, pow_add]; field_simp
      · rw [flowUp_mid d hact hα (fun h => absurd h hω), hc, capacityRatio_eq]; push_cast; ring
      · rw [flowDown_mid d hact (fun h => absurd h hα) hω, hc]; push_cast; ring

/-- Natural-number flow nodes inherit the refined shape witness. -/
theorem node_shape_refined (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    RefinedNodeShape d t i (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t) := by
  obtain ⟨a, u, n, ha, hu, hn, hshape⟩ := shape_rat_refined d hd t i ht2 ht
  unfold flowA7 flowUp7 flowDown7
  simp only [if_neg (show t ≠ 0 by omega), if_neg (show t ≠ 1 by omega),
    floor_of_eq _ _ ha, floor_of_eq _ _ hu, floor_of_eq _ _ hn]
  exact hshape

/-- Every ordinary scheduled bag has either a power-of-64 wire count, or is
within a `64^-2` to `64^-6` relative padding of one.  The latter family has
the exact form `64^(h+1) * (64^r - 1)`. -/
theorem scheduled_bag_size_form {d t i a u n : Nat}
    (hd : 7 ≤ d) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (shape : RefinedNodeShape d t i a u n) :
    a = 0 ∨ (∃ e, a = 64 ^ e) ∨
      (∃ h r, 2 ≤ r ∧ r ≤ 6 ∧ a = 64 ^ (h + 1) * (64 ^ r - 1)) := by
  cases shape with
  | off => exact Or.inl rfl
  | topDesc g _ _ _ => exact Or.inr (Or.inl ⟨g + 1, rfl⟩)
  | topRise f _ _ => exact Or.inr (Or.inl ⟨6 + f, rfl⟩)
  | mid g _ _ =>
      right; right
      refine ⟨g, 6, by omega, by omega, ?_⟩
      have he : 7 + g = (g + 1) + 6 := by omega
      have he2 : 1 + g = g + 1 := by omega
      rw [he, he2, pow_add]
      change 64 ^ (g + 1) * 64 ^ 6 - 64 ^ (g + 1) =
        64 ^ (g + 1) * (64 ^ 6 - 1)
      norm_num
      omega
  | botDesc g h hgh hg _ _ =>
      right; right
      refine ⟨h, g - h, ?_, ?_, ?_⟩
      · omega
      · omega
      · have he : g + 1 = (h + 1) + (g - h) := by omega
        rw [he, pow_add]
        simpa using (Nat.mul_sub_left_distrib (64 ^ (h + 1)) (64 ^ (g - h)) 1).symm
  | botRise g h hgh he hdrel hi =>
      right; right
      have hb := omega7_bounds d t ht2
      have hgap : 2 ≤ g - h ∧ g - h ≤ 6 := by omega
      refine ⟨h, g - h, hgap.1, hgap.2, ?_⟩
      have he' : g + 1 = (h + 1) + (g - h) := by omega
      rw [he', pow_add]
      simpa using (Nat.mul_sub_left_distrib (64 ^ (h + 1)) (64 ^ (g - h)) 1).symm

/-- The packet-size classification for the actual integer scheduler flow. -/
theorem flowA7_scheduled_bag_size_form (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    flowA7 d hd i t = 0 ∨ (∃ e, flowA7 d hd i t = 64 ^ e) ∨
      (∃ h r, 2 ≤ r ∧ r ≤ 6 ∧
        flowA7 d hd i t = 64 ^ (h + 1) * (64 ^ r - 1)) := by
  exact scheduled_bag_size_form hd ht2 ht (node_shape_refined d hd t i ht2 ht)

/-- Every ordinary scheduled shape has packet-multiple bag/down sizes and a
half-fringe residue of either zero or one half-packet. -/
theorem refined_packet_residues {d t i a u n : Nat}
    (hd : 7 ≤ d) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (shape : RefinedNodeShape d t i a u n) :
    64 ∣ a ∧ 64 ∣ n ∧ (u / 2 % 64 = 0 ∨ u / 2 % 64 = 32) := by
  cases shape with
  | off => simp
  | topDesc g he hi hs =>
      have hg : 2 ≤ g := by
        rcases hi with ⟨_, hαle, _, hpar⟩
        by_cases hEq : i = alpha7 d t
        · have hx := exp_top d t ht2 (Nat.le_of_lt ht)
          rw [← hEq] at hx
          omega
        · have hgap : alpha7 d t + 2 ≤ i := by
            have hp := alpha7_parity d t
            omega
          have hx := exp_nontop d t i ht2 ht hgap hpar
          omega
      refine ⟨dvd64_pow_pos (by omega), dvd64_pow_pos (by omega), ?_⟩
      simp
  | topRise f he hi =>
      change 64 ∣ 64 ^ (6 + f) ∧
        64 ∣ 16777215 * 64 ^ (1 + f) ∧
        ((2 * (32 * 64 ^ (1 + f))) / 2 % 64 = 0 ∨
         (2 * (32 * 64 ^ (1 + f))) / 2 % 64 = 32)
      refine ⟨dvd64_pow_pos (by omega), ?_, ?_⟩
      · have hp : 64 ∣ 64 ^ (1 + f) := dvd64_pow_pos (by omega)
        exact dvd_mul_of_dvd_right hp _
      · simp [Nat.mul_div_cancel_left]
        left
        apply Nat.mod_eq_zero_of_dvd
        have hp : 64 ∣ 64 ^ (1 + f) := dvd64_pow_pos (by omega)
        exact dvd_mul_of_dvd_right hp _
  | mid g he hi =>
      change 64 ∣ 64 ^ (7 + g) - 64 ^ (1 + g) ∧
        64 ∣ 16777215 * 64 ^ (2 + g) ∧
        ((2 * (4095 * 32 * 64 ^ g)) / 2 % 64 = 0 ∨
         (2 * (4095 * 32 * 64 ^ g)) / 2 % 64 = 32)
      refine ⟨?_, ?_, ?_⟩
      · have hp1 : 64 ∣ 64 ^ (7 + g) := dvd64_pow_pos (by omega)
        have hp2 : 64 ∣ 64 ^ (1 + g) := dvd64_pow_pos (by omega)
        exact Nat.dvd_sub hp1 hp2
      · have hp : 64 ∣ 64 ^ (2 + g) := dvd64_pow_pos (by omega)
        exact dvd_mul_of_dvd_right hp _
      · simp [Nat.mul_div_cancel_left]
        change (131040 * 64 ^ g) % 64 = 0 ∨ (131040 * 64 ^ g) % 64 = 32
        have hcoef : 131040 = 4095 * 32 := by norm_num
        rw [hcoef]
        rcases residue_4095_half g with hh | hh
        · exact Or.inr hh
        · exact Or.inl hh
  | botDesc g h hgh hg he hdi =>
      change 64 ∣ 64 ^ (g + 1) - 64 ^ (h + 1) ∧
        64 ∣ 64 ^ g - 64 ^ (h + 2) ∧
        ((2 * (4095 * 32 * 64 ^ h)) / 2 % 64 = 0 ∨
         (2 * (4095 * 32 * 64 ^ h) / 2) % 64 = 32)
      refine ⟨?_, ?_, ?_⟩
      · have hp1 : 64 ∣ 64 ^ (g + 1) := dvd64_pow_pos (by omega)
        have hp2 : 64 ∣ 64 ^ (h + 1) := dvd64_pow_pos (by omega)
        exact Nat.dvd_sub hp1 hp2
      · have hp1 : 64 ∣ 64 ^ g := dvd64_pow_pos (by omega)
        have hp2 : 64 ∣ 64 ^ (h + 2) := dvd64_pow_pos (by omega)
        exact Nat.dvd_sub hp1 hp2
      · simp [Nat.mul_div_cancel_left]
        change (131040 * 64 ^ h) % 64 = 0 ∨ (131040 * 64 ^ h) % 64 = 32
        have hcoef : 131040 = 4095 * 32 := by norm_num
        rw [hcoef]
        rcases residue_4095_half h with hh | hh
        · exact Or.inr hh
        · exact Or.inl hh
  | botRise g h hgh he _ _ =>
      change 64 ∣ 64 ^ (g + 1) - 64 ^ (h + 1) ∧ 64 ∣ 0 ∧
        ((64 ^ (g + 1) - 64 ^ (h + 1)) / 2 % 64 = 0 ∨
         (64 ^ (g + 1) - 64 ^ (h + 1)) / 2 % 64 = 32)
      refine ⟨?_, by simp, ?_⟩
      · have hp1 : 64 ∣ 64 ^ (g + 1) := dvd64_pow_pos (by omega)
        have hp2 : 64 ∣ 64 ^ (h + 1) := dvd64_pow_pos (by omega)
        exact Nat.dvd_sub hp1 hp2
      · exact residue_half_diff g h hgh

/-- Actual packet counts (wire count divided by packet width 64) are powers of
64 or one of the five bounded-cofactor families `64^h * (64^r - 1)`. -/
theorem flowA7_scheduled_packet_factorization (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    flowA7 d hd i t = 0 ∨
      (∃ e, flowA7 d hd i t / 64 = 64 ^ e) ∨
      (∃ h r, 2 ≤ r ∧ r ≤ 6 ∧
        flowA7 d hd i t / 64 = 64 ^ h * (64 ^ r - 1)) := by
  have hdiv : 64 ∣ flowA7 d hd i t :=
    (refined_packet_residues hd ht2 ht
      (node_shape_refined d hd t i ht2 ht)).1
  rcases flowA7_scheduled_bag_size_form d hd t i ht2 ht with hz | hp | hnear
  · exact Or.inl hz
  · rcases hp with ⟨e, he⟩
    have hepos : 0 < e := by
      by_contra hn
      have he0 : e = 0 := by omega
      rw [he0] at he
      simp at he
      rw [he] at hdiv
      norm_num at hdiv
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    right; left
    refine ⟨k, ?_⟩
    rw [he, pow_succ]
    simp
  · rcases hnear with ⟨h, r, hrlo, hrhi, he⟩
    right; right
    refine ⟨h, r, hrlo, hrhi, ?_⟩
    have hfactor : 64 ^ (h + 1) * (64 ^ r - 1) =
        64 * (64 ^ h * (64 ^ r - 1)) := by
      rw [show h + 1 = Nat.succ h by omega, pow_succ]
      ring
    rw [he, hfactor]
    simp

/-- A live half-fringe cuts the 64-wire packet grid exactly in half. -/
def HalfMisaligned (u : Nat) : Prop := 0 < u ∧ u / 2 % 64 = 32

/-- In a refined scheduled shape, a positive half-fringe can be half-packet
shifted only at the unique exponent level `d + 2*i = t + 9`. -/
theorem halfMisalignment_exponent {d t i a u n : Nat}
    (shape : RefinedNodeShape d t i a u n)
    (bad : HalfMisaligned u) : d + 2 * i = t + 9 := by
  cases shape with
  | off => simp [HalfMisaligned] at bad
  | topDesc g he hi hs => simp [HalfMisaligned] at bad
  | topRise f he hi =>
      simp [HalfMisaligned] at bad
      have hdiv : 64 ∣ 32 * 64 ^ (1 + f) := by
        have hp : 64 ∣ 64 ^ (1 + f) := dvd_pow (by norm_num) (by omega)
        exact dvd_mul_of_dvd_right hp _
      have hmod : 32 * 64 ^ (1 + f) % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
      omega
  | mid g he hi =>
      simp [HalfMisaligned] at bad
      have hg0 : g = 0 := by
        by_contra hne
        have hgpos : 1 ≤ g := by omega
        have hdiv : 64 ∣ 4095 * 32 * 64 ^ g := by
          have hp : 64 ∣ 64 ^ g := dvd_pow (by norm_num) (by omega)
          exact dvd_mul_of_dvd_right hp _
        have hmod : 4095 * 32 * 64 ^ g % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
      omega
  | botDesc g h hgh hg he hd =>
      simp [HalfMisaligned] at bad
      have hh0 : h = 0 := by
        by_contra hne
        have hhpos : 1 ≤ h := by omega
        have hp : 64 ∣ 64 ^ h := dvd_pow (by norm_num) (by omega)
        have hdiv : 64 ∣ 4095 * 32 * 64 ^ h := dvd_mul_of_dvd_right hp _
        have hmod : 4095 * 32 * 64 ^ h % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
      omega
  | botRise g h hgh he _ _ =>
      simp [HalfMisaligned] at bad
      have hh0 : h = 0 := by
        by_contra hne
        have hhpos : 1 ≤ h := by omega
        have hpow : 64 ∣ 64 ^ h := dvd_pow (by norm_num) (by omega)
        have hdiff : 64 ∣ 64 ^ g - 64 ^ h := by
          have hg : 64 ∣ 64 ^ g := dvd_pow (by norm_num) (by omega)
          exact Nat.dvd_sub hg hpow
        have hhalf : (64 ^ (g + 1) - 64 ^ (h + 1)) / 2 =
            32 * (64 ^ g - 64 ^ h) := by
          have hpowg : 64 ^ (g + 1) = 64 * 64 ^ g := by rw [pow_succ]; ring
          have hpowh : 64 ^ (h + 1) = 64 * 64 ^ h := by rw [pow_succ]; ring
          have hle : 64 ^ h ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) hgh
          rw [hpowg, hpowh]
          omega
        have hdiv : 64 ∣ 32 * (64 ^ g - 64 ^ h) := dvd_mul_of_dvd_right hdiff _
        rw [hhalf] at bad
        have hmod : 32 * (64 ^ g - 64 ^ h) % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
      have hgpos : 1 ≤ g := by
        by_contra hnot
        have hg0 : g = 0 := by omega
        subst g
        simp [hh0] at bad
      omega

theorem parent_child_halfMisalignment_impossible {d t level : Nat}
    (parentEquation : d + 2 * (level - 1) = t + 9)
    (childEquation : d + 2 * (level + 1) = t + 9) : False := by
  omega

/-- A receiver cannot simultaneously have a live shifted parent fringe and
a live shifted child fringe. -/
theorem receiver_no_simultaneous_misalignment {d t level : Nat}
    {ap up np ac uc nc : Nat}
    (parentShape : RefinedNodeShape d t (level - 1) ap up np)
    (childShape : RefinedNodeShape d t (level + 1) ac uc nc)
    (parentBad : HalfMisaligned up) (childBad : HalfMisaligned uc) : False := by
  have parentEq := halfMisalignment_exponent parentShape parentBad
  have childEq := halfMisalignment_exponent childShape childBad
  omega

/-- The no-simultaneous-shift statement specialized to actual scheduled
integer flows; the refined classifier supplies the formerly missing witness. -/
theorem scheduled_receiver_no_simultaneous_misalignment
    (d : Nat) (hd : 7 ≤ d) (t level : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ¬ (HalfMisaligned (flowUp7 d hd (level - 1) t) ∧
       HalfMisaligned (flowUp7 d hd (level + 1) t)) := by
  intro hbad
  have hp := node_shape_refined d hd t (level - 1) ht2 ht
  have hc := node_shape_refined d hd t (level + 1) ht2 ht
  exact receiver_no_simultaneous_misalignment hp hc hbad.1 hbad.2

/-- `WireFlow.downSet` is exactly the half-open rank interval prescribed by
the child-port cut. This is the point where the residue calculations apply
to the concrete flow partition. -/
theorem downSet_rank_cut {N : Nat} (s : Finset (Fin N)) (π τ j : Nat)
    {w : Fin N} (hw : w ∈ downSet s π τ j) :
    w ∈ s ∧ π / 2 + j * τ ≤ rankIn s w ∧
      rankIn s w < π / 2 + (j + 1) * τ := by
  change w ∈ blockOf s (π / 2 + j * τ) (π / 2 + (j + 1) * τ) at hw
  exact mem_blockOf.mp hw

/-- The rank image of a `WireFlow.blockOf` is exactly its interval of rank
labels. This records that the interval accounting is realized by the concrete
wire set, not just by its cardinality. -/
theorem blockOf_rank_image {N : Nat} (s : Finset (Fin N)) (lo hi : Nat)
    (hhi : hi ≤ s.card) : (blockOf s lo hi).image (rankIn s) = Finset.Ico lo hi := by
  have himg : s.image (rankIn s) = Finset.range s.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases Finset.mem_image.mp hr with ⟨w, hw, rfl⟩
      exact Finset.mem_range.mpr (rankIn_lt_card hw)
    · simp [Finset.card_image_of_injOn rankIn_injOn]
  ext r
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_blockOf.mp hw).2
  · intro hr
    have hrCard : r < s.card := hr.2.trans_le hhi
    have hrImage : r ∈ s.image (rankIn s) := by
      rw [himg]
      exact Finset.mem_range.mpr hrCard
    rcases Finset.mem_image.mp hrImage with ⟨w, hw, hwr⟩
    exact ⟨w, mem_blockOf.mpr ⟨hw, by rw [hwr]; exact hr.1,
      by rw [hwr]; exact hr.2⟩, hwr⟩

/-- Exact rank-label image of a child port in `WireFlow`. -/
theorem downSet_rank_image {N : Nat} (s : Finset (Fin N)) (π τ j : Nat)
    (hhi : π / 2 + (j + 1) * τ ≤ s.card) :
    (downSet s π τ j).image (rankIn s) =
      Finset.Ico (π / 2 + j * τ) (π / 2 + (j + 1) * τ) := by
  unfold downSet
  exact blockOf_rank_image s _ _ hhi

/-- Exact rank-label images of the two parent fringes in `WireFlow.upSet`. -/
theorem upSet_rank_images {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hhi : π / 2 ≤ s.card) :
    (blockOf s 0 (π / 2)).image (rankIn s) = Finset.Ico 0 (π / 2) ∧
      (blockOf s (s.card - π / 2) s.card).image (rankIn s) =
        Finset.Ico (s.card - π / 2) s.card := by
  constructor
  · exact blockOf_rank_image s _ _ (by omega)
  · exact blockOf_rank_image s _ _ (by omega)

/-- A value assignment is sorted on `s` when increasing wire index never
decreases the value. This is the invariant needed to regard rank cuts as
sorted runs. -/
def RankSortedOn {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (v : Fin N → α) : Prop :=
  ∀ ⦃x y : Fin N⦄, x ∈ s → y ∈ s → x.val ≤ y.val → v x ≤ v y

/-- Rank-sortedness passes to every concrete wire subset, in particular to
the fragments selected by `blockOf`. -/
theorem rankSortedOn_subset {N : Nat} {α : Type} [Preorder α]
    {s t : Finset (Fin N)} {v : Fin N → α}
    (hsub : t ⊆ s) (hsort : RankSortedOn s v) : RankSortedOn t v := by
  intro x y hx hy hxy
  exact hsort (hsub hx) (hsub hy) hxy

theorem rankSortedOn_blockOf {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (lo hi : Nat) (v : Fin N → α)
    (hsort : RankSortedOn s v) : RankSortedOn (blockOf s lo hi) v :=
  rankSortedOn_subset (blockOf_subset) hsort

theorem rankSortedOn_downSet {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (π τ j : Nat) (v : Fin N → α)
    (hsort : RankSortedOn s v) : RankSortedOn (downSet s π τ j) v :=
  rankSortedOn_subset downSet_subset hsort

theorem rankSortedOn_upSet {N : Nat} {α : Type} [Preorder α]
    (s : Finset (Fin N)) (π : Nat) (v : Fin N → α)
    (hsort : RankSortedOn s v) : RankSortedOn (upSet s π) v :=
  rankSortedOn_subset upSet_subset hsort

/-- If the parent's current wire-set is value-sorted, its concrete incoming
`parentPart` remains one sorted run after the `WireFlow` rank cut. -/
theorem rankSortedOn_parentPart {d tf : Nat} {α : Type} [Preorder α]
    (F : FlowSizes d tf) (S : KBag 64 d → Finset (Fin (64 ^ d))) (t : Nat)
    (b : KBag 64 d) (v : Fin (64 ^ d) → α) (hb : 1 ≤ b.l)
    (hsort : RankSortedOn (S b.parent) v) :
    RankSortedOn (parentPart F S t b) v := by
  unfold parentPart
  rw [if_pos hb]
  exact rankSortedOn_downSet (S b.parent) _ _ _ v hsort

/-- Each child contributes a sorted incoming `upSet` run whenever that
child's current wire-set is sorted. -/
theorem rankSortedOn_childPort {d tf : Nat} {α : Type} [Preorder α]
    (F : FlowSizes d tf) (S : KBag 64 d → Finset (Fin (64 ^ d))) (t : Nat)
    (b : KBag 64 d) (v : Fin (64 ^ d) → α) (j : Fin 64) (hb : b.l < d)
    (hsort : RankSortedOn (S (b.child j.val j.isLt hb)) v) :
    RankSortedOn (upSet (S (b.child j.val j.isLt hb)) (F.up (b.l + 1) t)) v :=
  rankSortedOn_upSet (S (b.child j.val j.isLt hb)) _ v hsort

/-- A Boolean vector that rises weakly on its first half and falls weakly on
its second half has a contiguous true set, hence satisfies Bitonic.Window. -/
theorem window_of_halves (v : Fin 64 → Bool)
    (hlow : ∀ i j, i.val ≤ j.val → j.val < 32 → v i ≤ v j)
    (hhigh : ∀ i j, 32 ≤ i.val → i.val ≤ j.val → v j ≤ v i) :
    Bitonic.Window v := by
  classical
  let T : Finset (Fin 64) := Finset.univ.filter (fun i => v i = true)
  by_cases hT : T.Nonempty
  · let lo : Fin 64 := T.min' hT
    let hi : Fin 64 := T.max' hT
    refine ⟨lo.val, hi.val + 1, Or.inl ?_⟩
    intro i
    constructor
    · intro hv
      have hmem : i ∈ T := by simp [T, hv]
      have hlow' : lo ≤ i := Finset.min'_le T i hmem
      have hhigh' : i ≤ hi := Finset.le_max' T i hmem
      exact ⟨(Fin.le_iff_val_le_val).1 hlow', Nat.lt_succ_of_le ((Fin.le_iff_val_le_val).1 hhigh')⟩
    · intro hr
      have hlo : lo ≤ i := Fin.le_iff_val_le_val.mpr hr.1
      have hhi : i ≤ hi := Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ hr.2)
      have hloT : v lo = true := by
        have hm := Finset.min'_mem T hT
        simpa [T] using hm
      have hhiT : v hi = true := by
        have hm := Finset.max'_mem T hT
        simpa [T] using hm
      have htrue : v i = true := by
        by_cases hi32 : i.val < 32
        · have hlo32 : lo.val < 32 := by have := hlo; omega
          have hmono := hlow lo i (by exact (Fin.le_iff_val_le_val).2 (by omega)) hi32
          rw [hloT] at hmono
          cases hv' : v i
          · rw [hv'] at hmono
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hmono)
          · rfl
        · have hi32' : 32 ≤ i.val := by omega
          have hhi32 : 32 ≤ hi.val := by have := hhi; omega
          have hmono := hhigh i hi hi32' hhi
          rw [hhiT] at hmono
          cases hv' : v i
          · rw [hv'] at hmono
            exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) hmono)
          · rfl
      simpa [T] using htrue
  · refine ⟨0, 0, Or.inl ?_⟩
    intro i
    have hfalse : v i ≠ true := by
      intro hv
      exact hT ⟨i, by simp [T, hv]⟩
    simp [hfalse]

/-- A 64-wire bitonic merge sorts two arbitrary ascending 32-wire runs when
the second run is reversed into the upper half. This is the local repair
primitive for pairing two half-packet boundary fragments. -/
theorem bitonicMerge64_sorts_two_runs {α : Type} [LinearOrder α]
    (v : Fin 64 → α)
    (hlow : ∀ i j, i.val ≤ j.val → j.val < 32 → v i ≤ v j)
    (hhigh : ∀ i j, 32 ≤ i.val → i.val ≤ j.val → v j ≤ v i) :
    Monotone ((Bitonic.bitonicMerge 6).exec v) := by
  intro i j hij
  by_contra hnot
  have hrev : (Bitonic.bitonicMerge 6).exec v j < (Bitonic.bitonicMerge 6).exec v i :=
    lt_of_not_ge hnot
  let c := (Bitonic.bitonicMerge 6).exec v j
  let cut : α → Bool := fun x => decide (c < x)
  have hcutmono : Monotone cut := by
    intro a b hab
    by_cases ha : c < a
    · have hb : c < b := lt_of_lt_of_le ha hab
      simp [cut, ha, hb]
    · simp [cut, ha]
  have hwindow' : Bitonic.Window (fun k => cut (v k)) := by
    -- Every threshold of the two-run input has the same rise/fall shape.
    apply window_of_halves
    · intro a b hab hb32
      by_cases haa : c < v a
      · have hbb : c < v b := lt_of_lt_of_le haa (hlow a b hab hb32)
        simp [cut, haa, hbb]
      · simp [cut, haa]
    · intro a b ha32 hab
      by_cases hbb : c < v b
      · have haa : c < v a := lt_of_lt_of_le hbb (hhigh a b ha32 hab)
        simp [cut, haa, hbb]
      · simp [cut, hbb]
  have hbool := Bitonic.bitonicMerge_sorts 6 (fun k => cut (v k)) hwindow'
  have hmono := hbool hij
  have hcomm := ComparatorNetwork.exec_comp_monotone (Bitonic.bitonicMerge 6) hcutmono v
  simp only [Function.comp] at hcomm
  have hci := congrFun hcomm i
  have hcj := congrFun hcomm j
  change cut ((Bitonic.bitonicMerge 6).exec v i) =
    (Bitonic.bitonicMerge 6).exec (fun k => cut (v k)) i at hci
  change cut ((Bitonic.bitonicMerge 6).exec v j) =
    (Bitonic.bitonicMerge 6).exec (fun k => cut (v k)) j at hcj
  have hmono' : cut ((Bitonic.bitonicMerge 6).exec v i) ≤
      cut ((Bitonic.bitonicMerge 6).exec v j) := by
    rw [hci, hcj]
    exact hmono
  have htrue : cut ((Bitonic.bitonicMerge 6).exec v i) = true := by
    simp [cut, c, hrev]
  have hfalse : cut ((Bitonic.bitonicMerge 6).exec v j) = false := by
    simp [cut, c]
  rw [htrue, hfalse] at hmono'
  exact (by decide : ¬ ((true : Bool) ≤ false)) hmono'

theorem bitonicMerge64_depth_le : (Bitonic.bitonicMerge 6).depth ≤ 6 :=
  Bitonic.bitonicMerge_depth_le 6

/-- Fixed-label fallback for an arbitrary 64-wire support: scatter the full
64-wire bitonic sorter along the increasing physical-wire embedding. This
sorts the values on that support regardless of how the source fragments
interleave in the receiver. -/
theorem bitonicSort64_scatter_sorts {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 64 ↪o Fin N) (v : Fin N → α) :
    Monotone (fun i =>
      ((Bitonic.bitonicSort 6).scatterEmbed N e).exec v (e i)) := by
  have hsort : Monotone ((Bitonic.bitonicSort 6).exec (v ∘ e)) :=
    (Bitonic.bitonicSort_sorts 6) α (v ∘ e)
  simpa only [ComparatorNetwork.scatterEmbed_exec_inside] using hsort

/-- The fixed-label fallback costs at most 21 layers. -/
theorem bitonicSort64_scatter_depth_le {N : Nat} (e : Fin 64 ↪o Fin N) :
    ((Bitonic.bitonicSort 6).scatterEmbed N e).depth ≤ 21 := by
  exact (depth_scatterEmbed_le (Bitonic.bitonicSort 6) N e).trans (by
    have h := Bitonic.bitonicSort_depth_le_budget 6
    norm_num [bitonicDepthBudget] at h
    exact h)

/-- A full 128-wire sorter can consume two arbitrary fixed supports and
produce a sorted union on their increasing physical-wire order. -/
theorem bitonicSort128_scatter_sorts {N : Nat} {α : Type} [LinearOrder α]
    (e : Fin 128 ↪o Fin N) (v : Fin N → α) :
    Monotone (fun i =>
      ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v (e i)) := by
  have hsort : Monotone ((Bitonic.bitonicSort 7).exec (v ∘ e)) :=
    (Bitonic.bitonicSort_sorts 7) α (v ∘ e)
  simpa only [ComparatorNetwork.scatterEmbed_exec_inside] using hsort

theorem bitonicSort128_scatter_depth_le {N : Nat} (e : Fin 128 ↪o Fin N) :
    ((Bitonic.bitonicSort 7).scatterEmbed N e).depth ≤ 28 := by
  exact (depth_scatterEmbed_le (Bitonic.bitonicSort 7) N e).trans (by
    have h := Bitonic.bitonicSort_depth_le_budget 7
    norm_num [bitonicDepthBudget] at h
    exact h)

/-- Alternating ranks of a sorted 128-wire union form two sorted packets,
with the packets interleaved rank-by-rank. -/
theorem sorted128_even_odd_interleave {α : Type} [Preorder α]
    (w : Fin 128 → α) (hw : Monotone w) :
    ∀ i : Fin 63,
      w ⟨2 * i.val, by have := i.isLt; omega⟩ ≤
        w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ∧
      w ⟨2 * i.val + 1, by have := i.isLt; omega⟩ ≤
        w ⟨2 * i.val + 2, by have := i.isLt; omega⟩ := by
  intro i
  constructor <;> apply hw <;> simp <;> omega

/-- Fixed-support merge-and-deal fallback: sort the union of any two packet
supports, then designate alternating physical ranks as the two output
supports. The output lanes are sorted and interleave rank-by-rank. -/
theorem bitonicSort128_scatter_parity_profile {N : Nat} {α : Type}
    [LinearOrder α] (e : Fin 128 ↪o Fin N) (v : Fin N → α) :
    ∀ i : Fin 63,
      ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v
          (e ⟨2 * i.val, by have := i.isLt; omega⟩) ≤
        ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v
          (e ⟨2 * i.val + 1, by have := i.isLt; omega⟩) ∧
      ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v
          (e ⟨2 * i.val + 1, by have := i.isLt; omega⟩) ≤
        ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v
          (e ⟨2 * i.val + 2, by have := i.isLt; omega⟩) := by
  exact sorted128_even_odd_interleave
    (fun i => ((Bitonic.bitonicSort 7).scatterEmbed N e).exec v (e i))
    (bitonicSort128_scatter_sorts e v)

/-- The two endpoint half-packets of a long rank interval are disjoint and
form a fixed 64-wire support. -/
theorem rankInterval_endpoint_pair {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hspan : 64 ≤ hi - lo) (hhi : hi ≤ s.card) :
    Disjoint (blockOf s lo (lo + 32)) (blockOf s (hi - 32) hi) ∧
      (blockOf s lo (lo + 32)).card = 32 ∧
      (blockOf s (hi - 32) hi).card = 32 ∧
      (blockOf s lo (lo + 32) ∪ blockOf s (hi - 32) hi).card = 64 := by
  have hlo : lo + 32 ≤ s.card := by omega
  have hleft : (blockOf s lo (lo + 32)).card = 32 := by
    rw [blockOf_card (by omega)]
    omega
  have hright : (blockOf s (hi - 32) hi).card = 32 := by
    rw [blockOf_card hhi]
    omega
  have hdisj : Disjoint (blockOf s lo (lo + 32)) (blockOf s (hi - 32) hi) :=
    disjoint_blockOf (by omega)
  refine ⟨hdisj, hleft, hright, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hleft, hright]

/-- Rank-separated blocks of one support are also separated in physical wire
order. This is what makes their union an order-preserving merge embedding. -/
theorem blockOf_lt_of_separated {N : Nat} (s : Finset (Fin N))
    {lo hi lo' hi' : Nat} (hsep : hi ≤ lo') {a b : Fin N}
    (ha : a ∈ blockOf s lo hi) (hb : b ∈ blockOf s lo' hi') : a < b := by
  have har := mem_blockOf.mp ha
  have hbr := mem_blockOf.mp hb
  have hrank : rankIn s a < rankIn s b := by omega
  by_contra hnot
  have hba : b ≤ a := le_of_not_gt hnot
  rcases lt_or_eq_of_le hba with hlt | heq
  · have := rankIn_lt_rankIn (blockOf_subset hb) hlt
    omega
  · subst b
    omega

theorem rankInterval_endpoint_pair_ordered {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hspan : 64 ≤ hi - lo) {a b : Fin N}
    (ha : a ∈ blockOf s lo (lo + 32))
    (hb : b ∈ blockOf s (hi - 32) hi) : a < b := by
  exact blockOf_lt_of_separated s (lo := lo) (hi := lo + 32)
    (lo' := hi - 32) (hi' := hi) (by omega) ha hb

/-- In a shifted child fringe, pair the last 32 ranks of the prefix with the
first 32 ranks of the suffix. The pair support is fixed by the sender wires,
has size 64, and does not depend on input values. -/
theorem upFringe_endpoint_pair {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hπeven : 2 ∣ π) (hcard64 : 64 ∣ s.card)
    (hhalf32 : (π / 2) % 64 = 32) (hπcard : π ≤ s.card) :
    Disjoint (blockOf s (π / 2 - 32) (π / 2))
      (blockOf s (s.card - π / 2) (s.card - π / 2 + 32)) ∧
      (blockOf s (π / 2 - 32) (π / 2)).card = 32 ∧
      (blockOf s (s.card - π / 2) (s.card - π / 2 + 32)).card = 32 ∧
      (blockOf s (π / 2 - 32) (π / 2) ∪
        blockOf s (s.card - π / 2) (s.card - π / 2 + 32)).card = 64 := by
  have hhalf : 32 ≤ π / 2 := by
    have := Nat.mod_add_div (π / 2) 64
    rw [hhalf32] at this
    omega
  have htail : π / 2 ≤ s.card - π / 2 := by
    have hπeq : 2 * (π / 2) = π := Nat.mul_div_cancel' hπeven
    omega
  have hprefix : (blockOf s (π / 2 - 32) (π / 2)).card = 32 := by
    rw [blockOf_card (by omega)]
    omega
  have hsuffix : (blockOf s (s.card - π / 2) (s.card - π / 2 + 32)).card = 32 := by
    rw [blockOf_card (by omega)]
    omega
  have hdisj : Disjoint (blockOf s (π / 2 - 32) (π / 2))
      (blockOf s (s.card - π / 2) (s.card - π / 2 + 32)) :=
    disjoint_blockOf (by omega)
  refine ⟨hdisj, hprefix, hsuffix, ?_⟩
  rw [Finset.card_union_of_disjoint hdisj, hprefix, hsuffix]

theorem upFringe_endpoint_pair_ordered {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hπeven : 2 ∣ π) (hhalf32 : (π / 2) % 64 = 32) (hπcard : π ≤ s.card)
    {a b : Fin N}
    (ha : a ∈ blockOf s (π / 2 - 32) (π / 2))
    (hb : b ∈ blockOf s (s.card - π / 2) (s.card - π / 2 + 32)) : a < b := by
  have hπeq : 2 * (π / 2) = π := Nat.mul_div_cancel' hπeven
  exact blockOf_lt_of_separated s (lo := π / 2 - 32) (hi := π / 2)
    (lo' := s.card - π / 2) (hi' := s.card - π / 2 + 32) (by omega) ha hb

/-- Fixed support chosen for the pair of endpoint half-fragments in a shifted
up-fringe. -/
def upFringePairSupport {N : Nat} (s : Finset (Fin N)) (π : Nat) : Finset (Fin N) :=
  blockOf s (π / 2 - 32) (π / 2) ∪
    blockOf s (s.card - π / 2) (s.card - π / 2 + 32)

theorem upFringePairSupport_card {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hπeven : 2 ∣ π) (hcard64 : 64 ∣ s.card)
    (hhalf32 : (π / 2) % 64 = 32) (hπcard : π ≤ s.card) :
    (upFringePairSupport s π).card = 64 := by
  have h := upFringe_endpoint_pair s π hπeven hcard64 hhalf32 hπcard
  simpa [upFringePairSupport] using h.2.2.2

theorem upFringePairSupport_subset {N : Nat} (s : Finset (Fin N)) (π : Nat) :
    upFringePairSupport s π ⊆ s := by
  unfold upFringePairSupport
  exact Finset.union_subset blockOf_subset blockOf_subset

/-- Pair supports chosen from disjoint child senders stay disjoint. -/
theorem upFringePairSupport_disjoint {N : Nat} {s s' : Finset (Fin N)} (π π' : Nat)
    (hdisj : Disjoint s s') : Disjoint (upFringePairSupport s π) (upFringePairSupport s' π') :=
  hdisj.mono (upFringePairSupport_subset s π) (upFringePairSupport_subset s' π')

/-- Concrete fixed supports for the two endpoint fragments of an ordinary
scheduled sender's up-fringe. -/
def scheduledUpFringePairSupport {d tf : Nat} (F : FlowSizes d tf) (t : Nat)
    (q : KBag 64 d) : Finset (Fin (64 ^ d)) :=
  upFringePairSupport (wireSets F t q) (F.up q.l t)

/-- Distinct scheduled senders produce disjoint fixed repair supports. In
particular, the 64 child-fringe pairs of a receiver can run in parallel. -/
theorem scheduledUpFringePairSupport_disjoint {d tf : Nat}
    (F : FlowSizes d tf) {t : Nat} (ht : t ≤ tf)
    (q q' : KBag 64 d) (hne : q ≠ q') :
    Disjoint (scheduledUpFringePairSupport F t q)
      (scheduledUpFringePairSupport F t q') := by
  unfold scheduledUpFringePairSupport
  exact upFringePairSupport_disjoint _ _ (wireSets_disjoint F ht q q' hne)

/-- When the down-flow is packet-aligned, both endpoints of every child cut
have the same packet residue as the initial half-fringe endpoint. -/
theorem downSet_cut_residues {π τ j : Nat} (hτ : 64 ∣ τ) :
    (π / 2 + j * τ) % 64 = (π / 2) % 64 ∧
      (π / 2 + (j + 1) * τ) % 64 = (π / 2) % 64 := by
  have hj : (j * τ) % 64 = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hτ j)
  have hj' : ((j + 1) * τ) % 64 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hτ (j + 1))
  constructor
  · rw [Nat.add_mod, hj, Nat.add_zero]
    simp
  · rw [Nat.add_mod, hj', Nat.add_zero]
    simp

/-- The two parent-port fringes are the first and last half-fringe rank
intervals in `WireFlow.upSet`. -/
theorem upSet_rank_cut {N : Nat} (s : Finset (Fin N)) (π : Nat)
    {w : Fin N} (hw : w ∈ upSet s π) :
    (w ∈ s ∧ rankIn s w < π / 2) ∨
      (w ∈ s ∧ s.card - π / 2 ≤ rankIn s w ∧ rankIn s w < s.card) := by
  simp only [upSet, Finset.mem_union] at hw
  rcases hw with hw | hw
  · left
    have h := mem_blockOf.mp hw
    exact ⟨h.1, h.2.2⟩
  · right
    have h := mem_blockOf.mp hw
    exact ⟨h.1, h.2.1, h.2.2⟩

/-- Number of packet cells (64 consecutive rank positions) cut partially at
the two endpoints of a nonempty half-open rank interval. -/
def intervalBoundaryFragments (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0 else (if lo % 64 = 0 then 0 else 1) +
    (if hi % 64 = 0 then 0 else 1)

/-- For a packet-multiple interval, its two endpoint residues agree. -/
theorem packet_interval_endpoint_residue {lo hi : Nat} (hle : lo ≤ hi)
    (hdiv : 64 ∣ hi - lo) : hi % 64 = lo % 64 := by
  have hdecomp : hi = lo + (hi - lo) := by omega
  have hlen : (hi - lo) % 64 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  rw [hdecomp, Nat.add_mod, hlen, Nat.add_zero]
  simp

/-- A positive packet-multiple rank interval with endpoint residue 0 is
aligned; with residue 32 it cuts exactly two packet cells in half. -/
theorem packet_interval_boundary_fragments {lo hi : Nat} (hlt : lo < hi)
    (hdiv : 64 ∣ hi - lo) (hres : lo % 64 = 0 ∨ lo % 64 = 32) :
    intervalBoundaryFragments lo hi = if lo % 64 = 0 then 0 else 2 := by
  have hres' := packet_interval_endpoint_residue (by omega) hdiv
  unfold intervalBoundaryFragments
  rw [if_neg (by omega), hres']
  rcases hres with h0 | h32
  · simp [h0]
  · simp [h32]

/-- Each 64-rank child block in `WireFlow.downSet` is packet-multiple and
inherits the receiver's half-fringe endpoint residue. -/
theorem downSet_boundary_fragments {N : Nat} (s : Finset (Fin N))
    (π τ j : Nat) (hτ : 64 ∣ τ) (hres : (π / 2) % 64 = 0 ∨ (π / 2) % 64 = 32)
    (hpos : 0 < τ) :
    intervalBoundaryFragments (π / 2 + j * τ) (π / 2 + (j + 1) * τ) =
      if (π / 2) % 64 = 0 then 0 else 2 := by
  have hlen : (π / 2 + (j + 1) * τ) - (π / 2 + j * τ) = τ := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hlt : π / 2 + j * τ < π / 2 + (j + 1) * τ := by
    have := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self j) hpos
    omega
  have hdiv : 64 ∣ (π / 2 + (j + 1) * τ) - (π / 2 + j * τ) := by
    rw [hlen]
    exact hτ
  have hstart : (π / 2 + j * τ) % 64 = (π / 2) % 64 :=
    (downSet_cut_residues hτ).1
  have hresStart : (π / 2 + j * τ) % 64 = 0 ∨
      (π / 2 + j * τ) % 64 = 32 := by rw [hstart]; exact hres
  simpa [intervalBoundaryFragments, hlt, hstart] using
    packet_interval_boundary_fragments hlt hdiv hresStart

/-- The first and last half-fringe intervals in `upSet` together contribute
two partial packet cells exactly in the half-packet-shifted case. -/
theorem upSet_boundary_fragments {N : Nat} (s : Finset (Fin N)) (π : Nat)
    (hcard : 64 ∣ s.card) (hhalf : 0 < π / 2) (hle : π / 2 ≤ s.card)
    (hres : (π / 2) % 64 = 0 ∨ (π / 2) % 64 = 32) :
    intervalBoundaryFragments 0 (π / 2) +
      intervalBoundaryFragments (s.card - π / 2) s.card =
        if (π / 2) % 64 = 0 then 0 else 2 := by
  have hc0 : s.card % 64 = 0 := Nat.mod_eq_zero_of_dvd hcard
  have htail : s.card = (s.card - π / 2) + π / 2 := by omega
  have htailres : (s.card - π / 2) % 64 = (π / 2) % 64 := by
    rcases hres with hzero | h32
    · have hhdiv : 64 ∣ π / 2 := Nat.dvd_of_mod_eq_zero hzero
      have hdiv : 64 ∣ s.card - π / 2 := Nat.dvd_sub hcard hhdiv
      rw [Nat.mod_eq_zero_of_dvd hdiv, hzero]
    · have hsum : ((s.card - π / 2) % 64 + (π / 2) % 64) % 64 = 0 := by
        rw [← Nat.add_mod, ← htail]
        exact hc0
      have hbound := Nat.mod_lt (s.card - π / 2) (by norm_num : 0 < 64)
      rw [h32] at hsum
      omega
  have htaillen : s.card - π / 2 < s.card := by omega
  have hprefix : intervalBoundaryFragments 0 (π / 2) =
      if (π / 2) % 64 = 0 then 0 else 1 := by
    unfold intervalBoundaryFragments
    rw [if_neg (by omega)]
    norm_num
  have hsuffix : intervalBoundaryFragments (s.card - π / 2) s.card =
      if (π / 2) % 64 = 0 then 0 else 1 := by
    unfold intervalBoundaryFragments
    rw [if_neg (by omega)]
    simp [hc0, htailres]
  rw [hprefix, hsuffix]
  rcases hres with h0 | h32
  · simp [h0]
  · simp [h32]

/-- Aggregate port accounting: a shifted parent down-cut costs at most two
half-packet pieces; 64 shifted child up-fringes cost at most 128. The two
cases cannot occur together for the scheduled adjacent levels. -/
theorem receiver_fragment_budget {d t level : Nat} {ap up np ac uc nc : Nat}
    (parentShape : RefinedNodeShape d t (level - 1) ap up np)
    (childShape : RefinedNodeShape d t (level + 1) ac uc nc) :
    (if HalfMisaligned up then 2 else 0) +
      (if HalfMisaligned uc then 64 * 2 else 0) ≤ 128 := by
  classical
  have hnot : ¬ (HalfMisaligned up ∧ HalfMisaligned uc) := by
    intro h
    exact receiver_no_simultaneous_misalignment parentShape childShape h.1 h.2
  by_cases hp : HalfMisaligned up <;> by_cases hc : HalfMisaligned uc <;>
    simp_all

/-- The same aggregate accounting for concrete scheduled flows. -/
theorem scheduled_receiver_fragment_budget
    (d : Nat) (hd : 7 ≤ d) (t level : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    (if HalfMisaligned (flowUp7 d hd (level - 1) t) then 2 else 0) +
      (if HalfMisaligned (flowUp7 d hd (level + 1) t) then 64 * 2 else 0) ≤ 128 := by
  classical
  have hp := node_shape_refined d hd t (level - 1) ht2 ht
  have hc := node_shape_refined d hd t (level + 1) ht2 ht
  exact receiver_fragment_budget hp hc

/-- Apart from singleton and empty bags, every scheduled packet count either
tiles exactly into groups of 64 or has exactly 63 packets left over after
tiling. In the latter case the cohort has at least 4095 packets. This is the
shape needed to apply a 64-run merge tree to all full groups while isolating a
small, explicit tail. -/
theorem flowA7_packet_count_block_shape (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    flowA7 d hd i t / 64 = 0 ∨
      flowA7 d hd i t / 64 = 1 ∨
      64 ∣ flowA7 d hd i t / 64 ∨
      (flowA7 d hd i t / 64) % 64 = 63 ∧
        4095 ≤ flowA7 d hd i t / 64 := by
  let c := flowA7 d hd i t / 64
  have hfactor := flowA7_scheduled_packet_factorization d hd t i ht2 ht
  change c = 0 ∨ c = 1 ∨ 64 ∣ c ∨ c % 64 = 63 ∧ 4095 ≤ c
  rcases hfactor with hz | hp | hn
  · left
    simp [c, hz]
  · rcases hp with ⟨e, he⟩
    have hc : c = 64 ^ e := by simpa [c] using he
    rw [hc]
    by_cases he0 : e = 0
    · right; left
      simp [he0]
    · right; right; left
      have hepos : 0 < e := Nat.pos_of_ne_zero he0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0
      refine ⟨64 ^ k, ?_⟩
      simp [pow_succ, Nat.mul_comm]
  · rcases hn with ⟨h, r, hrlo, hrhi, he⟩
    have hc : c = 64 ^ h * (64 ^ r - 1) := by simpa [c] using he
    rw [hc]
    by_cases hh : h = 0
    · subst h
      right; right; right
      have hr : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        norm_num [Nat.pow_succ] at *
    · right; right; left
      have hpos : 0 < h := Nat.pos_of_ne_zero hh
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh
      refine ⟨64 ^ k * (64 ^ r - 1), ?_⟩
      rw [pow_succ]
      ring

theorem packetTailFraction_bound {c : Nat} (hc : 4095 ≤ c) :
    (63 : Rat) / c ≤ (7 : Rat) / 455 := by
  have hcpos : (0 : Rat) < c := by
    exact_mod_cast (show 0 < c by omega)
  rw [div_le_div_iff₀ hcpos (by norm_num : (0 : Rat) < 455)]
  have hcCast : (4095 : Rat) ≤ c := by exact_mod_cast hc
  norm_num
  nlinarith

/-- The only non-full 64-packet block in an ordinary scheduled bag has at
most `7/455` of that bag's packets. -/
theorem flowA7_packet_tail_fraction_le (d : Nat) (hd : 7 ≤ d) (t i : Nat)
    (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (htail : (flowA7 d hd i t / 64) % 64 = 63) :
    (63 : Rat) / ((flowA7 d hd i t / 64 : Nat) : Rat) ≤ (7 : Rat) / 455 := by
  have hshape := flowA7_packet_count_block_shape d hd t i ht2 ht
  rcases hshape with hzero | hone | hdiv | hrem
  · rw [hzero] at htail
    norm_num at htail
  · rw [hone] at htail
    norm_num at htail
  · have hmod : (flowA7 d hd i t / 64) % 64 = 0 :=
      Nat.mod_eq_zero_of_dvd hdiv
    rw [hmod] at htail
    norm_num at htail
  · exact packetTailFraction_bound hrem.2

end Chvatal.PacketAlignment
