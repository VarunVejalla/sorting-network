import PacketInduction

/-! The actual §7 flow has only two receiver packet-count residues modulo 64.
This closes the residue cases needed to apply the proved 64-run and 63-run
merge batches to every nonzero active receiver. -/

namespace Chvatal.PacketAlignment

open Chvatal

private theorem residue_pow_diff_factor (g h : Nat) (hhg : h ≤ g) :
    64 ^ (g + 1) - 64 ^ (h + 1) =
      64 * (64 ^ h * (64 ^ (g - h) - 1)) := by
  have hexp : g + 1 = (h + 1) + (g - h) := by omega
  calc
    64 ^ (g + 1) - 64 ^ (h + 1) =
        64 ^ (h + 1) * 64 ^ (g - h) - 64 ^ (h + 1) := by
          rw [hexp, pow_add, pow_succ]
    _ = 64 ^ (h + 1) * (64 ^ (g - h) - 1) := by
          simpa using (Nat.mul_sub_left_distrib
            (64 ^ (h + 1)) (64 ^ (g - h)) 1).symm
    _ = 64 * (64 ^ h * (64 ^ (g - h) - 1)) := by
          rw [pow_succ]
          ring

private theorem residue_pow_diff_quotient (g h : Nat) (hhg : h ≤ g) :
    (64 ^ (g + 1) - 64 ^ (h + 1)) / 64 =
      64 ^ h * (64 ^ (g - h) - 1) := by
  rw [residue_pow_diff_factor g h hhg]
  exact Nat.mul_div_right _ (by norm_num : 0 < 64)

private theorem residue_pow_diff_quotient_mod (g h : Nat) (hhg : h ≤ g)
    (hneq : h < g) :
    ((64 ^ (g + 1) - 64 ^ (h + 1)) / 64) % 64 =
      if h = 0 then 63 else 0 := by
  rw [residue_pow_diff_quotient g h hhg]
  by_cases hh : h = 0
  · subst h
    simp only [pow_zero, Nat.one_mul, Nat.sub_zero]
    have hg : 1 ≤ g := by omega
    have hmod : 64 ^ g % 64 = 0 := Nat.mod_eq_zero_of_dvd
      (Nat.pow_dvd_pow 64 (show 1 ≤ g by omega))
    have hpos : 1 ≤ 64 ^ g := Nat.one_le_pow _ _ (by norm_num)
    have hdecomp := Nat.mod_add_div (64 ^ g) 64
    rw [hmod] at hdecomp
    have hpow : 64 * (64 ^ g / 64) = 64 ^ g := by omega
    have hquot : 1 ≤ 64 ^ g / 64 := by omega
    have hsub : 64 ^ g - 1 = 64 * (64 ^ g / 64 - 1) + 63 := by omega
    rw [hsub]
    simp [Nat.add_mod]
  · have hh1 : 1 ≤ h := by omega
    have hdiv : 64 ∣ 64 ^ h := Nat.pow_dvd_pow 64 (by omega)
    have hmul : 64 ∣ 64 ^ h * (64 ^ (g - h) - 1) := dvd_mul_of_dvd_left hdiv _
    simp [hh, Nat.mod_eq_zero_of_dvd hmul]

private theorem nodeShape_packetCount_residue {d t i a u n : Nat}
    (hshape : NodeShape d t i a u n) (hlarge : 128 ≤ a) :
    (a / 64) % 64 = 0 ∨ (a / 64) % 64 = 63 := by
  cases hshape with
  | off => omega
  | topDesc g _ _ _ =>
      by_cases hg : g = 0
      · subst g
        norm_num at hlarge
      · have hg1 : 1 ≤ g := by omega
        rw [show 64 ^ (g + 1) = 64 ^ g * 64 by rw [pow_succ]]
        simp only [Nat.mul_div_left _ (by norm_num : 0 < 64)]
        exact Or.inl (Nat.mod_eq_zero_of_dvd
          (Nat.pow_dvd_pow 64 (show 1 ≤ g by omega)))
  | topRise f _ _ =>
      rw [show 64 ^ (6 + f) = 64 ^ (5 + f) * 64 by
        rw [show 6 + f = (5 + f) + 1 by omega, pow_succ]]
      simp only [Nat.mul_div_left _ (by norm_num : 0 < 64)]
      exact Or.inl (Nat.mod_eq_zero_of_dvd
        (Nat.pow_dvd_pow 64 (show 1 ≤ 5 + f by omega)))
  | mid g _ _ =>
      have hq : (64 ^ (7 + g) - 64 ^ (1 + g)) / 64 =
          64 ^ g * (64 ^ 6 - 1) := by
        simpa only [show 7 + g = (6 + g) + 1 by omega,
          show 1 + g = g + 1 by omega,
          show 6 + g - g = 6 by omega] using
          residue_pow_diff_quotient (6 + g) g (by omega)
      rw [hq]
      by_cases hg : g = 0
      · subst g
        norm_num
      · have hg1 : 1 ≤ g := by omega
        exact Or.inl (Nat.mod_eq_zero_of_dvd
          (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 64 (by omega)) _))
  | botDesc g h hgh _ _ _ =>
      have hq := residue_pow_diff_quotient_mod g h (by omega) (by omega)
      rw [hq]
      by_cases hh : h = 0 <;> simp [hh]
  | botRise g h hle =>
      by_cases heq : g = h
      · subst g
        norm_num at hlarge
      · have hq := residue_pow_diff_quotient_mod g h (by omega) (by omega)
        rw [hq]
        by_cases hh : h = 0 <;> simp [hh]

private theorem nodeShape_active_size {d t i a u n : Nat}
    (ht2 : 2 ≤ t) (ht : t < tf7 d) (hshape : NodeShape d t i a u n) :
    a = 0 ∨ 128 ≤ a := by
  cases hshape with
  | off => exact Or.inl rfl
  | topDesc g hexp hinner _ =>
      by_cases hg : g = 0
      · subst g
        have htop := exp_top d t ht2 (le_of_lt ht)
        have halpha : alpha7 d t ≤ i := hinner.2.1
        omega
      · have hg1 : 1 ≤ g := by omega
        have hpow : 2 ≤ g + 1 := by omega
        have hlarge : 128 ≤ 64 ^ 2 := by norm_num
        exact Or.inr (le_trans hlarge (Nat.pow_le_pow_right (by norm_num) hpow))
  | topRise f _ _ =>
      have hlarge : 128 ≤ 64 ^ 2 := by norm_num
      have hpow : 2 ≤ 6 + f := by omega
      exact Or.inr (le_trans hlarge (Nat.pow_le_pow_right (by norm_num) hpow))
  | mid g _ _ =>
      have hfactor : 64 ^ (7 + g) - 64 ^ (1 + g) =
          64 * (64 ^ g * (64 ^ 6 - 1)) := by
        rw [show 7 + g = (6 + g) + 1 by omega,
          show 1 + g = g + 1 by omega]
        rw [residue_pow_diff_factor (6 + g) g (by omega)]
        simp
      have hone : 1 ≤ 64 ^ g := Nat.one_le_pow _ _ (by norm_num)
      have hprod := Nat.mul_le_mul_right (64 ^ 6 - 1) hone
      have hfactorLower : 64 ^ 6 - 1 ≤ 64 ^ g * (64 ^ 6 - 1) := by simpa using hprod
      have hlarge : 128 ≤ 64 * (64 ^ 6 - 1) := by norm_num
      exact Or.inr (hfactor ▸ le_trans hlarge (Nat.mul_le_mul_left 64 hfactorLower))
  | botDesc g h hgh _ _ _ =>
      have hfactor : 64 ^ (g + 1) - 64 ^ (h + 1) =
          64 * (64 ^ h * (64 ^ (g - h) - 1)) :=
        residue_pow_diff_factor g h (by omega)
      have hpow : 4096 ≤ 64 ^ (g - h) := by
        calc 4096 = 64 ^ 2 := by norm_num
          _ ≤ 64 ^ (g - h) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hterm : 4095 ≤ 64 ^ (g - h) - 1 := by omega
      have hone : 1 ≤ 64 ^ h := Nat.one_le_pow _ _ (by norm_num)
      have hprod := Nat.mul_le_mul_right (64 ^ (g - h) - 1) hone
      have hfactorLower : 4095 ≤ 64 ^ h * (64 ^ (g - h) - 1) := by
        exact le_trans hterm (by simpa using hprod)
      have hlarge : 128 ≤ 64 * 4095 := by norm_num
      exact Or.inr (hfactor ▸ le_trans hlarge (Nat.mul_le_mul_left 64 hfactorLower))
  | botRise g h hle =>
      by_cases heq : g = h
      · subst g
        exact Or.inl (by simp)
      · have hfactor : 64 ^ (g + 1) - 64 ^ (h + 1) =
            64 * (64 ^ h * (64 ^ (g - h) - 1)) :=
          residue_pow_diff_factor g h (by omega)
        have hpow : 64 ≤ 64 ^ (g - h) := by
          calc 64 = 64 ^ 1 := by norm_num
            _ ≤ 64 ^ (g - h) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hterm : 63 ≤ 64 ^ (g - h) - 1 := by omega
        have hone : 1 ≤ 64 ^ h := Nat.one_le_pow _ _ (by norm_num)
        have hprod := Nat.mul_le_mul_right (64 ^ (g - h) - 1) hone
        have hfactorLower : 63 ≤ 64 ^ h * (64 ^ (g - h) - 1) :=
          le_trans hterm (by simpa using hprod)
        have hlarge : 128 ≤ 64 * 63 := by norm_num
        exact Or.inr (hfactor ▸ le_trans hlarge (Nat.mul_le_mul_left 64 hfactorLower))

/-- Every nonzero actual receiver at an interior level has packet count
congruent to 0 or 63 modulo 64. -/
theorem flowA7_receiver_packetCount_residue {d : Nat} (hd : 7 ≤ d)
    (t l : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) (hl : 1 ≤ l) :
    (flowA7 d hd l (t + 1) / 64) % 64 = 0 ∨
      (flowA7 d hd l (t + 1) / 64) % 64 = 63 := by
  by_cases hfinal : t + 1 = tf7 d
  · rw [hfinal, flowA7_tf d hd]
    by_cases hlevel : l = d - 6
    · subst l
      norm_num
    · simp [hlevel]
  · have ht' : t + 1 < tf7 d := by omega
    have hshape := (flow7_shape d hd (t + 1) l (by omega) ht').1
    rcases nodeShape_active_size (by omega) ht' hshape with hzero | hlarge
    · simp [hzero]
    · exact nodeShape_packetCount_residue hshape hlarge

end Chvatal.PacketAlignment
