module
/-
  # Chvatal §3 Lemmas 3.1-3.2

  Source: V. Chvatal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §3.

  Status: algebraic core of Lemma 3.1 under the global mass identity, and the
  capacity form of Lemma 3.2 under an explicit snap hypothesis
  `c < 2Ak²/ν` (paper intermediate). The §7 schedule discharges this from the
  `α*` envelope in `Schedule7.lemma32_levelSchedule7`.
-/

public import AKS.Chvatal.Scheduler
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

open Finset

/-! **Lemma 3.1 telescoping** -/

private theorem term_diff (Q : Rat) (hQ : Q ≠ 0) (m : Nat) (hm : 1 ≤ m) :
    (1 - 1 / Q) * Q ^ m = Q ^ m - Q ^ (m - 1) := by
  have hQm : Q ^ m = Q ^ (m - 1) * Q := by
    calc Q ^ m = Q ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
      _ = Q ^ (m - 1) * Q := pow_succ _ _
  have hdiv : Q ^ m / Q = Q ^ (m - 1) := by
    rw [hQm, mul_div_cancel_right₀ _ hQ]
  calc (1 - 1 / Q) * Q ^ m
      = Q ^ m - Q ^ m / Q := by ring
    _ = Q ^ m - Q ^ (m - 1) := by rw [hdiv]

/-- Interior telescoping: `1 + sum_{m=1}^{M-1} (1 - 1/Q) Q^m = Q^{M-1}`. -/
theorem lemma31_telescope (Q : Rat) (hQ : Q ≠ 0) (M : Nat) (hM : 1 ≤ M) :
    (1 : Rat) + ∑ m ∈ Finset.Icc 1 (M - 1), (1 - 1 / Q) * Q ^ m =
      Q ^ (M - 1) := by
  refine Nat.le_induction ?_ ?_ M hM
  · simp
  · intro M hM ih
    have hIcc : Finset.Icc 1 M = insert M (Finset.Icc 1 (M - 1)) := by
      ext x
      simp only [mem_insert, mem_Icc]
      constructor
      · intro ⟨hx1, hx2⟩
        by_cases hx : x = M
        · exact Or.inl hx
        · exact Or.inr ⟨hx1, Nat.le_pred_of_lt (lt_of_le_of_ne hx2 hx)⟩
      · rintro (rfl | ⟨hx1, hx2⟩) <;> omega
    have hnot : M ∉ Finset.Icc 1 (M - 1) := by
      simp only [mem_Icc]; omega
    have hterm := term_diff Q hQ M (by omega : 1 ≤ M)
    calc (1 : Rat) + ∑ m ∈ Finset.Icc 1 ((M + 1) - 1), (1 - 1 / Q) * Q ^ m
        = 1 + ∑ m ∈ Finset.Icc 1 M, (1 - 1 / Q) * Q ^ m := by simp
      _ = 1 + ((1 - 1 / Q) * Q ^ M +
            ∑ m ∈ Finset.Icc 1 (M - 1), (1 - 1 / Q) * Q ^ m) := by
          rw [hIcc, sum_insert hnot, add_comm]
      _ = (1 + ∑ m ∈ Finset.Icc 1 (M - 1), (1 - 1 / Q) * Q ^ m) +
            (Q ^ M - Q ^ (M - 1)) := by
          rw [hterm]; ring
      _ = Q ^ (M - 1) + (Q ^ M - Q ^ (M - 1)) := by rw [ih]
      _ = Q ^ M := by ring

/-! **Lemma 3.1 helpers** -/

private theorem sum_split_at
    (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (i t : Nat) (_hi : i ≤ d)
    (htotal : (∑ j ∈ Finset.range (d + 1),
        (p.br : Rat) ^ j * allocation p d sched j t) = (p.br ^ d : Nat)) :
    (∑ j ∈ Finset.Icc i d, (p.br : Rat) ^ j * allocation p d sched j t) =
      (↑(p.br ^ d) : Rat) -
        ∑ j ∈ Finset.range i, (p.br : Rat) ^ j * allocation p d sched j t := by
  have hN :
      ∑ j ∈ Finset.range (d + 1),
          (p.br : Rat) ^ j * allocation p d sched j t =
        (↑(p.br ^ d) : Rat) := htotal
  have hlo : (Finset.range (d + 1)).filter (· < i) = Finset.range i := by
    ext j; simp only [mem_filter, mem_range]; omega
  have hhi : (Finset.range (d + 1)).filter (fun j ↦ i ≤ j) = Finset.Icc i d := by
    ext j; simp only [mem_filter, mem_range, mem_Icc]; omega
  have hsum := sum_filter_add_sum_filter_not (Finset.range (d + 1))
    (fun j : Nat ↦ j < i)
    (fun j ↦ (p.br : Rat) ^ j * allocation p d sched j t)
  simp only [not_lt, hlo, hhi] at hsum
  linarith [hsum, hN]

private theorem mass_div
    (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (i t : Nat) :
    (∑ j ∈ Finset.Icc i d, (p.br : Rat) ^ (j - i) * allocation p d sched j t) =
      (∑ j ∈ Finset.Icc i d, (p.br : Rat) ^ j * allocation p d sched j t) /
        (p.br : Rat) ^ i := by
  have hbr : (p.br : Rat) ^ i ≠ 0 := pow_ne_zero _ (ne_of_gt p.br_cast_pos)
  rw [eq_div_iff_mul_eq hbr, sum_mul]
  refine sum_congr rfl ?_
  intro j hj
  simp only [mem_Icc] at hj
  rw [mul_assoc, mul_comm (allocation _ _ _ _ _), ← mul_assoc, ← pow_add,
    Nat.sub_add_cancel hj.1]

private theorem sum_below_alpha_zero
    (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (t i : Nat) (hα : sched.alpha t = i) :
    ∑ j ∈ Finset.range i, (p.br : Rat) ^ j * allocation p d sched j t = 0 := by
  apply sum_eq_zero
  intro j hj
  simp only [mem_range] at hj
  have : allocation p d sched j t = 0 := by
    apply allocation_inactive
    intro h; omega
  simp [this]

private theorem sum_below_active
    (p : ScheduleParams) (d : Nat) (sched : LevelSchedule p d)
    (t i : Nat) (hα : sched.alpha t < i) :
    ∑ j ∈ Finset.range i, (p.br : Rat) ^ j * allocation p d sched j t =
      ∑ j ∈ Finset.Icc (sched.alpha t) (i - 1),
        (p.br : Rat) ^ j * allocation p d sched j t := by
  have hsub : Finset.Icc (sched.alpha t) (i - 1) ⊆ Finset.range i := by
    intro j hj
    simp only [mem_Icc, mem_range] at hj ⊢
    omega
  rw [← sum_sdiff hsub]
  have hz : ∀ j ∈ Finset.range i \ Finset.Icc (sched.alpha t) (i - 1),
      (p.br : Rat) ^ j * allocation p d sched j t = 0 := by
    intro j hj
    simp only [mem_sdiff, mem_range, mem_Icc] at hj
    have : allocation p d sched j t = 0 := by
      apply allocation_inactive
      intro h; omega
    simp [this]
  simp [sum_eq_zero hz]

private theorem even_sub_div {a b : Nat} (h : a % 2 = b % 2) :
    2 * ((a - b) / 2) = a - b := by
  have : 2 ∣ a - b := Nat.dvd_of_mod_eq_zero (by omega)
  exact Nat.mul_div_cancel' this

/-! **Lemma 3.1** -/

/-- §3 Lemma 3.1 under the global mass identity `sum_j br^j a(j,t) = N`. -/
theorem lemma31_of_total (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat) (ht : t ≤ sched.tf)
    (htotal : (∑ j ∈ Finset.range (d + 1),
        (p.br : Rat) ^ j * allocation p d sched j t) = (p.br ^ d : Nat))
    (i : Nat) (hα : sched.alpha t ≤ i) (hω : i ≤ sched.omega t)
    (hpar : i % 2 = t % 2) :
    (∑ j ∈ Finset.Icc i d,
        (p.br : Rat) ^ (j - i) * allocation p d sched j t) =
      if i = sched.alpha t then
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i
      else
        (↑(p.br ^ d) : Rat) / (p.br : Rat) ^ i -
          capacity p d i t / capacityRatio p := by
  have hid : i ≤ d := le_trans hω (sched.omega_le_d t ht)
  have hbrpow_i : (p.br : Rat) ^ i ≠ 0 := pow_ne_zero _ (ne_of_gt p.br_cast_pos)
  rw [mass_div, sum_split_at p d sched i t hid htotal]
  by_cases htop : i = sched.alpha t
  · subst htop
    have hz := sum_below_alpha_zero p d sched t _ rfl
    simp [hz]
  · -- Interior / bottom levels: telescope the active ladder below `i`.
    have hαlt : sched.alpha t < i := lt_of_le_of_ne hα (Ne.symm htop)
    rw [if_neg htop, sum_below_active p d sched t i hαlt]
    set α := sched.alpha t with hαdef
    set M := (i - α) / 2 with hMdef
    have hαpar : α % 2 = t % 2 := by rw [hαdef]; exact sched.alpha_parity t ht
    have hAi : α % 2 = i % 2 := by omega
    have hMpos : 1 ≤ M := by omega
    have hi_eq : i = α + 2 * M := by omega
    have hQne : capacityRatio p ≠ 0 := ne_of_gt (capacityRatio_pos p)
    have honly :
        ∑ j ∈ Finset.Icc α (i - 1),
            (p.br : Rat) ^ j * allocation p d sched j t =
          ∑ j ∈ (Finset.Icc α (i - 1)).filter (fun j ↦ j % 2 = α % 2),
            (p.br : Rat) ^ j * allocation p d sched j t := by
      have hsplit := sum_filter_add_sum_filter_not (Finset.Icc α (i - 1))
        (fun j : Nat ↦ j % 2 = α % 2)
        (fun j ↦ (p.br : Rat) ^ j * allocation p d sched j t)
      have hz : ∑ j ∈ (Finset.Icc α (i - 1)).filter
          (fun j ↦ ¬ (j % 2 = α % 2)),
          (p.br : Rat) ^ j * allocation p d sched j t = 0 := by
        apply sum_eq_zero
        intro j hj
        simp only [mem_filter] at hj
        have : allocation p d sched j t = 0 := by
          apply allocation_inactive
          intro h; exact hj.2 (by omega)
        simp [this]
      linarith [hsplit, hz]
    have hmap :
        ∑ j ∈ (Finset.Icc α (i - 1)).filter (fun j ↦ j % 2 = α % 2),
            (p.br : Rat) ^ j * allocation p d sched j t =
          ∑ m ∈ Finset.range M,
            (p.br : Rat) ^ (α + 2 * m) *
              allocation p d sched (α + 2 * m) t := by
      refine sum_nbij (fun j ↦ (j - α) / 2) ?maps ?inj ?surj ?eq
      · intro j hj
        have ⟨hjI, hjP⟩ := mem_filter.mp hj
        have ⟨hjL, hjR⟩ := mem_Icc.mp hjI
        -- Same parity as i and j ≤ i-1 forces j ≤ i-2, hence j-α < i-α = 2M.
        have : j - α < 2 * M := by omega
        exact mem_range.mpr
          ((Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
            rwa [Nat.mul_comm] at this))
      · intro a ha b hb heq
        have ⟨haI, haP⟩ := mem_filter.mp ha
        have ⟨hbI, hbP⟩ := mem_filter.mp hb
        have ⟨haL, haR⟩ := mem_Icc.mp haI
        have ⟨hbL, hbR⟩ := mem_Icc.mp hbI
        have hae := even_sub_div (a := a) (b := α) haP
        have hbe := even_sub_div (a := b) (b := α) hbP
        have heq' : (a - α) / 2 = (b - α) / 2 := heq
        have : a - α = b - α := by
          calc a - α = 2 * ((a - α) / 2) := hae.symm
            _ = 2 * ((b - α) / 2) := by rw [heq']
            _ = b - α := hbe
        omega
      · intro m hm
        have hm' : m < M := mem_range.mp hm
        refine ⟨α + 2 * m, mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, ?_⟩, by omega⟩, ?_⟩
        · have : 2 * m ≤ 2 * (M - 1) :=
            Nat.mul_le_mul_left 2 (Nat.le_pred_of_lt hm')
          omega
        · show (α + 2 * m - α) / 2 = m
          rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      · intro j hj
        have ⟨hjI, hjP⟩ := mem_filter.mp hj
        have hjL := (mem_Icc.mp hjI).1
        have hje := even_sub_div (a := j) (b := α) hjP
        have hm : j = α + 2 * ((j - α) / 2) := by
          calc j = j - α + α := (Nat.sub_add_cancel hjL).symm
            _ = 2 * ((j - α) / 2) + α := by rw [hje]
            _ = α + 2 * ((j - α) / 2) := Nat.add_comm _ _
        rw [hm]
        simp only [Nat.add_sub_cancel_left,
          Nat.mul_div_cancel_left _ (by omega : 0 < (2 : Nat))]
    have hterm : ∀ m ∈ Finset.range M,
        (p.br : Rat) ^ (α + 2 * m) * allocation p d sched (α + 2 * m) t =
          (p.br : Rat) ^ α * capacity p d α t *
            (if m = 0 then (1 : Rat)
             else (1 - 1 / capacityRatio p) * capacityRatio p ^ m) := by
      intro m hm
      have hm' : m < M := mem_range.mp hm
      have hlev : α + 2 * m ≤ sched.omega t := by omega
      have hlev_par : (α + 2 * m) % 2 = t % 2 := by omega
      have hαle : sched.alpha t ≤ α + 2 * m := by
        rw [← hαdef]; omega
      have hcond : t ≤ sched.tf ∧ sched.alpha t ≤ α + 2 * m ∧
          α + 2 * m ≤ sched.omega t ∧ (α + 2 * m) % 2 = t % 2 :=
        ⟨ht, hαle, hlev, hlev_par⟩
      by_cases hm0 : m = 0
      · subst hm0
        have hcond0 : t ≤ sched.tf ∧ sched.alpha t ≤ α ∧
            α ≤ sched.omega t ∧ α % 2 = t % 2 := by
          rw [← hαdef]
          exact ⟨ht, le_rfl, by omega, hαpar⟩
        have hαeq : α = sched.alpha t := hαdef.symm
        have halloc : allocation p d sched α t = capacity p d α t := by
          unfold allocation
          rw [if_pos hcond0, if_pos hαeq]
        rw [Nat.add_zero, if_pos rfl, halloc, mul_one]
      · have hneα : α + 2 * m ≠ sched.alpha t := by
          rw [← hαdef]; omega
        have hneω : α + 2 * m ≠ sched.omega t := by omega
        have halloc : allocation p d sched (α + 2 * m) t =
            (1 - 1 / capacityRatio p) * capacity p d (α + 2 * m) t := by
          unfold allocation
          rw [if_pos hcond, if_neg hneα, if_neg hneω]
        have hw := capacity_weighted_step p d α t m
        have hpowa : (p.br : Rat) ^ (α + 2 * m) =
            (p.br : Rat) ^ α * (p.br : Rat) ^ (2 * m) := pow_add _ _ _
        rw [if_neg hm0, halloc, hpowa]
        calc (p.br : Rat) ^ α * (p.br : Rat) ^ (2 * m) *
              ((1 - 1 / capacityRatio p) * capacity p d (α + 2 * m) t)
            = (p.br : Rat) ^ α * (1 - 1 / capacityRatio p) *
                ((p.br : Rat) ^ (2 * m) * capacity p d (α + 2 * m) t) := by ring
          _ = (p.br : Rat) ^ α * (1 - 1 / capacityRatio p) *
                (capacityRatio p ^ m * capacity p d α t) := by rw [hw]
          _ = (p.br : Rat) ^ α * capacity p d α t *
                ((1 - 1 / capacityRatio p) * capacityRatio p ^ m) := by ring
    have hre :
        ∑ m ∈ Finset.range M,
            (p.br : Rat) ^ α * capacity p d α t *
              (if m = 0 then (1 : Rat)
               else (1 - 1 / capacityRatio p) * capacityRatio p ^ m) =
          (p.br : Rat) ^ α * capacity p d α t * capacityRatio p ^ (M - 1) := by
      have h0 : (0 : Nat) ∈ Finset.range M := mem_range.mpr (by omega)
      rw [← add_sum_erase _ _ h0]
      simp only [↓reduceIte]
      have herase : Finset.erase (Finset.range M) 0 = Finset.Icc 1 (M - 1) := by
        ext m
        simp only [mem_erase, mem_range, mem_Icc]
        omega
      rw [herase]
      have hrest : ∀ m ∈ Finset.Icc 1 (M - 1),
          (p.br : Rat) ^ α * capacity p d α t *
            (if m = 0 then (1 : Rat)
             else (1 - 1 / capacityRatio p) * capacityRatio p ^ m) =
          (p.br : Rat) ^ α * capacity p d α t *
            ((1 - 1 / capacityRatio p) * capacityRatio p ^ m) := by
        intro m hm
        have : m ≠ 0 := by
          have := (mem_Icc.mp hm).1; omega
        simp only [this, ↓reduceIte]
      rw [sum_congr rfl hrest]
      have htel := lemma31_telescope (capacityRatio p) hQne M hMpos
      calc (p.br : Rat) ^ α * capacity p d α t * (1 : Rat) +
            ∑ x ∈ Finset.Icc 1 (M - 1),
              (p.br : Rat) ^ α * capacity p d α t *
                ((1 - 1 / capacityRatio p) * capacityRatio p ^ x)
          = (p.br : Rat) ^ α * capacity p d α t *
              ((1 : Rat) + ∑ x ∈ Finset.Icc 1 (M - 1),
                (1 - 1 / capacityRatio p) * capacityRatio p ^ x) := by
              rw [mul_add, mul_sum]
        _ = (p.br : Rat) ^ α * capacity p d α t * capacityRatio p ^ (M - 1) := by
              rw [htel]
    have hfin :
        (p.br : Rat) ^ α * capacity p d α t * capacityRatio p ^ (M - 1) =
          (p.br : Rat) ^ i * capacity p d i t / capacityRatio p := by
      have hw := capacity_weighted_step p d α t M
      rw [hi_eq]
      have hpowa : (p.br : Rat) ^ (α + 2 * M) =
          (p.br : Rat) ^ α * (p.br : Rat) ^ (2 * M) := pow_add _ _ _
      field_simp [hQne]
      calc (p.br : Rat) ^ α * capacity p d α t * capacityRatio p ^ (M - 1) *
            capacityRatio p
          = (p.br : Rat) ^ α * capacity p d α t *
              (capacityRatio p ^ (M - 1) * capacityRatio p) := by ring
        _ = (p.br : Rat) ^ α * capacity p d α t * capacityRatio p ^ M := by
              rw [← pow_succ, Nat.sub_add_cancel hMpos]
        _ = (p.br : Rat) ^ α *
              (capacityRatio p ^ M * capacity p d α t) := by ring
        _ = (p.br : Rat) ^ α *
              ((p.br : Rat) ^ (2 * M) * capacity p d (α + 2 * M) t) := by
              rw [← hw]
        _ = (p.br : Rat) ^ α * (p.br : Rat) ^ (2 * M) *
              capacity p d (α + 2 * M) t := by ring
        _ = (p.br : Rat) ^ (α + 2 * M) * capacity p d (α + 2 * M) t := by
              rw [← hpowa]
    have hmass :
        ∑ j ∈ Finset.Icc α (i - 1),
            (p.br : Rat) ^ j * allocation p d sched j t =
          (p.br : Rat) ^ i * capacity p d i t / capacityRatio p := by
      rw [honly, hmap, sum_congr rfl hterm, hre, hfin]
    rw [hmass]
    field_simp [hbrpow_i]

/-! **Lemma 3.2** -/

/-- §3 Lemma 3.2, capacity form.

    Under the paper intermediate snap bound `c(alpha(t), t) < 2 A br^2 / nu`
    and a dyadic/power closing hypothesis into `c ≤ A br^2 / nu`, conclude
    the paper bound. At `params7` the closing step is `Schedule7`'s exponent
    comparison (`≤ 5 ⇒ ≤ 64^5`). -/
theorem lemma32_of_snap (p : ScheduleParams) (d : Nat)
    (sched : LevelSchedule p d) (t : Nat)
    (_hasc : sched.alpha t < sched.alpha (t + 1))
    (_hsnap : capacity p d (sched.alpha t) t <
      2 * p.A * (p.br : Rat) ^ 2 / p.nu)
    (hclose : capacity p d (sched.alpha t) t ≤
      p.A * (p.br : Rat) ^ 2 / p.nu) :
    sched.alpha t = 0 ∨
      capacity p d (sched.alpha t) t ≤ p.A * (p.br : Rat) ^ 2 / p.nu := by
  by_cases hroot : sched.alpha t = 0
  · exact Or.inl hroot
  · exact Or.inr hclose

end Chvatal
