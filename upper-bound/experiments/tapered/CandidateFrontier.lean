import AKS.Chvatal.Schedule7
import Mathlib.Tactic

namespace Tapered945

def candidateTf (d : Nat) : Nat := 3 * d - 20

/-- The scale-matched terminal cutoff, three stages before the old endpoint.
The finite bootstrap can have coincident frontiers at earlier stages. -/
def candidateTerminalCutoff (d : Nat) : Nat := candidateTf d - 3

/-- Nat-arithmetic form of `max(0, floor((2*t-3*d+23)/3))`. -/
def candidateAlphaBase (d t : Nat) : Nat := max 0 ((2 * t + 23) / 3 - d)

def candidateOmegaBase (t : Nat) : Nat := (t + 4) / 3

def candidateAlpha (d t : Nat) : Nat := Chvatal.ceilParity (candidateAlphaBase d t) t

def candidateOmega (t : Nat) : Nat := Chvatal.ceilParity (candidateOmegaBase t) t

def candidateCapacityExponent (d l t : Nat) : Nat := 6 * d + 6 * l - 4 * t - 8

def candidateReferenceCapacity (d l t : Nat) : Rat :=
  (2 : Rat) ^ candidateCapacityExponent d l t

def candidateActive (d t : Nat) (b : Chvatal.KBag 64 d) : Prop :=
  candidateAlpha d t ≤ b.l ∧ b.l ≤ candidateOmega t

def candidateScheduledActive (d t : Nat) (b : Chvatal.KBag 64 d) : Prop :=
  candidateActive d t b ∧ b.l % 2 = t % 2

private theorem div3_bounds (n : Nat) :
    3 * (n / 3) ≤ n ∧ n ≤ 3 * (n / 3) + 2 := by
  constructor
  · simpa [Nat.mul_comm] using Nat.div_mul_le_self n 3
  · have hdecomp := Nat.mod_add_div n 3
    have hmod := Nat.mod_lt n (by omega : 0 < 3)
    omega

private theorem ceilParity_bounds (m p : Nat) :
    m ≤ Chvatal.ceilParity m p ∧ Chvatal.ceilParity m p ≤ m + 1 := by
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem ceilParity_mono {m n p : Nat} (h : m ≤ n) :
    Chvatal.ceilParity m p ≤ Chvatal.ceilParity n p := by
  unfold Chvatal.ceilParity
  split_ifs <;> omega

private theorem candidateAlphaBase_unit (d t : Nat) :
    candidateAlphaBase d t ≤ candidateAlphaBase d (t + 1) + 1 ∧
      candidateAlphaBase d (t + 1) ≤ candidateAlphaBase d t + 1 := by
  have hq := div3_bounds (2 * t + 23)
  have hq' := div3_bounds (2 * (t + 1) + 23)
  have hqstep : (2 * (t + 1) + 23) / 3 ≤ (2 * t + 23) / 3 + 1 := by omega
  have hqback : (2 * t + 23) / 3 ≤ (2 * (t + 1) + 23) / 3 + 1 := by omega
  unfold candidateAlphaBase
  by_cases h : (2 * t + 23) / 3 ≤ d <;>
    by_cases h' : (2 * (t + 1) + 23) / 3 ≤ d <;>
    simp [h, h'] <;> omega

private theorem candidateOmegaBase_unit (t : Nat) :
    candidateOmegaBase t ≤ candidateOmegaBase (t + 1) + 1 ∧
      candidateOmegaBase (t + 1) ≤ candidateOmegaBase t + 1 := by
  have hq := div3_bounds (t + 4)
  have hq' := div3_bounds (t + 5)
  unfold candidateOmegaBase
  omega

theorem candidate_frontiers_meet (d : Nat) (hd : 14 ≤ d) :
    candidateAlpha d (candidateTf d) = d - 6 ∧
      candidateOmega (candidateTf d) = d - 6 := by
  have htf : candidateTf d = 3 * d - 20 := rfl
  have hdivA : (2 * (3 * d - 20) + 23) / 3 = 2 * d - 6 := by omega
  have hdivO : (3 * d - 20 + 4) / 3 = d - 6 := by omega
  have hpar : (d - 6) % 2 = (3 * d - 20) % 2 := by omega
  have hbaseA : candidateAlphaBase d (3 * d - 20) = d - 6 := by
    unfold candidateAlphaBase
    rw [hdivA]
    omega
  have hbaseO : candidateOmegaBase (3 * d - 20) = d - 6 := by
    unfold candidateOmegaBase
    rw [hdivO]
  constructor
  · unfold candidateAlpha
    rw [htf]
    rw [hbaseA]
    simp [Chvatal.ceilParity, hpar]
  · unfold candidateOmega
    rw [htf]
    rw [hbaseO]
    simp [Chvatal.ceilParity, hpar]

/-- The real reference-capacity exponent at the meeting frontier is exactly 36. -/
theorem candidate_meeting_capacity_exponent (d : Nat) (hd : 14 ≤ d) :
    6 * d + 6 * candidateAlpha d (candidateTf d) -
      4 * candidateTf d - 8 = 36 := by
  obtain ⟨ha, -⟩ := candidate_frontiers_meet d hd
  rw [ha]
  unfold candidateTf
  omega

/-- At the terminal cutoff, both frontiers are at level `d-7` and the reference
capacity matches that level's native `64^7` reservoir. -/
theorem candidate_terminal_cutoff_scale (d : Nat) (hd : 14 ≤ d) :
    candidateAlpha d (candidateTerminalCutoff d) = d - 7 ∧
    candidateOmega (candidateTerminalCutoff d) = d - 7 ∧
    candidateReferenceCapacity d (d - 7) (candidateTerminalCutoff d) = 64 ^ 7 := by
  have htime : candidateTerminalCutoff d = 3 * d - 23 := by
    unfold candidateTerminalCutoff candidateTf
    omega
  have hdivA : (2 * (3 * d - 23) + 23) / 3 = 2 * d - 8 := by omega
  have hdivO : (3 * d - 23 + 4) / 3 = d - 7 := by omega
  have hparA : (d - 8) % 2 ≠ (3 * d - 23) % 2 := by omega
  have hparO : (d - 7) % 2 = (3 * d - 23) % 2 := by omega
  have hbaseA : candidateAlphaBase d (3 * d - 23) = d - 8 := by
    unfold candidateAlphaBase
    rw [hdivA]
    omega
  have hbaseO : candidateOmegaBase (3 * d - 23) = d - 7 := by
    unfold candidateOmegaBase
    rw [hdivO]
  have hAlpha : candidateAlpha d (3 * d - 23) = d - 7 := by
    unfold candidateAlpha
    rw [hbaseA]
    simp [Chvatal.ceilParity, hparA]
    omega
  have hOmega : candidateOmega (3 * d - 23) = d - 7 := by
    unfold candidateOmega
    rw [hbaseO]
    simp [Chvatal.ceilParity, hparO]
  have hexp : 6 * d + 6 * (d - 7) - 4 * (3 * d - 23) - 8 = 42 := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [htime]
    exact hAlpha
  · rw [htime]
    exact hOmega
  · rw [htime]
    unfold candidateReferenceCapacity
    unfold candidateCapacityExponent
    rw [hexp]
    norm_num

/-- Capacity scales for the two bottom expansions feeding the terminal
meeting. The lower parent has native size `64^8`; its first children have the
meeting reservoir size `64^7`. The top parent at the meeting step has scale
`2^40`, so the second bottom cohort has capacity `1024` times that scale. -/
theorem candidate_terminal_cohort_scales (d : Nat) (hd : 14 ≤ d) :
    candidateReferenceCapacity d (d - 8) (candidateTerminalCutoff d - 3) = 64 ^ 8 ∧
    candidateReferenceCapacity d (d - 7) (candidateTerminalCutoff d - 2) =
      4 * 64 ^ 8 ∧
    candidateReferenceCapacity d (d - 8) (candidateTerminalCutoff d - 1) =
      2 ^ 40 ∧
    candidateReferenceCapacity d (d - 6) (candidateTerminalCutoff d - 1) =
      4096 * 2 ^ 40 := by
  have ht0 : candidateTerminalCutoff d - 3 = 3 * d - 26 := by
    unfold candidateTerminalCutoff candidateTf
    omega
  have ht1 : candidateTerminalCutoff d - 2 = 3 * d - 25 := by
    unfold candidateTerminalCutoff candidateTf
    omega
  have ht2 : candidateTerminalCutoff d - 1 = 3 * d - 24 := by
    unfold candidateTerminalCutoff candidateTf
    omega
  have he0 : candidateCapacityExponent d (d - 8) (3 * d - 26) = 48 := by
    unfold candidateCapacityExponent
    omega
  have he1 : candidateCapacityExponent d (d - 7) (3 * d - 25) = 50 := by
    unfold candidateCapacityExponent
    omega
  have he2 : candidateCapacityExponent d (d - 8) (3 * d - 24) = 40 := by
    unfold candidateCapacityExponent
    omega
  have he3 : candidateCapacityExponent d (d - 6) (3 * d - 24) = 52 := by
    unfold candidateCapacityExponent
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ht0]
    unfold candidateReferenceCapacity
    rw [he0]
    norm_num
  · rw [ht1]
    unfold candidateReferenceCapacity
    rw [he1]
    norm_num
  · rw [ht2]
    unfold candidateReferenceCapacity
    rw [he2]
  · rw [ht2]
    unfold candidateReferenceCapacity
    rw [he3]
    norm_num


theorem candidate_frontiers_order (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) :
    candidateAlpha d t ≤ candidateOmega t := by
  have hgap : candidateAlphaBase d t ≤ candidateOmegaBase t := by
    have htlin : t + 20 ≤ 3 * d := by
      unfold candidateTf at ht
      omega
    have hq : (2 * t + 23) / 3 ≤ (t + 4) / 3 + d := by
      calc
        (2 * t + 23) / 3 ≤ (t + 4 + d * 3) / 3 := by
          apply Nat.div_le_div_right
          omega
        _ = (t + 4) / 3 + d := by
          rw [Nat.mul_comm d 3]
          rw [Nat.add_mul_div_left (t + 4) d (by omega : 0 < 3)]
    unfold candidateAlphaBase candidateOmegaBase
    omega
  have ha := ceilParity_bounds (candidateAlphaBase d t) t
  have ho := ceilParity_bounds (candidateOmegaBase t) t
  unfold candidateAlpha candidateOmega
  exact ceilParity_mono hgap

/-- The two special initialization stages meet the ordinary band at levels
zero and two. -/
theorem candidate_frontiers_stage_two (d : Nat) (hd : 14 ≤ d) :
    candidateAlpha d 2 = 0 ∧ candidateOmega 2 = 2 := by
  constructor
  · unfold candidateAlpha candidateAlphaBase Chvatal.ceilParity
    have hd9 : 9 ≤ d := by omega
    rw [show (2 * 2 + 23) / 3 = 9 by norm_num]
    rw [Nat.sub_eq_zero_of_le hd9]
    norm_num
  · unfold candidateOmega candidateOmegaBase Chvatal.ceilParity
    norm_num

theorem candidate_alpha_exponent_bound (d : Nat) (_hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) :
    34 ≤ 6 * d + 6 * candidateAlpha d t - 4 * t - 8 := by
  have hlow : 3 * ((2 * t + 23) / 3) ≥ 2 * t + 21 := by
    have hq := div3_bounds (2 * t + 23)
    omega
  have ha := (ceilParity_bounds (candidateAlphaBase d t) t).1
  have ht' : t ≤ 3 * d - 20 := by simpa [candidateTf] using ht
  have habase : 3 * candidateAlphaBase d t ≥ 2 * t + 21 - 3 * d := by
    have hq := div3_bounds (2 * t + 23)
    unfold candidateAlphaBase
    omega
  unfold candidateAlpha
  omega

theorem candidate_omega_exponent_bound (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) :
    36 ≤ 6 * d + 6 * candidateOmega t - 4 * t - 8 := by
  have hlow : 3 * ((t + 4) / 3) ≥ t + 2 := by
    have hq := div3_bounds (t + 4)
    omega
  have ho := (ceilParity_bounds (candidateOmegaBase t) t).1
  have ht' : t ≤ 3 * d - 20 := by simpa [candidateTf] using ht
  unfold candidateOmegaBase at ho
  unfold candidateOmega candidateOmegaBase
  omega

theorem candidate_alpha_unit_motion (d : Nat) (_hd : 14 ≤ d)
    (t : Nat) (_ht : t < candidateTf d) :
    candidateAlpha d t ≤ candidateAlpha d (t + 1) + 1 ∧
      candidateAlpha d (t + 1) ≤ candidateAlpha d t + 1 := by
  have hb := candidateAlphaBase_unit d t
  unfold candidateAlpha
  exact (Chvatal.ceilParity_unit_step _ _ t hb.2 hb.1).symm

theorem candidate_omega_unit_motion (t : Nat) :
    candidateOmega t ≤ candidateOmega (t + 1) + 1 ∧
      candidateOmega (t + 1) ≤ candidateOmega t + 1 := by
  have hb := candidateOmegaBase_unit t
  unfold candidateOmega
  exact (Chvatal.ceilParity_unit_step _ _ t hb.2 hb.1).symm

theorem candidate_alpha_parity (d t : Nat) : candidateAlpha d t % 2 = t % 2 := by
  unfold candidateAlpha Chvatal.ceilParity
  split_ifs <;> omega

theorem candidate_omega_parity (t : Nat) : candidateOmega t % 2 = t % 2 := by
  unfold candidateOmega Chvatal.ceilParity
  split_ifs <;> omega

/-- Since the parity target flips at every stage, each parity-rounded frontier
moves exactly one level. The disjunction keeps the direction explicit: the
lower frontier can move down at the initial boundary. -/
theorem candidate_alpha_frontier_moves_one (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) :
    candidateAlpha d (t + 1) = candidateAlpha d t + 1 ∨
      candidateAlpha d t = candidateAlpha d (t + 1) + 1 := by
  have hstep := candidate_alpha_unit_motion d hd t ht
  have hpar0 := candidate_alpha_parity d t
  have hpar1 := candidate_alpha_parity d (t + 1)
  omega

theorem candidate_omega_frontier_moves_one (t : Nat) :
    candidateOmega (t + 1) = candidateOmega t + 1 ∨
      candidateOmega t = candidateOmega (t + 1) + 1 := by
  have hstep := candidate_omega_unit_motion t
  have hpar0 := candidate_omega_parity t
  have hpar1 := candidate_omega_parity (t + 1)
  omega

theorem candidate_omega_le_depth (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) : candidateOmega t ≤ d := by
  unfold candidateOmega candidateOmegaBase Chvatal.ceilParity candidateTf at *
  split_ifs <;> omega

theorem candidate_omega_le_depth_minus_five (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) : candidateOmega t ≤ d - 5 := by
  unfold candidateOmega candidateOmegaBase Chvatal.ceilParity candidateTf at *
  split_ifs <;> omega

private theorem candidate_active_parent_depth (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (b : Chvatal.KBag 64 d)
    (hbottom : b.l + 2 ≤ candidateOmega t) : b.l < d := by
  have hω := candidate_omega_le_depth d hd t (by omega)
  omega

private theorem candidate_active_child_depth (d : Nat) (b : Chvatal.KBag 64 d)
    (j : Fin 64) (hparent : b.l < d) (hchild : b.l + 1 < d) :
    (b.child j.val j.isLt hparent).l < d := by
  change b.l + 1 < d
  exact hchild

/-- Away from the terminal two layers, an active bag's child is active at the
next stage and all of its grandchildren remain active at the current stage.
These are exactly the addresses needed by the integer occupancy recurrence. -/
theorem candidate_interior_active_successors (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (b : Chvatal.KBag 64 d)
    (hb : candidateScheduledActive d t b)
    (hbottom : b.l + 2 ≤ candidateOmega t) :
    (∀ j : Fin 64, candidateScheduledActive d (t + 1)
      (b.child j.val j.isLt (candidate_active_parent_depth d hd t ht b hbottom))) ∧
    (∀ j l : Fin 64, candidateScheduledActive d t
      ((b.child j.val j.isLt (candidate_active_parent_depth d hd t ht b hbottom)).child
        l.val l.isLt (candidate_active_child_depth d b j
          (candidate_active_parent_depth d hd t ht b hbottom) (by
            have hω := candidate_omega_le_depth d hd t (by omega)
            omega)))) := by
  rcases hb with ⟨⟨hα, hω⟩, hpar⟩
  have ht0 : t ≤ candidateTf d := by omega
  have haStep := candidate_alpha_unit_motion d hd t ht
  have hoStep := candidate_omega_unit_motion t
  have hωd := candidate_omega_le_depth d hd t ht0
  have hωmove : candidateOmega t ≤ candidateOmega (t + 1) + 1 := hoStep.1
  constructor
  · intro j
    have hlev : b.l < d := candidate_active_parent_depth d hd t ht b hbottom
    have hclev : b.l + 1 < d := by
      have hω := candidate_omega_le_depth d hd t ht0
      omega
    change (candidateAlpha d (t + 1) ≤ b.l + 1 ∧
      b.l + 1 ≤ candidateOmega (t + 1)) ∧ (b.l + 1) % 2 = (t + 1) % 2
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    calc
      (b.l + 1) % 2 = (b.l % 2 + 1 % 2) % 2 := by rw [Nat.add_mod]
      _ = (t % 2 + 1 % 2) % 2 := by rw [hpar]
      _ = (t + 1) % 2 := by simp [Nat.add_mod]
  · intro j l
    have hlev : b.l < d := candidate_active_parent_depth d hd t ht b hbottom
    have hclev : b.l + 1 < d := by omega
    change (candidateAlpha d t ≤ b.l + 2 ∧
      b.l + 2 ≤ candidateOmega t) ∧ (b.l + 2) % 2 = t % 2
    refine ⟨⟨by omega, hbottom⟩, ?_⟩
    calc
      (b.l + 2) % 2 = (b.l % 2 + 2 % 2) % 2 := by rw [Nat.add_mod]
      _ = (t % 2 + 2 % 2) % 2 := by rw [hpar]
      _ = t % 2 := by norm_num

/-- Every active ordinary bag has enough reference capacity for the integerizer. -/
theorem candidate_active_capacity_lower (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t ≤ candidateTf d) (l : Nat) (hl : candidateAlpha d t ≤ l) :
    2 ^ 34 ≤ candidateReferenceCapacity d l t := by
  have hα := candidate_alpha_exponent_bound d hd t ht
  have hmono : candidateCapacityExponent d (candidateAlpha d t) t ≤
      candidateCapacityExponent d l t := by
    unfold candidateCapacityExponent
    omega
  unfold candidateReferenceCapacity
  exact pow_le_pow_right₀ (by norm_num : (1 : Rat) ≤ 2) (le_trans hα hmono)

/-- Two tree levels down at the same stage multiply reference capacity by `64²`. -/
theorem candidate_reference_capacity_grandchild (d l t : Nat)
    (hbase : 4 * t + 8 ≤ 6 * d + 6 * l) :
    candidateReferenceCapacity d (l + 2) t =
      64 ^ 2 * candidateReferenceCapacity d l t := by
  have hexp : candidateCapacityExponent d (l + 2) t =
      candidateCapacityExponent d l t + 12 := by
    unfold candidateCapacityExponent
    omega
  unfold candidateReferenceCapacity
  rw [hexp, pow_add]
  norm_num
  ring

/-- A parent-to-child tree step combined with one time step changes capacity by `4`. -/
theorem candidate_reference_capacity_next_stage (d : Nat) (hd : 14 ≤ d)
    (t : Nat) (ht : t < candidateTf d) (l : Nat)
    (hl : candidateAlpha d t ≤ l) :
    candidateReferenceCapacity d (l + 1) (t + 1) =
      4 * candidateReferenceCapacity d l t := by
  have ht' : t ≤ candidateTf d := by omega
  have hα := candidate_alpha_exponent_bound d hd t ht'
  have hexp : candidateCapacityExponent d (l + 1) (t + 1) =
      candidateCapacityExponent d l t + 2 := by
    unfold candidateCapacityExponent
    omega
  unfold candidateReferenceCapacity
  rw [hexp, pow_add]
  norm_num
  ring

end Tapered945
