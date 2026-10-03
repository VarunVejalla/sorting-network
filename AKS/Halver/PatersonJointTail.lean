module

public import AKS.Halver.PatersonSimultaneous
public import Mathlib.Algebra.Order.Field.GeomSum
public import AKS.Bags.PatersonNumerics

/-! # A sharper tail bound for the small supported fraction -/

@[expose] public section

open Finset

namespace Paterson

set_option maxHeartbeats 10000

theorem indexed_tail_le_geometric {m p r : ℕ} {a e : ℚ}
    (hm : 0 < m) (ha : 0 ≤ a) (hp : (p : ℝ) ≤ (a : ℝ) * m)
    (hr : 0 < r) :
    indexedTailTerm m p e r ≤
      (a : ℝ) ^ r / Real.pi := by
  let q := maximalTrapTotal p e r
  let s := q - r
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hqp : q ≤ p := maximalTrapTotal_le_cap p e r
  have hsp : s ≤ p := (Nat.sub_le _ _).trans hqp
  have hspR : (s : ℝ) ≤ (a : ℝ) * m :=
    (by exact_mod_cast hsp : (s : ℝ) ≤ p).trans hp
  have hratio0 : (0 : ℝ) ≤ (s : ℝ) / m := by positivity
  have hratioA : (s : ℝ) / m ≤ a := (div_le_iff₀ hmR).mpr hspR
  have hpow : ((s : ℝ) / m) ^ r ≤ (a : ℝ) ^ r := by gcongr
  have hden1 : 0 < Real.pi * (r : ℝ) := mul_pos Real.pi_pos hrR
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold indexedTailTerm tailTerm
  apply (div_le_div_iff₀ hden1 hpi).mpr
  have hpow0 : 0 ≤ (a : ℝ) ^ r := pow_nonneg haR _
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : Real.pi ≤ Real.pi * (r : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hr1 Real.pi_pos.le
  calc
    ((s : ℝ) / m) ^ r * Real.pi ≤ (a : ℝ) ^ r * Real.pi :=
      mul_le_mul_of_nonneg_right hpow Real.pi_pos.le
    _ ≤ (a : ℝ) ^ r * (Real.pi * r) :=
      mul_le_mul_of_nonneg_left hden hpow0

theorem collapsed_tail_le_geometric {m : ℕ} {a e : ℚ}
    (hm : 0 < m) (ha : 0 ≤ a) (ha1 : a < 1) :
    (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) ≤
      ((a : ℝ) / (1 - (a : ℝ))) / Real.pi := by
  let p := supportedTrapCap m a
  let R := roundedTrapSize e p
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have ha1R : (a : ℝ) < 1 := by exact_mod_cast ha1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (p : ℝ) ≤ (a : ℝ) * m :=
    Nat.floor_le (mul_nonneg haR hmR.le)
  have hpoint : ∀ r ∈ Finset.Icc 1 R,
      indexedTailTerm m p e r ≤ (a : ℝ) ^ r / Real.pi := by
    intro r hr
    exact indexed_tail_le_geometric hm ha hp (Finset.mem_Icc.mp hr).1
  have hsum := Finset.sum_le_sum hpoint
  have hIcc : Finset.Icc 1 R = Finset.Ico 1 (R + 1) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hgeom : (∑ r ∈ Finset.Icc 1 R, (a : ℝ) ^ r) ≤
      (a : ℝ) / (1 - (a : ℝ)) := by
    rw [hIcc]
    simpa using (geom_sum_Ico_le_of_lt_one (m := 1) (n := R + 1) haR ha1R)
  calc
    (∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
      ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) ≤
        ∑ r ∈ Finset.Icc 1 R, indexedTailTerm m p e r :=
      admissible_tail_le_indexed_tail m a e
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (a : ℝ) ^ r / Real.pi := hsum
    _ = (∑ r ∈ Finset.Icc 1 R, (a : ℝ) ^ r) / Real.pi := by rw [Finset.sum_div]
    _ ≤ ((a : ℝ) / (1 - (a : ℝ))) / Real.pi := by
      exact div_le_div_of_nonneg_right hgeom Real.pi_pos.le

/-- The two first-level contracts fit together in the union bound. This is
the analytic estimate; constructing one network from it additionally needs
the finite union-of-traps criterion. -/
theorem paterson_first_level_joint_tail_lt_one {m : ℕ} (hm : 0 < m) :
    (2 : ℝ) *
      ((∑ rs ∈ admissibleCollapsedWitnessSizes m
          (2 * patersonMu) patersonDelta1,
          ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) +
       (∑ rs ∈ admissibleCollapsedWitnessSizes m
          patersonAlpha0 patersonDelta0,
          ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1))) < 1 := by
  have hsmall := collapsed_tail_le_geometric
    (m := m) (a := 2 * patersonMu) (e := patersonDelta1)
    hm (by norm_num [patersonMu]) (by norm_num [patersonMu])
  have hbig := (admissible_tail_le_indexed_tail m patersonAlpha0 patersonDelta0).trans
    (indexed_tail_sum_le_three_halves_over_pi hm
      patersonAlpha0_pos.le patersonAlpha0_lt_one.le
      (by norm_num [patersonDelta0]))
  have hsmall' : (∑ rs ∈ admissibleCollapsedWitnessSizes m
          (2 * patersonMu) patersonDelta1,
          ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) ≤
      (1 / 24 : ℝ) / Real.pi := by
    convert hsmall using 1
    norm_num [patersonMu]
  have hpi : (37 / 12 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    linarith
  calc
    (2 : ℝ) *
      ((∑ rs ∈ admissibleCollapsedWitnessSizes m
          (2 * patersonMu) patersonDelta1,
          ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1)) +
       (∑ rs ∈ admissibleCollapsedWitnessSizes m
          patersonAlpha0 patersonDelta0,
          ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1))) ≤
        2 * ((1 / 24 : ℝ) / Real.pi + (3 / 2 : ℝ) / Real.pi) := by
      gcongr
    _ = (37 / 12 : ℝ) / Real.pi := by ring
    _ < 1 := (div_lt_one Real.pi_pos).mpr hpi

theorem collapsed_pair_weight_le_tail {m c : ℕ} {a e : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (hehalf : e ≤ 1 / 2)
    (hc : patersonHalverDepthBound a e ≤ c) :
    (((∑ p ∈ (admissibleCollapsedWitnessSizes m a e).biUnion (pairsOfSizes m),
      ((p.2.card : ℚ) / m) ^ (p.1.card * c)) : ℚ) : ℝ) ≤
      ∑ rs ∈ admissibleCollapsedWitnessSizes m a e,
        ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
  rw [sum_trap_weights]
  push_cast
  apply Finset.sum_le_sum
  intro rs hrs
  exact admissible_collapsed_failure_term_le ha ha1 he hehalf hc hrs

theorem collapsed_trap_cover {m : ℕ} {a e : ℚ}
    (ha : a ≤ 1) (he : 0 < e) :
    ∀ k : ℕ, (k : ℝ) ≤ (a : ℝ) * m →
      ∀ X Y : Finset (Fin m), (e : ℝ) * k < X.card →
        X.card + Y.card ≤ k → X.card ≤ Y.card →
        ∃ X' Y',
          (X', Y') ∈ (admissibleCollapsedWitnessSizes m a e).biUnion (pairsOfSizes m) ∧
          X' ⊆ X ∧ Y ⊆ Y' := by
  intro k hk X Y hx hxy hXY
  obtain ⟨rs, hrs, hr, hs, hsm⟩ :=
    admissibleCollapsedWitnessSizes_cover ha he hk hx (by omega)
  obtain ⟨X', hX', hcX'⟩ := exists_subset_card_eq hr
  obtain ⟨Y', hY', _, hcY'⟩ := exists_subsuperset_card_eq
    (subset_univ Y) (show Y.card ≤ rs.2 from by omega)
    (show rs.2 ≤ (univ : Finset (Fin m)).card from by simpa using hsm)
  refine ⟨X', Y', mem_biUnion.mpr ⟨rs, hrs, ?_⟩, hX', hY'⟩
  simp [pairsOfSizes, hcX', hcY']

/-- One depth-263 matching network satisfies both first-level restricted
contracts. The same sequence is used for both; the proof uses the joint tail
bound rather than adding the two individual depth budgets. -/
theorem exists_paterson_first_level_halver {m : ℕ} (hm : 0 < m) :
    ∃ gs : List (Equiv.Perm (Fin m)), gs.length = 263 ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs)
        patersonDelta1 (2 * patersonMu) ∧
      IsEpsilonAlphaHalver (patersonMatchingNetwork gs)
        patersonDelta0 patersonAlpha0 ∧
      (patersonMatchingNetwork gs).depth ≤ 263 := by
  let sizes₀ := admissibleCollapsedWitnessSizes m (2 * patersonMu) patersonDelta1
  let sizes₁ := admissibleCollapsedWitnessSizes m patersonAlpha0 patersonDelta0
  let pairs₀ := sizes₀.biUnion (pairsOfSizes m)
  let pairs₁ := sizes₁.biUnion (pairsOfSizes m)
  have h0 : (((∑ p ∈ pairs₀,
      ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) ≤
      ∑ rs ∈ sizes₀,
        ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
    exact collapsed_pair_weight_le_tail
      (by norm_num [patersonMu]) (by norm_num [patersonMu])
      (by norm_num [patersonDelta1]) (by norm_num [patersonDelta1])
      depth_bound_level1
  have h1 : (((∑ p ∈ pairs₁,
      ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) ≤
      ∑ rs ∈ sizes₁,
        ((rs.2 : ℝ) / m) ^ rs.1 / (Real.pi * rs.1) := by
    exact collapsed_pair_weight_le_tail patersonAlpha0_pos
      patersonAlpha0_lt_one.le
      (by norm_num [patersonDelta0]) (by norm_num [patersonDelta0])
      (depth_bound_level0.trans (by norm_num))
  have hu := trap_union_weight_le_sum (m := m) (c := 263) pairs₀ pairs₁
  have huR : (((∑ p ∈ pairs₀ ∪ pairs₁,
      ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) ≤
      (((∑ p ∈ pairs₀,
        ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) +
      (((∑ p ∈ pairs₁,
        ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) := by
    exact_mod_cast hu
  have hjoint := paterson_first_level_joint_tail_lt_one hm
  have hreal : (2 : ℝ) *
      (((∑ p ∈ pairs₀ ∪ pairs₁,
        ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) : ℚ) : ℝ) < 1 := by
    nlinarith only [h0, h1, huR, hjoint]
  have hsmall : 2 * (∑ p ∈ pairs₀ ∪ pairs₁,
      ((p.2.card : ℚ) / m) ^ (p.1.card * 263)) < 1 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    convert hreal using 1 <;> push_cast <;> ring
  exact exists_simultaneous_halver_of_trap_covers hm (by norm_num)
    (by norm_num [patersonMu]) patersonAlpha0_lt_one.le
    pairs₀ pairs₁
    (collapsed_trap_cover (by norm_num [patersonMu])
      (by norm_num [patersonDelta1]))
    (collapsed_trap_cover patersonAlpha0_lt_one.le
      (by norm_num [patersonDelta0])) hsmall

theorem exists_paterson_first_level_all_arities (m : ℕ) :
    ∃ net : ComparatorNetwork (2 * m),
      IsEpsilonAlphaHalver net patersonDelta1 (2 * patersonMu) ∧
      IsEpsilonAlphaHalver net patersonDelta0 patersonAlpha0 ∧
      net.depth ≤ 263 := by
  by_cases hm : 0 < m
  · obtain ⟨gs, _, hsmall, hlarge, hdepth⟩ :=
      exists_paterson_first_level_halver hm
    exact ⟨patersonMatchingNetwork gs, hsmall, hlarge, hdepth⟩
  · have hm0 : m = 0 := by omega
    subst m
    refine ⟨patersonMatchingNetwork ([] : List (Equiv.Perm (Fin 0))),
      patersonZeroHalver _ _, patersonZeroHalver _ _, ?_⟩
    have hzero := patersonMatchingNetwork_depth_le
      ([] : List (Equiv.Perm (Fin 0)))
    exact hzero.trans (by norm_num)

end Paterson
