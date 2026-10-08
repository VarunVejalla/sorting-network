module
/-
  # Chvátal Theorem 5.1 — Module A (existence plumbing)

  Discharges Lemma 6.1/6.2 fail unions from `DecodeMatrixClassObligation.levelExpOn`
  (pipeline mass `totalColumnOnes c ≤ n·i`) and `Lemma62FringeCellBound`, and yields
  combinatorial Property B/F via `ModuleACombinatorialObligation`. Matrix
  `HasMatrixPropertyB`/`F` on the sort–scramble–sort network uses
  `HasCombinatorialPropertyBOnPipeline` (sufficient for decode matrices).

  **Module A policy A1:** global `AvgRowOnesLeOne` / `TotalColumnOnesLeN` over all
  monotone `c` is **false** when `m > 1` and is **not** required for the pipeline
  track. Kernel-checked Chernoff on the decode class is `DecodeMatrixClassObligation.standard`.
  Unrestricted `HasCombinatorialPropertyB` (∀ monotone `c`, paper Thm 5.1 statement)
  still needs the unrestricted Chernoff residual or a paper-side matrix restriction.
-/

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Lemma62Chernoff
public import AKS.Chvatal.Lemma63
public import AKS.Chvatal.ModuleANumerics
public import AKS.Chvatal.MatrixBridge
public import AKS.Chvatal.RowScramble
public import AKS.Chvatal.SortedColumnDecode
public import Mathlib.Tactic.NormNum

set_option maxHeartbeats 2000000

@[expose] public section

namespace Chvatal

theorem scrambleGeometry_hm_pos {g : ScrambleGeometry} : 0 < g.m :=
  Nat.lt_of_lt_of_le (by norm_num : (0 : Nat) < 100) g.hm

theorem scrambleGeometry_hn_pos {g : ScrambleGeometry} : 0 < g.n :=
  Nat.lt_of_lt_of_le (by norm_num : (0 : Nat) < 16) g.hn

theorem scrambleGeometry_hm1 {g : ScrambleGeometry} : 1 ≤ g.m :=
  Nat.le_trans (by decide : (1 : Nat) ≤ 100) g.hm

theorem scrambleGeometry_hn1 {g : ScrambleGeometry} : 1 ≤ g.n :=
  Nat.le_trans (by decide : (1 : Nat) ≤ 16) g.hn

theorem scrambleGeometry_hf2 {g : ScrambleGeometry} : 2 ≤ g.f :=
  le_trans (by norm_num : (2 : Nat) ≤ 10) g.hf

theorem scrambleGeometry_hfpos {g : ScrambleGeometry} : 0 < g.f :=
  Nat.lt_of_lt_of_le (by norm_num : (0 : Nat) < 10) g.hf

theorem scrambleGeometry_hmF {g : ScrambleGeometry} : 1 ≤ fringeRowCount g.m g.f g.hfeven := by
  rw [fringeRowCount_eq g.m g.f g.hfeven]
  have h2f : 2 * g.f ≤ g.m := by
    rw [g.hshape]
    omega
  have hfhalf : g.f / 2 < g.m := by
    have hf10 : 10 ≤ g.f := g.hf
    omega
  exact Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hfhalf)

/-! **Lemma 6.1 union over `(c, S)` at level `i = 1`** -/

noncomputable def paperThreshold (m n : Nat) (epsB : ℝ) (i s : Nat) : ℝ :=
  ((i : ℝ) / (m : ℝ) + (epsB / 2) * ((n : ℝ) / s)) * (m : ℝ) * s

theorem paperThreshold_eq_is_mul {m n : Nat} (hm : 0 < m) (epsB : ℝ) (i s : Nat) (hs : 0 < s) :
    paperThreshold m n epsB i s = (i : ℝ) * s + (epsB / 2) * (m * n) := by
  unfold paperThreshold
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp [hm0, hs0]

theorem paperThreshold_mono {m n : Nat} (hm : 0 < m) (epsB : ℝ) (s : Nat) (hs : 0 < s)
    {i j : Nat} (hij : i ≤ j) :
    paperThreshold m n epsB i s ≤ paperThreshold m n epsB j s := by
  rw [paperThreshold_eq_is_mul hm epsB i s hs, paperThreshold_eq_is_mul hm epsB j s hs]
  gcongr

noncomputable def violatorsAtLevel {m n : Nat} (epsB : ℝ) (i : Nat)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) : Finset (Scramble m n) :=
  if hs : 0 < S.card then
    Finset.univ.filter fun σ =>
      paperThreshold m n epsB i S.card ≤ (onesInColumns c σ S : ℝ)
  else
    ∅

theorem mem_violatorsAtLevel {m n : Nat} (epsB : ℝ) (i : Nat)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n)
    (hs : 0 < S.card) :
    σ ∈ violatorsAtLevel epsB i c S ↔
      paperThreshold m n epsB i S.card ≤ (onesInColumns c σ S : ℝ) := by
  simp [violatorsAtLevel, hs]

theorem mem_violatorsAtLevel_mono {m n : Nat} (hm : 0 < m) (epsB : ℝ) (c : MonotoneColumnSums m n)
    (S : Finset (Fin n)) (σ : Scramble m n) (hs : 0 < S.card) {i j : Nat} (hij : i ≤ j)
    (h : σ ∈ violatorsAtLevel epsB j c S) :
    σ ∈ violatorsAtLevel epsB i c S := by
  rw [mem_violatorsAtLevel epsB j c S σ hs] at h
  rw [mem_violatorsAtLevel epsB i c S σ hs]
  exact le_trans (paperThreshold_mono hm epsB S.card hs hij) h

private theorem onesInColumns_eq_zero_of_totalColumnOnes_eq_zero {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n))
    (h0 : totalColumnOnes c = 0) : onesInColumns c σ S = 0 := by
  have hcol : ∀ j : Fin n, (c j).val = 0 := by
    intro j
    rw [totalColumnOnes] at h0
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => Nat.zero_le (c j').val)).1 h0 j
      (Finset.mem_univ j)
  unfold onesInColumns
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [Finset.card_eq_zero]
  ext j
  simp only [Finset.mem_inter, Finset.notMem_empty, iff_false]
  intro hj
  have hjscr : j ∈ scrambledRowOnes c σ r := hj.1
  simp only [scrambledRowOnes, Finset.mem_image] at hjscr
  obtain ⟨j', hj', _eq⟩ := hjscr
  have hmono : j' ∈ monotoneRowOnes c r := hj'
  rw [mem_monotoneRowOnes_iff] at hmono
  have hc0 := hcol j'
  omega

private theorem totalColumnOnes_eq_zero_of_matrixOnesLevel_eq_zero {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (h : matrixOnesLevel hn c = 0) : totalColumnOnes c = 0 := by
  unfold matrixOnesLevel at h
  have hlt : totalColumnOnes c + n - 1 < n := by
    rcases Nat.div_eq_zero_iff.mp h with h' | h'
    · exfalso; exact hn.ne' h'
    · exact h'
  omega

theorem violatorsAtLevel_card_le_on {m n : Nat} (hm : 0 < m) (hn : 0 < n) (epsB : ℝ)
    (hepsB : 0 < epsB) (i : Nat) (c : MonotoneColumnSums m n)
    (hc : TotalColumnOnesLeLevel m n i c) (S : Finset (Fin n)) (hs : 0 < S.card) :
    (violatorsAtLevel epsB i c S).card ≤
      Real.exp (-(2 * ((epsB / 2) * ((n : ℝ) / S.card)) ^ 2 * m * S.card)) *
        (Fintype.card (Scramble m n) : ℝ) := by
  classical
  set t := (epsB / 2) * ((n : ℝ) / S.card)
  have ht : 0 < t := by
    have hs0 : (0 : ℝ) < S.card := by exact_mod_cast hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have heps2 : 0 < epsB / 2 := by linarith [hepsB]
    exact mul_pos heps2 (div_pos hnpos hs0)
  have hset :
      violatorsAtLevel epsB i c S =
        (Finset.univ.filter fun σ =>
          paperThreshold m n epsB i S.card ≤ (onesInColumns c σ S : ℝ)) := by
    ext σ
    simp [violatorsAtLevel, hs, paperThreshold, mul_assoc, mul_comm, mul_left_comm]
  have hthresh :
      ∀ σ ∈ violatorsAtLevel epsB i c S,
        ((i : ℝ) / (m : ℝ) + t) * (m : ℝ) * S.card ≤ (onesInColumns c σ S : ℝ) := by
    intro σ hσ
    rw [hset] at hσ
    simpa [paperThreshold, t, mul_assoc, mul_comm, mul_left_comm] using
      (Finset.mem_filter.mp hσ).2
  exact (lemma63ExpBoundAtLevelOn_totalColumnOnesLeLevel hm hn).bound c hc S t ht
    (violatorsAtLevel epsB i c S) hthresh

theorem violatorsAtLevel_card_le {m n : Nat} (hn : 0 < n) (epsB : ℝ) (hepsB : 0 < epsB) (i : Nat)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (hs : 0 < S.card)
    (L : Lemma63ExpBoundAtLevel m n i) :
    (violatorsAtLevel epsB i c S).card ≤
      Real.exp (-(2 * ((epsB / 2) * ((n : ℝ) / S.card)) ^ 2 * m * S.card)) *
        (Fintype.card (Scramble m n) : ℝ) := by
  have ht : 0 < (epsB / 2) * ((n : ℝ) / S.card) := by
    have hs0 : (0 : ℝ) < S.card := by exact_mod_cast hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have heps2 : 0 < epsB / 2 := by linarith [hepsB]
    exact mul_pos heps2 (div_pos hnpos hs0)
  have hset :
      violatorsAtLevel epsB i c S =
        (Finset.univ.filter fun σ =>
          paperThreshold m n epsB i S.card ≤ (onesInColumns c σ S : ℝ)) := by
    ext σ
    simp [violatorsAtLevel, hs, paperThreshold, mul_assoc, mul_comm, mul_left_comm]
  rw [hset]
  exact L.bound c S ((epsB / 2) * ((n : ℝ) / S.card)) ht (Finset.univ.filter _)
    (fun σ hσ => (Finset.mem_filter.mp hσ).2)

theorem bad_scramble_mem_violators_level {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (epsB : ℝ) (hepsB : 0 < epsB) (i : Nat) (σ : Scramble m n) (c : MonotoneColumnSums m n)
    (hge : (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ))
    (hs : 0 < (excessColumnSet c σ i).card) :
    σ ∈ violatorsAtLevel epsB i c (excessColumnSet c σ i) := by
  set S := excessColumnSet c σ i
  have ht : 0 < (epsB / 2) * ((n : ℝ) / S.card) := by
    have hs0 : (0 : ℝ) < S.card := by exact_mod_cast hs
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have heps2 : 0 < epsB / 2 := by linarith [hepsB]
    exact mul_pos heps2 (div_pos hnpos hs0)
  rw [mem_violatorsAtLevel epsB i c S σ hs]
  have hones := onesInColumns_ge_paper_thresh hm hn c σ epsB i hge hs ht
  simpa [paperThreshold] using hones

theorem bad_scramble_mem_violators_level_one {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (epsB : ℝ) (hepsB : 0 < epsB) (σ : Scramble m n) (c : MonotoneColumnSums m n)
    (hge : (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ 1 : ℝ))
    (hs : 0 < (excessColumnSet c σ 1).card) :
    σ ∈ violatorsAtLevel epsB 1 c (excessColumnSet c σ 1) :=
  bad_scramble_mem_violators_level hm hn epsB hepsB 1 σ c hge hs

/-- Sound because `O.levelExp1.bound` quantifies over every monotone `c` (not merely
    avg-row-ones `≤ 1` matrices). Obtaining such a `levelExp1` without `AvgRowOnesLeOne`
    is the unrestricted Chernoff residual. -/
theorem lemma61FailBound_of_levelExp1 {m n : Nat} (epsB : ℝ)
    (O : Lemma61FailBoundObligation m n epsB) :
    Lemma61FailBound m n epsB := by
  classical
  refine { bound := ?_ }
  intro bad hbad
  have hepsB := O.epsB_pos
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have _hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hcell :
      ∀ (σ : Scramble m n), σ ∈ bad →
        ∃ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
          0 < S.card ∧ σ ∈ violatorsAtLevel epsB 1 c S := by
    intro σ hσ
    have hnot := hbad σ hσ
    obtain ⟨c, hge⟩ := combinatorialPropertyB_failWitness_level_one σ epsB hnot
    set S := excessColumnSet c σ 1
    have hs : 0 < S.card := by
      by_contra hs0
      push_neg at hs0
      have hcard0 : S.card = 0 := Nat.eq_zero_of_le_zero hs0
      have hempty : S = ∅ := Finset.card_eq_zero.mp hcard0
      have hzero : onesAboveBottom c σ 1 = 0 := by
        unfold onesAboveBottom
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj : scrambledColSum c σ j < 1 := by
          by_contra hnot
          push_neg at hnot
          have hmem : j ∈ S := by simpa [S, mem_excessColumnSet] using hnot
          exact Finset.notMem_empty j (by simpa [hempty] using hmem)
        exact Nat.sub_eq_zero_of_le (le_of_lt hj)
      have hzeroR : (onesAboveBottom c σ 1 : ℝ) = 0 := by exact_mod_cast hzero
      have hge0 : 0 < (epsB / 2) * (m * n) := by
        have hmn : 0 < (m * n : ℝ) := by exact_mod_cast (Nat.mul_pos O.hm O.hn)
        nlinarith [hepsB, hmn]
      linarith [hge, hzeroR, hge0]
    exact ⟨c, S, hs,
      bad_scramble_mem_violators_level_one O.hm O.hn epsB hepsB σ c hge hs⟩
  -- Cover `bad` by cells indexed by `(c, S)`.
  have hsubset :
      bad ⊆
        Finset.biUnion (Finset.univ : Finset (MonotoneColumnSums m n)) fun c =>
          Finset.biUnion (Finset.univ : Finset (Finset (Fin n))) fun S =>
            violatorsAtLevel epsB 1 c S := by
    intro σ hσ
    obtain ⟨c, S, hs, hmem⟩ := hcell σ hσ
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ _, hmem⟩
  set cover :=
    Finset.biUnion (Finset.univ : Finset (MonotoneColumnSums m n)) fun c =>
      Finset.biUnion (Finset.univ : Finset (Finset (Fin n))) fun S =>
        violatorsAtLevel epsB 1 c S
  have hcardNat :
      bad.card ≤
        ∑ c : MonotoneColumnSums m n,
          ∑ S : Finset (Fin n), (violatorsAtLevel epsB 1 c S).card := by
    have h₁ : bad.card ≤ cover.card := Finset.card_le_card hsubset
    have h₂ :
        cover.card ≤
          ∑ c : MonotoneColumnSums m n,
            ∑ S : Finset (Fin n), (violatorsAtLevel epsB 1 c S).card := by
      calc cover.card
          ≤ ∑ c, (Finset.univ.biUnion fun S => violatorsAtLevel epsB 1 c S).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ c, ∑ S, (violatorsAtLevel epsB 1 c S).card := by
          gcongr
          exact Finset.card_biUnion_le
    exact h₁.trans h₂
  have huniform :
      ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
        ((violatorsAtLevel epsB 1 c S).card : ℝ) ≤
          (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
    intro c S
    by_cases hs : 0 < S.card
    · have hle := violatorsAtLevel_card_le O.hn epsB hepsB 1 c S hs O.levelExp1
      have hs1 : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hs.ne'
      have hsn : S.card ≤ n := by
        simpa [Fintype.card_fin] using (S.card_le_univ : S.card ≤ Finset.univ.card)
      have hrate :=
        lemma61_exp_bound m n S.card epsB O.hm1 hs1 hsn O.hn1 O.heps
      exact hle.trans (mul_le_mul_of_nonneg_right hrate (le_of_lt _hNpos))
    · have hempty : violatorsAtLevel epsB 1 c S = ∅ := by simp [violatorsAtLevel, hs]
      rw [show ((violatorsAtLevel epsB 1 c S).card : ℝ) = 0 from by simp [hempty]]
      have hrhs : 0 ≤ (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
        have hN : 0 ≤ N := le_of_lt _hNpos
        positivity
      exact hrhs
  have hsumReal :
      ((∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          (violatorsAtLevel epsB 1 c S).card) : ℝ) ≤
        lemma61_failFactor m n * N := by
    have hcountC : Fintype.card (MonotoneColumnSums m n) = (m + 1) ^ n := by
      simp [monotoneColumnSums_card]
    have hcountS : Fintype.card (Finset (Fin n)) = 2 ^ n := finset_card n
    have hstep :
        ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          ((violatorsAtLevel epsB 1 c S).card : ℝ) ≤
          ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
      refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun S _ => ?_
      exact huniform c S
    calc ((∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (violatorsAtLevel epsB 1 c S).card) : ℝ)
        = ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            ((violatorsAtLevel epsB 1 c S).card : ℝ) := by simp
      _ ≤ ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (Real.exp 1 * m) ^ (-(n : ℝ)) * N := hstep
      _ = ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
          simp [Finset.sum_const, Finset.card_univ, hcountC, hcountS, mul_assoc, mul_left_comm,
            mul_comm]
      _ = lemma61_failFactor m n * N := by
          have h :
              ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) =
                lemma61_failFactor m n := by
            have hpow : (2 : ℝ) ^ n * (Real.exp 1 * m) ^ (-(n : ℝ)) =
                ((2 : ℝ) / (Real.exp 1 * m)) ^ n := by
              have hx : 0 < Real.exp 1 * m :=
                mul_pos (Real.exp_pos _) (by exact_mod_cast O.hm)
              rw [div_pow, div_eq_mul_inv]
              congr 1
              rw [Real.rpow_neg (le_of_lt hx), Real.rpow_natCast]
            calc ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ))
                = ((m + 1 : ℝ) ^ n) * ((2 : ℝ) / (Real.exp 1 * m)) ^ n := by
                    rw [← hpow, mul_assoc]
              _ = lemma61_failFactor m n := by
                    rw [← lemma61_union_eq_failFactor m n O.hm]
          rw [h]
  have hcastEq :
      ↑(∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          (violatorsAtLevel epsB 1 c S).card) =
        ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          ((violatorsAtLevel epsB 1 c S).card : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => (Nat.cast_sum (s := Finset.univ) _)
  exact le_trans (by rw [← hcastEq]; exact Nat.cast_le.mpr hcardNat) hsumReal

/-- Pipeline-class Lemma 6.1 fail union: each monotone matrix counted once at `matrixOnesLevel`. -/
theorem lemma61FailBound_onPipeline_of_decodeClass {m n : Nat} (epsB : ℝ)
    (O : DecodeMatrixClassObligation m n epsB) :
    Lemma61FailBoundOnPipeline m n epsB := by
  classical
  refine { bound := ?_ }
  intro bad hbad
  have hepsB := O.epsB_pos
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hcell :
      ∀ (σ : Scramble m n), σ ∈ bad →
        ∃ (i : Nat) (hi1 : 1 ≤ i) (him : i ≤ m) (c : MonotoneColumnSums m n),
          TotalColumnOnesLeLevel m n i c ∧
            ∃ (S : Finset (Fin n)), 0 < S.card ∧
              σ ∈ violatorsAtLevel epsB i c S := by
    intro σ hσ
    have hnot := hbad σ hσ
    obtain ⟨c, i, hclass, hi1, him, hge⟩ :=
      combinatorialPropertyB_pipeline_failWitness σ epsB hnot
    set S := excessColumnSet c σ i
    have hs : 0 < S.card := by
      by_contra hs0
      push_neg at hs0
      have hcard0 : S.card = 0 := Nat.eq_zero_of_le_zero hs0
      have hempty : S = ∅ := Finset.card_eq_zero.mp hcard0
      have hzero : onesAboveBottom c σ i = 0 := by
        unfold onesAboveBottom
        refine Finset.sum_eq_zero fun j _ => ?_
        have hj : scrambledColSum c σ j < i := by
          by_contra hnot
          push_neg at hnot
          have hmem : j ∈ S := by simpa [S, mem_excessColumnSet] using hnot
          exact Finset.notMem_empty j (by simpa [hempty] using hmem)
        exact Nat.sub_eq_zero_of_le (le_of_lt hj)
      have hzeroR : (onesAboveBottom c σ i : ℝ) = 0 := by exact_mod_cast hzero
      have hge0 : 0 < (epsB / 2) * (m * n) := by
        have hmn : 0 < (m * n : ℝ) := by exact_mod_cast (Nat.mul_pos O.hm O.hn)
        nlinarith [hepsB, hmn]
      linarith [hge, hzeroR, hge0]
    exact ⟨i, hi1, him, c, hclass, excessColumnSet c σ i, hs,
      bad_scramble_mem_violators_level O.hm O.hn epsB hepsB i σ c hge hs⟩
  set cover :=
    Finset.biUnion (Finset.univ : Finset (MonotoneColumnSums m n)) fun c =>
      Finset.biUnion (Finset.univ : Finset (Finset (Fin n))) fun S =>
        violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S
  have hsubset : bad ⊆ cover := by
    intro σ hσ
    obtain ⟨i, hi1, _him, c, hclass, S, hs, hmem⟩ := hcell σ hσ
    set k := matrixOnesLevel O.hn c
    have hki : k ≤ i := matrixOnesLevel_le_of_totalColumnOnesLeLevel O.hn c hclass
    have hmemK := mem_violatorsAtLevel_mono O.hm epsB c S σ hs hki hmem
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ _, hmemK⟩
  have hcardNat :
      bad.card ≤
        ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          (violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card := by
    have h₁ : bad.card ≤ cover.card := Finset.card_le_card hsubset
    have h₂ :
        cover.card ≤
          ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card := by
      dsimp [cover]
      calc cover.card
          ≤ ∑ c, (Finset.univ.biUnion fun S => violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ c, ∑ S, (violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card := by
          gcongr
          exact Finset.card_biUnion_le
    exact h₁.trans h₂
  have huniform :
      ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)),
        ((violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card : ℝ) ≤
          (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
    intro c S
    set i := matrixOnesLevel O.hn c
    by_cases hi1 : 1 ≤ i
    · have ht_le : totalColumnOnes c ≤ m * n := by
        unfold totalColumnOnes
        have hcol (j : Fin n) : (c j).val ≤ m := Nat.lt_succ_iff.mp (c j).isLt
        have hle : totalColumnOnes c ≤ n * m := by
          dsimp [totalColumnOnes]
          calc ∑ j₀ : Fin n, (c j₀).val
              ≤ ∑ _j : Fin n, m := Finset.sum_le_sum fun j _ => hcol j
            _ = n * m := by simp [Finset.sum_const, Finset.card_fin]
        rw [← Nat.mul_comm]
        exact hle
      have him : i ≤ m := matrixOnesLevel_le_m O.hn c ht_le
      have hclass : TotalColumnOnesLeLevel m n i c := by
        dsimp [TotalColumnOnesLeLevel]
        exact totalColumnOnes_le_mul_matrixOnesLevel O.hn c
      by_cases hs : 0 < S.card
      · have hle :=
          violatorsAtLevel_card_le_on O.hm O.hn epsB hepsB i c hclass S hs
        have hs1 : 1 ≤ S.card := Nat.one_le_iff_ne_zero.mpr hs.ne'
        have hsn : S.card ≤ n := by
          simpa [Fintype.card_fin] using (S.card_le_univ : S.card ≤ Finset.univ.card)
        have hrate := lemma61_exp_bound m n S.card epsB O.hm1 hs1 hsn O.hn1 O.heps
        exact hle.trans (mul_le_mul_of_nonneg_right hrate (le_of_lt hNpos))
      · have hempty : violatorsAtLevel epsB i c S = ∅ := by simp [violatorsAtLevel, hs]
        rw [show ((violatorsAtLevel epsB i c S).card : ℝ) = 0 from by simp [hempty]]
        positivity
    · have hi0 : i = 0 := by omega
      have htot0 : totalColumnOnes c = 0 :=
        totalColumnOnes_eq_zero_of_matrixOnesLevel_eq_zero O.hn c hi0
      have hempty : violatorsAtLevel epsB i c S = ∅ := by
        by_cases hs : 0 < S.card
        · have hnot : ∀ σ, σ ∉ violatorsAtLevel epsB i c S := by
            intro σ
            rw [mem_violatorsAtLevel epsB i c S σ hs, hi0]
            intro hle
            have hones : (onesInColumns c σ S : ℝ) = 0 := by
              exact_mod_cast onesInColumns_eq_zero_of_totalColumnOnes_eq_zero c σ S htot0
            have hpos : 0 < paperThreshold m n epsB 0 S.card := by
              rw [paperThreshold_eq_is_mul O.hm epsB 0 S.card hs]
              have hmn : 0 < (m * n : ℝ) := by exact_mod_cast (Nat.mul_pos O.hm O.hn)
              nlinarith [hepsB, hmn]
            linarith
          exact Finset.eq_empty_iff_forall_notMem.mpr hnot
        · simp [violatorsAtLevel, hs]
      rw [show ((violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card : ℝ) = 0 from by
        simp [hempty, i]]
      positivity
  have hcountC : Fintype.card (MonotoneColumnSums m n) = (m + 1) ^ n := by
    simp [monotoneColumnSums_card]
  have hcountS : Fintype.card (Finset (Fin n)) = 2 ^ n := finset_card n
  have hsumReal :
      ((∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          (violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card) : ℝ) ≤
        lemma61_failFactor m n * N := by
    have hstep :
        ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            ((violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card : ℝ) ≤
          ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
      refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun S _ => ?_
      exact huniform c S
    calc
      _ = ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            ((violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card : ℝ) := by simp
      _ ≤ ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
            (Real.exp 1 * m) ^ (-(n : ℝ)) * N := hstep
      _ = ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
          simp [Finset.sum_const, Finset.card_univ, hcountC, hcountS, mul_assoc, mul_left_comm,
            mul_comm]
      _ = lemma61_failFactor m n * N := by
          have h :
              ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) =
                lemma61_failFactor m n := by
            have hpow : (2 : ℝ) ^ n * (Real.exp 1 * m) ^ (-(n : ℝ)) =
                ((2 : ℝ) / (Real.exp 1 * m)) ^ n := by
              have hx : 0 < Real.exp 1 * m :=
                mul_pos (Real.exp_pos _) (by exact_mod_cast O.hm)
              rw [div_pow, div_eq_mul_inv]
              congr 1
              rw [Real.rpow_neg (le_of_lt hx), Real.rpow_natCast]
            calc ((m + 1 : ℝ) ^ n) * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ))
                = ((m + 1 : ℝ) ^ n) * ((2 : ℝ) / (Real.exp 1 * m)) ^ n := by
                    rw [← hpow, mul_assoc]
              _ = lemma61_failFactor m n := by
                    rw [← lemma61_union_eq_failFactor m n O.hm]
          rw [h]
  have hcastEq :
      ↑(∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          (violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card) =
        ∑ c : MonotoneColumnSums m n, ∑ S : Finset (Fin n),
          ((violatorsAtLevel epsB (matrixOnesLevel O.hn c) c S).card : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => (Nat.cast_sum (s := Finset.univ) _)
  exact le_trans (by rw [← hcastEq]; exact Nat.cast_le.mpr hcardNat) hsumReal

theorem ExistsCombinatorialPropertyBOnPipeline_of_decodeClass {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n) (O : DecodeMatrixClassObligation m n epsB) :
    ExistsCombinatorialPropertyBOnPipeline m n epsB :=
  exists_combinatorialPropertyB_onPipeline_of_failBound m n epsB hm hn
    (lt_trans (lemma61_failFactor_lt_one_hundredth m n hm hn) (by norm_num : (1 / 100 : ℝ) < 1))
    (lemma61FailBound_onPipeline_of_decodeClass epsB O)

theorem ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_m100 {epsB : ℝ}
    (O : DecodeMatrixClassObligation 100 16 epsB) :
    ExistsCombinatorialPropertyBOnPipeline 100 16 epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_decodeClass (by norm_num) (by norm_num) O

theorem Lemma61Obligation_of_failBoundObligation {m n : Nat} {epsB : ℝ}
    (O : Lemma61FailBoundObligation m n epsB)
    (hm : 100 ≤ m) (hn : 16 ≤ n) :
    Lemma61Obligation m n epsB where
  hm := hm
  hn := hn
  heps := O.heps
  failBound := lemma61FailBound_of_levelExp1 epsB O

theorem Lemma61Obligation_of_avgRowOnes_le_one {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (havg : AvgRowOnesLeOne m n) :
    Lemma61Obligation m n epsB :=
  Lemma61Obligation_of_failBoundObligation
    (Lemma61FailBoundObligation.of_avgRowOnes_le_one
      (by omega) (by omega) (by omega) (by omega) heps havg)
    hm hn

theorem Lemma61Obligation_of_totalColumnOnesLeN {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (h : TotalColumnOnesLeN m n) :
    Lemma61Obligation m n epsB :=
  Lemma61Obligation_of_failBoundObligation
    (Lemma61FailBoundObligation.of_totalColumnOnesLeN
      (by omega) (by omega) (by omega) (by omega) heps h)
    hm hn

theorem ExistsCombinatorialPropertyB_of_avgRowOnes_le_one {m n : Nat} {epsB : ℝ}
    (hm : 100 ≤ m) (hn : 16 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (havg : AvgRowOnesLeOne m n) :
    ExistsCombinatorialPropertyB m n epsB :=
  ExistsCombinatorialPropertyB_ofObligation
    (Lemma61Obligation_of_avgRowOnes_le_one hm hn heps havg)

/-! **Lemma 6.2 union over `(c, j, S)`** -/

noncomputable def fringeViolatorsAtCell {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ)
    (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)) : Finset (Scramble m n) := by
  classical
  exact Finset.univ.filter fun σ => fringeColumnEventBad hf deltaF epsF c σ j S

theorem mem_fringeViolatorsAtCell {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ)
    (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)) (σ : Scramble m n) :
    σ ∈ fringeViolatorsAtCell hf deltaF epsF c j S ↔
      fringeColumnEventBad hf deltaF epsF c σ j S := by
  simp [fringeViolatorsAtCell]

theorem fringeViolatorsAtCell_card_le {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ)
    (C : Lemma62FringeCellBound m n f hf deltaF epsF)
    (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n))
    (hj : 0 < j) (hjδ : (j : ℝ) ≤ deltaF * (f * n)) :
    (fringeViolatorsAtCell hf deltaF epsF c j S).card ≤
      (Real.exp 1 * m) ^ (-(n : ℝ)) * (Fintype.card (Scramble m n) : ℝ) := by
  classical
  exact C.bound c j S hj hjδ (fringeViolatorsAtCell hf deltaF epsF c j S)
    fun σ hσ => (Finset.mem_filter.mp hσ).2

theorem bad_scramble_mem_fringeViolators {m n f : Nat} (hf : Even f) (deltaF epsF : ℝ)
    (σ : Scramble m n) (hnot : ¬ HasCombinatorialPropertyF hf σ deltaF epsF) :
    ∃ (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)),
      0 < j ∧ (j : ℝ) ≤ deltaF * (f * n) ∧
        σ ∈ fringeViolatorsAtCell hf deltaF epsF c j S := by
  classical
  rcases (not_hasCombinatorialPropertyF_iff hf σ deltaF epsF).1 hnot with
    ⟨c, j, S, hj, hjδ, hbad⟩
  exact ⟨c, j, S, hj, hjδ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩

/-- Discharge Lemma 6.2 fail union from per-cell Chernoff and a paper closing bound. -/
structure Lemma62CellCountingObligation (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) where
  hm : 0 < m
  hn : 0 < n
  hm100 : 100 ≤ m
  hn16 : 16 ≤ n
  inner : Lemma62InnerBound
  jMax : Nat
  hjMax :
    ∀ j : Nat, 0 < j → (j : ℝ) ≤ deltaF * (f * n) → j ≤ jMax
  hjMax_top : (jMax : ℝ) ≤ deltaF * (f * n)
  cellExp : Lemma62FringeCellBound m n f hf deltaF epsF
  hclose :
    ((m + 1 : ℝ) ^ n) * (2 ^ n) * jMax * (Real.exp 1 * m) ^ (-(n : ℝ)) ≤
      lemma62_failFactor inner.x

theorem lemma62FailBound_of_cellExp {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    Lemma62FailBound m n f hf deltaF epsF O.inner.x := by
  classical
  refine { bound := ?_ }
  intro bad hbad
  set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
  have _hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hcell :
      ∀ (σ : Scramble m n), σ ∈ bad →
        ∃ (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)),
          0 < j ∧ (j : ℝ) ≤ deltaF * (f * n) ∧
            σ ∈ fringeViolatorsAtCell hf deltaF epsF c j S := by
    intro σ hσ
    exact bad_scramble_mem_fringeViolators hf deltaF epsF σ (hbad σ hσ)
  have hsubset :
      bad ⊆
        Finset.biUnion (Finset.univ : Finset (MonotoneColumnSums m n)) fun c =>
          Finset.biUnion (Finset.Ioc 0 O.jMax) fun j =>
            Finset.biUnion (Finset.univ : Finset (Finset (Fin n))) fun S =>
              fringeViolatorsAtCell hf deltaF epsF c j S := by
    intro σ hσ
    obtain ⟨c, j, S, hj, hjδ, hmem⟩ := hcell σ hσ
    have hjle : j ≤ O.jMax := O.hjMax j hj hjδ
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ioc.mpr ⟨hj, hjle⟩, ?_⟩
    refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ _, hmem⟩
  set cover :=
    Finset.biUnion (Finset.univ : Finset (MonotoneColumnSums m n)) fun c =>
      Finset.biUnion (Finset.Ioc 0 O.jMax) fun j =>
        Finset.biUnion (Finset.univ : Finset (Finset (Fin n))) fun S =>
          fringeViolatorsAtCell hf deltaF epsF c j S
  have hcardNat :
      bad.card ≤
        ∑ c : MonotoneColumnSums m n,
          ∑ j ∈ Finset.Ioc 0 O.jMax,
            ∑ S : Finset (Fin n), (fringeViolatorsAtCell hf deltaF epsF c j S).card := by
    have h₁ : bad.card ≤ cover.card := Finset.card_le_card hsubset
    have h₂ :
        cover.card ≤
          ∑ c : MonotoneColumnSums m n,
            ∑ j ∈ Finset.Ioc 0 O.jMax,
              ∑ S : Finset (Fin n), (fringeViolatorsAtCell hf deltaF epsF c j S).card := by
      have hle₁ : cover.card ≤
          ∑ c : MonotoneColumnSums m n,
            ((Finset.Ioc 0 O.jMax).biUnion fun j =>
              Finset.univ.biUnion fun S => fringeViolatorsAtCell hf deltaF epsF c j S).card :=
        Finset.card_biUnion_le
      have hle₂ :
          ∑ c : MonotoneColumnSums m n,
              ((Finset.Ioc 0 O.jMax).biUnion fun j =>
                Finset.univ.biUnion fun S => fringeViolatorsAtCell hf deltaF epsF c j S).card ≤
            ∑ c : MonotoneColumnSums m n,
              ∑ j ∈ Finset.Ioc 0 O.jMax,
                (Finset.univ.biUnion fun S => fringeViolatorsAtCell hf deltaF epsF c j S).card := by
        gcongr
        exact Finset.card_biUnion_le
      have hle₃ :
          ∑ c : MonotoneColumnSums m n,
              ∑ j ∈ Finset.Ioc 0 O.jMax,
                (Finset.univ.biUnion fun S => fringeViolatorsAtCell hf deltaF epsF c j S).card ≤
            ∑ c : MonotoneColumnSums m n,
              ∑ j ∈ Finset.Ioc 0 O.jMax,
                ∑ S : Finset (Fin n), (fringeViolatorsAtCell hf deltaF epsF c j S).card := by
        gcongr
        exact Finset.card_biUnion_le
      exact hle₁.trans (hle₂.trans hle₃)
    exact h₁.trans h₂
  have huniform :
      ∀ (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)),
        j ∈ Finset.Ioc 0 O.jMax →
          ((fringeViolatorsAtCell hf deltaF epsF c j S).card : ℝ) ≤
            (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
    intro c j S hjIoc
    have hj : 0 < j := (Finset.mem_Ioc.mp hjIoc).1
    have hjδ : (j : ℝ) ≤ deltaF * (f * n) := by
      have hjle : j ≤ O.jMax := (Finset.mem_Ioc.mp hjIoc).2
      have hjleR : (j : ℝ) ≤ O.jMax := by exact_mod_cast hjle
      exact hjleR.trans O.hjMax_top
    exact fringeViolatorsAtCell_card_le hf deltaF epsF O.cellExp c j S hj hjδ
  have hcountC : Fintype.card (MonotoneColumnSums m n) = (m + 1) ^ n := by
    simp [monotoneColumnSums_card]
  have hcountS : Fintype.card (Finset (Fin n)) = 2 ^ n := finset_card n
  have hjcard : (Finset.Ioc 0 O.jMax).card = O.jMax := by
    simpa using Finset.card_Ioc (n := 0) (m := O.jMax)
  have hsumReal :
      ((∑ c : MonotoneColumnSums m n,
          ∑ j ∈ Finset.Ioc 0 O.jMax,
            ∑ S : Finset (Fin n),
              (fringeViolatorsAtCell hf deltaF epsF c j S).card) : ℝ) ≤
        lemma62_failFactor O.inner.x * N := by
    have hstep :
        ∑ c : MonotoneColumnSums m n,
            ∑ j ∈ Finset.Ioc 0 O.jMax,
              ∑ S : Finset (Fin n),
                ((fringeViolatorsAtCell hf deltaF epsF c j S).card : ℝ) ≤
          ∑ c : MonotoneColumnSums m n,
            ∑ j ∈ Finset.Ioc 0 O.jMax,
              ∑ S : Finset (Fin n), (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
      refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun S _ => ?_
      exact huniform c j S hj
    calc
      _ = ∑ c, ∑ j ∈ Finset.Ioc 0 O.jMax, ∑ S,
            ((fringeViolatorsAtCell hf deltaF epsF c j S).card : ℝ) := by simp
      _ ≤ ∑ c, ∑ j ∈ Finset.Ioc 0 O.jMax, ∑ S, (Real.exp 1 * m) ^ (-(n : ℝ)) * N := hstep
      _ = ((m + 1 : ℝ) ^ n) * O.jMax * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) * N := by
          simp [Finset.sum_const, Finset.card_univ, hcountC, hcountS, hjcard, mul_assoc,
            mul_left_comm, mul_comm]
      _ ≤ lemma62_failFactor O.inner.x * N := by
          gcongr
          have hrearr :
              ((m + 1 : ℝ) ^ n) * O.jMax * (2 ^ n) * (Real.exp 1 * m) ^ (-(n : ℝ)) =
                ((m + 1 : ℝ) ^ n) * (2 ^ n) * O.jMax * (Real.exp 1 * m) ^ (-(n : ℝ)) := by
            ring
          rw [hrearr]
          exact O.hclose
  have hcastEq :
      ↑(∑ c : MonotoneColumnSums m n,
          ∑ j ∈ Finset.Ioc 0 O.jMax,
            ∑ S : Finset (Fin n),
              (fringeViolatorsAtCell hf deltaF epsF c j S).card) =
        ∑ c : MonotoneColumnSums m n,
          ∑ j ∈ Finset.Ioc 0 O.jMax,
            ∑ S : Finset (Fin n),
              ((fringeViolatorsAtCell hf deltaF epsF c j S).card : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => (Nat.cast_sum (s := Finset.univ) _)
  exact le_trans (by rw [← hcastEq]; exact Nat.cast_le.mpr hcardNat) hsumReal

def Lemma62FailBoundObligation_of_cellCounting {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    Lemma62FailBoundObligation m n f hf deltaF epsF where
  hm := O.hm100
  hn := O.hn16
  inner := O.inner
  hfail := lemma62FailBound_of_cellExp O

def Lemma62CountingObligation_of_cellCounting {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    Lemma62CountingObligation m n f hf deltaF epsF where
  hm := O.hm100
  hn := O.hn16
  inner := O.inner
  cellExp := O.cellExp
  hfail := lemma62FailBound_of_cellExp O

/-! **Module A combinatorial existence (Lemmas 6.1–6.2 counting)** -/

structure ModuleACombinatorialObligation (m n : Nat) (epsB : ℝ) (f : Nat) (hf : Even f)
    (deltaF epsF : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  B : DecodeMatrixClassObligation m n epsB
  F : Lemma62CellCountingObligation m n f hf deltaF epsF

theorem ExistsCombinatorialPropertyBOnPipeline_of_ModuleA_m100 {epsB : ℝ} {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyBOnPipeline 100 16 epsB :=
  ExistsCombinatorialPropertyBOnPipeline_of_decodeClass_m100 O.B

theorem ExistsCombinatorialPropertyB_of_ModuleA {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (havg : AvgRowOnesLeOne m n)
    (O : ModuleACombinatorialObligation m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyB m n epsB :=
  ExistsCombinatorialPropertyB_ofObligation
    (Lemma61Obligation_of_failBoundObligation
      (Lemma61FailBoundObligation.of_avgRowOnes_le_one O.B.hm O.B.hn O.B.hm1 O.B.hn1 O.B.heps
        havg)
      O.hm O.hn)

theorem ExistsCombinatorialPropertyF_of_ModuleA {m n : Nat} {epsB : ℝ} {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : ModuleACombinatorialObligation m n epsB f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_ofObligation
    (Lemma62FailBoundObligation_of_cellCounting O.F)

theorem ExistsCombinatorialPropertyF_of_cellCounting {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_ofObligation (Lemma62FailBoundObligation_of_cellCounting O)

/-- Supply `cellExp` from fringe Chernoff hypotheses; `hclose` and `jMax` remain numeric obligations. -/
def Lemma62CellCountingObligation.of_fringeCellHyp {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (H : Lemma62FringeCellBoundHyp m n f hf deltaF epsF)
    (hm : 0 < m) (hn : 0 < n) (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (inner : Lemma62InnerBound) (jMax : Nat)
    (hjMax : ∀ j : Nat, 0 < j → (j : ℝ) ≤ deltaF * (f * n) → j ≤ jMax)
    (hjMax_top : (jMax : ℝ) ≤ deltaF * (f * n))
    (hclose :
      ((m + 1 : ℝ) ^ n) * (2 ^ n) * jMax * (Real.exp 1 * m) ^ (-(n : ℝ)) ≤
        lemma62_failFactor inner.x) :
    Lemma62CellCountingObligation m n f hf deltaF epsF where
  hm := hm
  hn := hn
  hm100 := hm100
  hn16 := hn16
  inner := inner
  jMax := jMax
  hjMax := hjMax
  hjMax_top := hjMax_top
  cellExp := Lemma62FringeCellBound.of_hyp H
  hclose := hclose

def Lemma62CellCountingObligation.of_fringeCellHyp_cellUnion {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (H : Lemma62FringeCellBoundHyp m n f hf deltaF epsF)
    (hm : 0 < m) (hn : 0 < n) (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (inner : Lemma62InnerBound) (jMax : Nat)
    (hjMax : ∀ j : Nat, 0 < j → (j : ℝ) ≤ deltaF * (f * n) → j ≤ jMax)
    (hjMax_top : (jMax : ℝ) ≤ deltaF * (f * n))
    (hclose : lemma62_cellUnionFactor m n jMax ≤ lemma62_failFactor inner.x) :
    Lemma62CellCountingObligation m n f hf deltaF epsF :=
  of_fringeCellHyp H hm hn hm100 hn16 inner jMax hjMax hjMax_top
    (lemma62_cellUnionFactor_le_failFactor inner hclose)

/-- Section-7-style cap `jMax = ⌊δ_F · f · n⌋` with `δ_F ≤ 1/25`. -/
noncomputable def Lemma62CellCountingObligation.of_params7_jMax {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (H : Lemma62FringeCellBoundHyp m n f hf deltaF epsF)
    (hm : 0 < m) (hn : 0 < n) (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (inner : Lemma62InnerBound)
    (hdeltaF_nonneg : 0 ≤ deltaF)
    (_hdeltaF : deltaF ≤ 1 / 25)
    (hclose : lemma62_cellUnionFactor m n (lemma62_jMax deltaF f n) ≤ lemma62_failFactor inner.x) :
    Lemma62CellCountingObligation m n f hf deltaF epsF :=
  of_fringeCellHyp_cellUnion H hm hn hm100 hn16 inner (lemma62_jMax deltaF f n)
    (fun j hj hjδ => lemma62_jMax_hjMax j hj hjδ)
    (lemma62_jMax_le deltaF f n (lemma62_jMax_fn_nonneg f n hdeltaF_nonneg)) hclose

def Lemma62CellCountingObligation.of_avgRowOnes {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (hn : 0 < n) (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (havg : AvgRowOnesLeOne m n) (hm : 0 < m) (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmF : 1 ≤ fringeRowCount m f hf)
    (inner : Lemma62InnerBound) (jMax : Nat)
    (hjMax : ∀ j : Nat, 0 < j → (j : ℝ) ≤ deltaF * (f * n) → j ≤ jMax)
    (hjMax_top : (jMax : ℝ) ≤ deltaF * (f * n))
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log m) * n * fringeRowCount m f hf * n / 2) ≤
        epsF)
    (hclose : lemma62_cellUnionFactor m n jMax ≤ lemma62_failFactor inner.x) :
    Lemma62CellCountingObligation m n f hf deltaF epsF :=
  let H :=
    Lemma62FringeCellBoundHyp.of_avgRowOnes_worstEps hn hepsF hf2 havg hm1 hn1 hmF hepsWorst
  of_fringeCellHyp_cellUnion H hm hn hm100 hn16 inner jMax hjMax hjMax_top hclose

def ModuleACombinatorialObligation.of_decodeClass_and_cellCounting {m n : Nat} {epsB : ℝ}
    {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (B : DecodeMatrixClassObligation m n epsB)
    (F : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    ModuleACombinatorialObligation m n epsB f hf deltaF epsF where
  hm := hm100
  hn := hn16
  B := B
  F := F

def ModuleACombinatorialObligation.of_avgRowOnes_and_cellCounting {m n : Nat} {epsB : ℝ}
    {f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (hm100 : 100 ≤ m) (hn16 : 16 ≤ n)
    (havg : AvgRowOnesLeOne m n)
    (hepsB : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB)
    (F : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    ModuleACombinatorialObligation m n epsB f hf deltaF epsF :=
  of_decodeClass_and_cellCounting hm100 hn16
    (DecodeMatrixClassObligation.of_totalColumnOnesLeN
      (by omega) (by omega) (by omega) (by omega) hepsB
      (TotalColumnOnesLeN.of_avgRowOnesLeOne (by omega) havg))
    F

/-- Minimal §7-style F discharge: avg-row-ones density + worst-case `ε_F` sqrt + numeric close. -/
theorem ExistsCombinatorialPropertyF_of_params7_style {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_of_cellCounting O

theorem ExistsCombinatorialPropertyF_of_avgRowOnes_cellCounting {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation m n f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_of_params7_style O

/-- Paper minima `m = 100`, `n = 16`, `⌊δ_F f n⌋ ≤ 48`, inner `x = 3/10`. -/
noncomputable def Lemma62CellCountingObligation.m100_n16_jMax48 {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (hdeltaF : 0 ≤ deltaF) (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (havg : AvgRowOnesLeOne 100 16) (hmF : 1 ≤ fringeRowCount 100 f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 f hf * 16 / 2) ≤
        epsF)
    (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    Lemma62CellCountingObligation 100 16 f hf deltaF epsF := by
  let jMax := lemma62_jMax deltaF f 16
  refine of_avgRowOnes (by norm_num : (0 : Nat) < 16) hepsF hf2 havg (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmF Lemma62InnerBound.thirty jMax
    (fun j hj hjδ => lemma62_jMax_hjMax j hj hjδ)
    (lemma62_jMax_le deltaF f 16 (lemma62_jMax_fn_nonneg f 16 hdeltaF)) hepsWorst
    (lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16 hjMax48)

/-- F-side counting from fringe Chernoff hypotheses (per-cell `hepsCell`, not worst-case `hepsWorst`). -/
noncomputable def Lemma62CellCountingObligation.m100_n16_jMax48_of_fringeHyp {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (hdeltaF : 0 ≤ deltaF)
    (H : Lemma62FringeCellBoundHyp 100 16 f hf deltaF epsF)
    (hjMax48 : lemma62_jMax deltaF f 16 ≤ 48) :
    Lemma62CellCountingObligation 100 16 f hf deltaF epsF :=
  of_fringeCellHyp_cellUnion H (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Lemma62InnerBound.thirty (lemma62_jMax deltaF f 16)
    (fun j hj hjδ => lemma62_jMax_hjMax j hj hjδ)
    (lemma62_jMax_le deltaF f 16 (lemma62_jMax_fn_nonneg f 16 hdeltaF))
    (lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16 hjMax48)

theorem moduleA_fringeCellBoundHyp_f16 {epsF : ℝ} (hepsF : 0 < epsF)
    (havg : AvgRowOnesLeOne 100 16)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log 100) * 16 * fringeRowCount 100 16 (by decide : Even 16) * 16 / 2) ≤
        epsF) :
    Lemma62FringeCellBoundHyp 100 16 16 (by decide : Even 16) (invariant7.deltaF : ℝ) epsF :=
  Lemma62FringeCellBoundHyp.of_avgRowOnes_worstEps (by norm_num) hepsF (by norm_num) havg
    (by norm_num) (by norm_num) params7Geometry_f16_hmF hepsWorst

theorem moduleA_fringeCellBoundHyp_f16_eps300 (havg : AvgRowOnesLeOne 100 16) :
    Lemma62FringeCellBoundHyp 100 16 16 (by decide : Even 16) (invariant7.deltaF : ℝ) (300 : ℝ) :=
  moduleA_fringeCellBoundHyp_f16 (by norm_num) havg moduleA_hepsWorst_f16_le_300

theorem ExistsCombinatorialPropertyF_m100_n16_jMax48 {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (O : Lemma62CellCountingObligation 100 16 f hf deltaF epsF) :
    ExistsCombinatorialPropertyF 100 16 f hf deltaF epsF :=
  ExistsCombinatorialPropertyF_of_params7_style O

theorem scramble_card_pos (m n : Nat) : 0 < Fintype.card (Scramble m n) :=
  Fintype.card_pos

/-- Global (non-pipeline) B∧F scramble when `AvgRowOnesLeOne` supports Lemma 6.1 level-1 union. -/
theorem ExistsCombinatorialScrambleBF_of_ModuleA_m100 {epsB : ℝ} {f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (havg : AvgRowOnesLeOne 100 16)
    (O : ModuleACombinatorialObligation 100 16 epsB f hf deltaF epsF)
    (hinner : O.F.inner = Lemma62InnerBound.thirty) :
    ExistsCombinatorialScrambleBF 100 16 f hf epsB deltaF epsF := by
  have hB := lemma61FailBound_of_levelExp1 epsB
    (Lemma61FailBoundObligation.of_avgRowOnes_le_one O.B.hm O.B.hn O.B.hm1 O.B.hn1 O.B.heps havg)
  have hF := lemma62FailBound_of_cellExp O.F
  have hNpos : 0 < Fintype.card (Scramble 100 16) := scramble_card_pos 100 16
  have hαβ := moduleA_global_failFraction_add_lt_one_m100
  have hαβ' :
      lemma61_failFactor 100 16 + lemma62_failFactor O.F.inner.x < 1 := by
    rw [hinner]
    exact hαβ
  exact exists_combinatorialScrambleBF_of_failFractions 100 16 f hf epsB deltaF epsF O.F.inner.x hB
    hF hNpos hαβ'

end Chvatal

/- Bridge theorems and §7 separator entry points live in `AKS.Chvatal.ModuleABridge`. -/
