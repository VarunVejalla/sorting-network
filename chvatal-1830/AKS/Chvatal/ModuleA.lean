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







/-! **Lemma 6.2 union over `(c, j, S)`** -/





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




/-! **Module A combinatorial existence (Lemmas 6.1–6.2 counting)** -/

structure ModuleACombinatorialObligation (m n : Nat) (epsB : ℝ) (f : Nat) (hf : Even f)
    (deltaF epsF : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  B : DecodeMatrixClassObligation m n epsB
  F : Lemma62CellCountingObligation m n f hf deltaF epsF




















end Chvatal

/- Bridge theorems and §7 separator entry points live in `AKS.Chvatal.ModuleABridge`. -/
