module
/-
  # Chvátal Lemma 6.2 — Property F for random scrambles

  Source: V. Chvátal, DCS-TR-294 (1992), §6.

  Status: combinatorial fringe model + paper closing sum for fail probability
  `< 49/100`, packaged as `Lemma62FailBoundObligation`. Per-cell fringe Chernoff
  is discharged in `AKS.Chvatal.Lemma62Chernoff` from `FringeOnesDensityLeHalfWidth`
  and explicit `(e m)^{-n}` hypotheses; generic numeric union `hclose` is still a
  hypothesis, but `lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16` closes it
  at `m = 100`, `n = 16`, `jMax ≤ 48`, inner `x = 3/10`.
-/

public import AKS.Chvatal.Lemma63
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

/-! **Combinatorial fringe model (half-depth rows)** -/

/-- Rows strictly above the bottom `f/2` block (paper Lemma 6.2). -/
def aboveHalfFringeRows (m f : Nat) (_hf : Even f) : Finset (Fin m) :=
  Finset.univ.filter fun r => r.val < m - f / 2

def onesAboveHalfFringe {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) : Nat :=
  ∑ r ∈ aboveHalfFringeRows m f hf, rowHit c S r (σ r)

theorem onesAboveHalfFringe_eq_sum_rowHit {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n) :
    onesAboveHalfFringe hf c σ S = ∑ r ∈ aboveHalfFringeRows m f hf, rowHit c S r (σ r) := rfl

noncomputable def fringeRowCount (m f : Nat) (hf : Even f) : Nat :=
  (aboveHalfFringeRows m f hf).card

theorem Finset.card_filter_fin_val_lt (m t : Nat) (ht : t ≤ m) :
    (Finset.univ.filter (fun r : Fin m => r.val < t)).card = t := by
  classical
  let e : { r : Fin m // r.val < t } ≃ Fin t :=
    { toFun := fun r => ⟨r.val, r.property⟩
      invFun := fun i =>
        have him : i.val < m := Nat.lt_of_lt_of_le i.isLt ht
        ⟨Fin.mk i.val him, i.isLt⟩
      left_inv := by
        intro r
        ext
        simp [Fin.ext_iff]
      right_inv := by
        intro i
        ext
        simp [Fin.ext_iff] }
  calc
    (Finset.univ.filter (fun r : Fin m => r.val < t)).card
        = Fintype.card { r : Fin m // r.val < t } := by rw [Fintype.card_subtype]
    _ = t := (Fintype.card_congr e).trans (Fintype.card_fin t)

theorem fringeRowCount_eq (m f : Nat) (hf : Even f) :
    fringeRowCount m f hf = m - f / 2 := by
  unfold fringeRowCount aboveHalfFringeRows
  set t := m - f / 2
  by_cases ht0 : t = 0
  · rw [ht0]
    have hfilter : (Finset.univ.filter (fun r : Fin m => r.val < 0)) = ∅ := by
      ext r
      simp [Finset.mem_filter, not_lt_zero]
    rw [hfilter, Finset.card_empty]
  · have ht : t ≤ m := Nat.sub_le _ _
    rw [Finset.card_filter_fin_val_lt m t ht]

theorem one_le_fringeRowCount {m f : Nat} (hf : Even f) (hm : f / 2 < m) :
    1 ≤ fringeRowCount m f hf := by
  rw [fringeRowCount_eq m f hf]
  exact Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hm)

theorem fringeRowCount_m100_f16 :
    fringeRowCount 100 16 (by decide : Even 16) = 92 := by
  rw [fringeRowCount_eq 100 16 (by decide : Even 16), show 100 - 16 / 2 = 92 from by norm_num]

noncomputable def fringeOnesDensity {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) : ℝ :=
  let mF := fringeRowCount m f hf
  if hmF : mF = 0 then 0
  else
    (∑ r ∈ aboveHalfFringeRows m f hf, ((monotoneRowOnes c r).card : ℝ)) / (mF * n)

/-- Paper event `E` at `(c,j,S)` for a fixed scramble (Lemma 6.2). -/
def fringeColumnEventBad {m n f : Nat} (hf : Even f) (_deltaF epsF : ℝ)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat) (S : Finset (Fin n)) :
    Prop :=
  (f / 2 : ℝ) * S.card + epsF * j ≤ (onesAboveHalfFringe hf c σ S : ℝ)

def HasCombinatorialPropertyF {m n f : Nat} (hf : Even f) (σ : Scramble m n)
    (deltaF epsF : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (j : Nat),
    0 < j → (j : ℝ) ≤ deltaF * (f * n) →
      ∀ (S : Finset (Fin n)), ¬ fringeColumnEventBad hf deltaF epsF c σ j S

def ExistsCombinatorialPropertyF (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) : Prop :=
  ∃ σ : Scramble m n, HasCombinatorialPropertyF hf σ deltaF epsF

theorem not_hasCombinatorialPropertyF_iff {m n f : Nat} (hf : Even f)
    (σ : Scramble m n) (deltaF epsF : ℝ) :
    ¬ HasCombinatorialPropertyF hf σ deltaF epsF ↔
      ∃ (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)),
        0 < j ∧ (j : ℝ) ≤ deltaF * (f * n) ∧
          fringeColumnEventBad hf deltaF epsF c σ j S := by
  classical
  constructor
  · intro hnot
    by_contra hnone
    push_neg at hnone
    have hF : HasCombinatorialPropertyF hf σ deltaF epsF := by
      intro c j hj hjδ S
      exact hnone c j S hj hjδ
    exact hnot hF
  · intro h
    rcases h with ⟨c, j, S, hj, hjδ, hbad⟩
    intro hF
    exact hF c j hj hjδ S hbad

theorem finset_card (n : Nat) :
    Fintype.card (Finset (Fin n)) = 2 ^ n := by
  classical
  simp [Fintype.card_fin]

/-! **Paper closing numeric (Lemma 6.2, end of proof)** -/

/-- Inner constant `0 < x < 0.32` from Chvátal (6.2). -/
structure Lemma62InnerBound where
  x : ℝ
  hx0 : 0 ≤ x
  hx : x < 32 / 100

/-- Fail fraction from the Lemma 6.2 closing sum (supplied as `x < 0.32`). -/
noncomputable def lemma62_failFactor (x : ℝ) : ℝ := 1.025 * (x / (1 - x))

/-- Paper: `1.025 · ∑_{i≥1} x^i < 0.49` when `0 ≤ x < 0.32`. -/
theorem lemma62_failSum_lt (B : Lemma62InnerBound) :
    (1.025 : ℝ) * ∑' i : ℕ, B.x ^ (i + 1) < 49 / 100 := by
  have hlt1 : B.x < 1 := lt_of_lt_of_le B.hx (by norm_num : (32 / 100 : ℝ) ≤ 1)
  have hbase := tsum_geometric_of_lt_one B.hx0 hlt1
  have hgeom :
      (∑' i : ℕ, B.x ^ (i + 1)) = B.x / (1 - B.x) := by
    have hmul : ∑' i : ℕ, B.x ^ (i + 1) = B.x * ∑' i : ℕ, B.x ^ i := by
      rw [← tsum_mul_left]
      refine tsum_congr fun i => ?_
      rw [pow_succ, mul_comm]
    rw [hmul, hbase]
    field_simp [sub_ne_zero.mpr hlt1.ne]
  have hden_pos : (0 : ℝ) < 1 - B.x := sub_pos.mpr hlt1
  have hden32 : (0 : ℝ) < 1 - 32 / 100 := by norm_num
  have hbound : B.x / (1 - B.x) < 32 / 68 := by
    by_cases h0 : B.x = 0
    · rw [h0]; simp
    have h2 : B.x * (1 - 32 / 100 : ℝ) < (32 / 100) * (1 - B.x) := by
      nlinarith [B.hx0, B.hx]
    have h2' : B.x / (1 - B.x) < (32 / 100) / (1 - 32 / 100) :=
      (div_lt_div_iff₀ hden_pos hden32).2 h2
    calc B.x / (1 - B.x)
        < (32 / 100) / (1 - 32 / 100) := h2'
      _ = 32 / 68 := by norm_num
  have h32 : (1.025 : ℝ) * (32 / 68) < 49 / 100 := by norm_num
  calc (1.025 : ℝ) * ∑' i : ℕ, B.x ^ (i + 1)
      = (1.025 : ℝ) * (B.x / (1 - B.x)) := by rw [hgeom]
    _ < (1.025 : ℝ) * (32 / 68) := by gcongr
    _ < 49 / 100 := h32

/-- Union-bound factor in `Lemma62CellCountingObligation.hclose` (before `lemma62_failFactor`). -/
noncomputable def lemma62_cellUnionFactor (m n jMax : Nat) : ℝ :=
  (m + 1 : ℝ) ^ n * (2 : ℝ) ^ n * jMax * (Real.exp 1 * m) ^ (-(n : ℝ))

theorem lemma62_cellUnionFactor_eq (m n jMax : Nat) :
    lemma62_cellUnionFactor m n jMax =
      ((m + 1 : ℝ) ^ n) * (2 ^ n) * jMax * (Real.exp 1 * m) ^ (-(n : ℝ)) := by
  unfold lemma62_cellUnionFactor
  ring_nf

theorem lemma62_cellUnionFactor_le_failFactor {m n jMax : Nat} (B : Lemma62InnerBound)
    (h : lemma62_cellUnionFactor m n jMax ≤ lemma62_failFactor B.x) :
    ((m + 1 : ℝ) ^ n) * (2 ^ n) * jMax * (Real.exp 1 * m) ^ (-(n : ℝ)) ≤
      lemma62_failFactor B.x := by
  simpa [lemma62_cellUnionFactor_eq] using h

theorem lemma62_cellUnionFactor_mono_jMax {m n j j' : Nat} (h : j ≤ j') :
    lemma62_cellUnionFactor m n j ≤ lemma62_cellUnionFactor m n j' := by
  unfold lemma62_cellUnionFactor
  gcongr

noncomputable def Lemma62InnerBound.thirty : Lemma62InnerBound where
  x := 3 / 10
  hx0 := by norm_num
  hx := by norm_num

theorem lemma62_failFactor_thirty_eq :
    lemma62_failFactor Lemma62InnerBound.thirty.x = (1.025 : ℝ) * (3 / 7) := by
  unfold lemma62_failFactor Lemma62InnerBound.thirty
  norm_num

/-- Closing union bound at paper minima `m = 100`, `n = 16`, `jMax = 48`, inner `x = 3/10`. -/
theorem lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16_j48 :
    lemma62_cellUnionFactor 100 16 48 ≤ lemma62_failFactor Lemma62InnerBound.thirty.x := by
  rw [lemma62_failFactor_thirty_eq]
  have hcell :
      lemma62_cellUnionFactor 100 16 48 =
        (48 : ℝ) * (2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100)) ^ 16 := by
    unfold lemma62_cellUnionFactor
    push_cast
    have hmpos : (0 : ℝ) < (100 : ℝ) := by norm_num
    have hempos : (0 : ℝ) < Real.exp 1 * 100 := mul_pos (Real.exp_pos 1) hmpos
    rw [Real.rpow_neg hempos.le]
    field_simp [hmpos.ne']
    exact_mod_cast (mul_pow (100 : ℝ) (Real.exp 1) 16).symm
  rw [hcell]
  have hmpos : (0 : ℝ) < (100 : ℝ) := by norm_num
  have hratio : ((100 : ℝ) + 1) / 100 ≤ (101 : ℝ) / 100 := by
    field_simp [hmpos.ne']
    linarith
  have hform :
      2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100) =
        (2 / Real.exp 1) * (((100 : ℝ) + 1) / 100) := by
    field_simp [hmpos.ne']
  have hform' :
      2 * (101 : ℝ) / (Real.exp 1 * 100) =
        (2 / Real.exp 1) * (101 / 100) := by
    field_simp
  have hbase :
      2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100) ≤
        2 * (101 : ℝ) / (Real.exp 1 * 100) := by
    rw [hform, hform']
    exact mul_le_mul_of_nonneg_left hratio (by positivity)
  have he : (2712 / 1000 : ℝ) < Real.exp 1 :=
    LT.lt.trans (by norm_num : (2712 / 1000 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
  have hnum : 2 * (101 : ℝ) / (Real.exp 1 * 100) < (149 / 200 : ℝ) := by
    have hlt :
        2 * (101 : ℝ) / (Real.exp 1 * 100) <
          2 * (101 : ℝ) / ((2712 / 1000) * 100) := by
      refine div_lt_div_of_pos_left (by positivity) (by positivity) ?_
      exact mul_lt_mul_of_pos_right he (by positivity)
    have hval : 2 * (101 : ℝ) / ((2712 / 1000) * 100) = (202000 : ℝ) / 271200 := by
      norm_num
    have h149 : (202000 : ℝ) / 271200 < 149 / 200 := by norm_num
    linarith
  have hbase_nn : (0 : ℝ) ≤ 2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100) := by positivity
  have hnum_nn : (0 : ℝ) ≤ 2 * (101 : ℝ) / (Real.exp 1 * 100) := by positivity
  have hpow :
      (2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100)) ^ 16 ≤
        (2 * (101 : ℝ) / (Real.exp 1 * 100)) ^ 16 :=
    pow_le_pow_left₀ hbase_nn hbase 16
  have hpow_mid :
      (2 * (101 : ℝ) / (Real.exp 1 * 100)) ^ 16 ≤ (149 / 200 : ℝ) ^ 16 :=
    pow_le_pow_left₀ hnum_nn hnum.le 16
  have h48 : (48 : ℝ) * (149 / 200 : ℝ) ^ 16 ≤ (1.025 : ℝ) * (3 / 7) := by norm_num
  calc (48 : ℝ) * (2 * ((100 : ℝ) + 1) / (Real.exp 1 * 100)) ^ 16
      ≤ (48 : ℝ) * (2 * (101 : ℝ) / (Real.exp 1 * 100)) ^ 16 := by gcongr
    _ ≤ (48 : ℝ) * (149 / 200 : ℝ) ^ 16 := by gcongr
    _ ≤ (1.025 : ℝ) * (3 / 7) := h48

theorem lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16 {jMax : Nat}
    (hjMax48 : jMax ≤ 48) :
    lemma62_cellUnionFactor 100 16 jMax ≤ lemma62_failFactor Lemma62InnerBound.thirty.x :=
  le_trans (lemma62_cellUnionFactor_mono_jMax hjMax48)
    lemma62_cellUnionFactor_le_failFactor_thirty_m100_n16_j48

/-- Paper-style `j` loop cap `⌊δ_F · f · n⌋` (Section 7 uses `δ_F ≤ 1/25`). -/
noncomputable def lemma62_jMax (deltaF : ℝ) (f n : Nat) : Nat :=
  Nat.floor (deltaF * ((f * n : ℝ)))

theorem lemma62_jMax_le (deltaF : ℝ) (f n : Nat)
    (hfn : 0 ≤ deltaF * (f * n)) :
    (lemma62_jMax deltaF f n : ℝ) ≤ deltaF * (f * n) := by
  dsimp [lemma62_jMax]
  exact Nat.floor_le hfn

theorem lemma62_jMax_hjMax {f n : Nat} {deltaF : ℝ} (j : Nat)
    (hj : 0 < j) (hjδ : (j : ℝ) ≤ deltaF * (f * n)) :
    j ≤ lemma62_jMax deltaF f n := by
  classical
  have _hfn : 0 ≤ deltaF * (f * n) := le_of_lt (lt_of_lt_of_le (by exact_mod_cast hj) hjδ)
  dsimp [lemma62_jMax]
  exact (Nat.le_floor_iff _hfn).mpr hjδ

theorem lemma62_jMax_fn_nonneg {deltaF : ℝ} (f n : Nat) (hdeltaF : 0 ≤ deltaF) :
    0 ≤ deltaF * (f * n) := by
  positivity

/-- Paper §6.2 loop: `(j : ℝ) ≤ δ_F · f · n` and `δ_F · n < 1` force `j < f` when `f > 0`. -/
theorem j_lt_f_of_le_deltaF_mul {f n j : Nat} {deltaF : ℝ} (hf : 0 < f)
    (hdeltaFn : (deltaF : ℝ) * (n : ℝ) < 1) (hjδ : (j : ℝ) ≤ deltaF * (f * n)) :
    j < f := by
  by_contra hnot
  push_neg at hnot
  have hj' : (f : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hnot
  have hmul : (j : ℝ) ≤ (f : ℝ) * (deltaF * (n : ℝ)) := by
    calc (j : ℝ)
        ≤ deltaF * (f * n) := hjδ
      _ = (f : ℝ) * (deltaF * (n : ℝ)) := by ring
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf
  have : (f : ℝ) ≤ (f : ℝ) * (deltaF * (n : ℝ)) := le_trans hj' hmul
  nlinarith [this, hdeltaFn, hfR]

theorem lemma62_failFactor_lt_fortyNine_hundredth (B : Lemma62InnerBound) :
    lemma62_failFactor B.x < 49 / 100 := by
  unfold lemma62_failFactor
  have hlt1 : B.x < 1 := lt_of_lt_of_le B.hx (by norm_num : (32 / 100 : ℝ) ≤ 1)
  have hbase := tsum_geometric_of_lt_one B.hx0 hlt1
  have hgeom :
      (∑' i : ℕ, B.x ^ (i + 1)) = B.x / (1 - B.x) := by
    have hmul : ∑' i : ℕ, B.x ^ (i + 1) = B.x * ∑' i : ℕ, B.x ^ i := by
      rw [← tsum_mul_left]
      refine tsum_congr fun i => ?_
      rw [pow_succ, mul_comm]
    rw [hmul, hbase]
    field_simp [sub_ne_zero.mpr hlt1.ne]
  calc lemma62_failFactor B.x
      = (1.025 : ℝ) * (B.x / (1 - B.x)) := rfl
    _ = (1.025 : ℝ) * ∑' i : ℕ, B.x ^ (i + 1) := by rw [← hgeom]
    _ < 49 / 100 := lemma62_failSum_lt B

/-- Global fail-fraction bound at the end of Lemma 6.2 (counting form). -/
structure Lemma62FailBound (m n f : Nat) (hf : Even f) (deltaF epsF x : ℝ) : Prop where
  bound :
    ∀ (bad : Finset (Scramble m n)),
      (∀ σ ∈ bad, ¬ HasCombinatorialPropertyF hf σ deltaF epsF) →
        (bad.card : ℝ) ≤
          lemma62_failFactor x * (Fintype.card (Scramble m n) : ℝ)

theorem exists_combinatorialPropertyF_of_failBound
    (m n f : Nat) (hf : Even f) (deltaF epsF x : ℝ)
    (hx0 : 0 ≤ x) (hx : x < 32 / 100)
    (hfail : Lemma62FailBound m n f hf deltaF epsF x) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF := by
  classical
  have hfactor := lemma62_failFactor_lt_fortyNine_hundredth ⟨x, hx0, hx⟩
  have htotpos : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  by_contra hnone
  have hnone' : ∀ σ : Scramble m n, ¬ HasCombinatorialPropertyF hf σ deltaF epsF :=
    fun σ h => hnone ⟨σ, h⟩
  have hle := hfail.bound Finset.univ (fun σ _ => hnone' σ)
  simp only [Finset.card_univ] at hle
  have h1 : (1 : ℝ) ≤ lemma62_failFactor x :=
    le_of_mul_le_mul_left (by simpa [mul_one, mul_comm] using hle) htotpos
  linarith

/-- Per-cell Hoeffding bound for fringe rows (paper Lemma 6.2, event `E`). -/
structure Lemma62FringeCellBound (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n) (j : Nat) (S : Finset (Fin n)),
      0 < j → (j : ℝ) ≤ deltaF * (f * n) →
        ∀ (bad : Finset (Scramble m n)),
          (∀ σ ∈ bad, fringeColumnEventBad hf deltaF epsF c σ j S) →
            (bad.card : ℝ) ≤
              (Real.exp 1 * m) ^ (-(n : ℝ)) * (Fintype.card (Scramble m n) : ℝ)

/-- Residual: discharge `Lemma62FailBound` from `Lemma62FringeCellBound` and the paper
    `(m+1)^n · 2^n · j`-loop accounting (Chvátal §6.2). -/
structure Lemma62CountingObligation (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  inner : Lemma62InnerBound
  cellExp : Lemma62FringeCellBound m n f hf deltaF epsF
  hfail : Lemma62FailBound m n f hf deltaF epsF inner.x

structure Lemma62FailBoundObligation (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) where
  hm : 100 ≤ m
  hn : 16 ≤ n
  inner : Lemma62InnerBound
  hfail : Lemma62FailBound m n f hf deltaF epsF inner.x

theorem ExistsCombinatorialPropertyF_ofObligation
    {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (O : Lemma62FailBoundObligation m n f hf deltaF epsF) :
    ExistsCombinatorialPropertyF m n f hf deltaF epsF :=
  exists_combinatorialPropertyF_of_failBound m n f hf deltaF epsF O.inner.x O.inner.hx0 O.inner.hx O.hfail

/-! **§7 `δ_F = 128/4095`, paper `n = 16`, loop cap `48`** -/

theorem params7_deltaF_nonneg : (0 : ℝ) ≤ (invariant7.deltaF : ℝ) := by
  unfold invariant7
  norm_num

private theorem lemma62_jMax_mono_f {deltaF : ℝ} (hdeltaF : 0 ≤ deltaF) {f g : Nat} (hfg : f ≤ g)
    (n : Nat) :
    lemma62_jMax deltaF f n ≤ lemma62_jMax deltaF g n := by
  dsimp [lemma62_jMax]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfn : (f : ℝ) * n ≤ (g : ℝ) * n := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hfg) hn
  have hmul : deltaF * ((f * n : ℝ)) ≤ deltaF * ((g * n : ℝ)) :=
    mul_le_mul_of_nonneg_left hfn hdeltaF
  exact Nat.floor_mono hmul

theorem lemma62_jMax_params7_f97_n16_le_48 :
    lemma62_jMax (invariant7.deltaF : ℝ) 97 16 ≤ 48 := by
  have hjMax :
      lemma62_jMax (invariant7.deltaF : ℝ) 97 16 = Nat.floor ((198656 : ℝ) / 4095) := by
    dsimp [lemma62_jMax, invariant7]
    congr 1
    norm_num
  have hpos : (0 : ℝ) ≤ (198656 : ℝ) / 4095 := by positivity
  have hfloor : Nat.floor ((198656 : ℝ) / 4095) = 48 := by
    rw [Nat.floor_eq_iff hpos]
    constructor <;> norm_num
  rw [hjMax, hfloor]

theorem lemma62_jMax_params7_f16_le_48 {f : Nat} (hf : f ≤ 97) :
    lemma62_jMax (invariant7.deltaF : ℝ) f 16 ≤ 48 :=
  (lemma62_jMax_mono_f params7_deltaF_nonneg hf 16).trans
    lemma62_jMax_params7_f97_n16_le_48

end Chvatal
