module
/-
  # Chvátal Lemma 6.1 — Property B for random scrambles

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), §6
  (`http://users.encs.concordia.ca/~chvatal/aks.pdf`).

  Status: kernel-checked algebraic/counting core of Lemma 6.1:
  * εB-threshold ⇒ `exp(-2 t² m s) ≤ (e m)^{-n}`,
  * ones-above-bottom excess ⇒ some column set carries the excess,
  * monotone matrices = `(m+1)^n`,
  * `(m+1)^n · (2/(e m))^n = lemma61_failFactor < 1/100`,
  * `Lemma61FailBound` ⇒ combinatorial Property B exists.

  Residual: general `Lemma63ExpBoundAtLevel` + `Lemma61FailBound` union
  (`Lemma61FailBoundObligation` in `AKS.Chvatal.Lemma63`). Bridge from combinatorial
  Property B to `HasMatrixPropertyB` on the sort–scramble–sort network remains
  open.
-/

public import AKS.Chvatal.Theorem51Core
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace Chvatal

instance (m n : Nat) : Fintype (Scramble m n) :=
  inferInstanceAs (Fintype (Fin m → Equiv.Perm (Fin n)))

instance (m n : Nat) : Nonempty (Scramble m n) :=
  ⟨fun _ => 1⟩

/-! **Combinatorial 0-1 model** -/

abbrev MonotoneColumnSums (m n : Nat) : Type := Fin n → Fin (m + 1)

theorem monotoneColumnSums_card (m n : Nat) :
    Fintype.card (MonotoneColumnSums m n) = (m + 1) ^ n := by
  simp [Fintype.card_fin]

def monotoneRowOnes {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => (m - r.val) ≤ (c j).val

/-- Average number of ones per row in the monotone `0–1` matrix (Chvátal §6). -/
noncomputable def avgRowOnes {m n : Nat} (c : MonotoneColumnSums m n) : ℝ :=
  (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n

theorem avgRowOnes_eq {m n : Nat} (c : MonotoneColumnSums m n) :
    avgRowOnes c = (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n :=
  rfl

/-- **Module A policy A1:** every monotone matrix has average row ones at most `1`.

This is **false** for unrestricted `MonotoneColumnSums` when `m > 1`
(`not_AvgRowOnesLeOne_of_m_gt_one`, witness `maxColumnMonotone`). The sort–scramble
pipeline should only produce matrices in a smaller class (e.g. total column ones
`≤ n` after marking); discharging this globally for all monotone `c` is the
Module A residual. Combinatorial Property B is still stated for all monotone `c`;
`AvgRowOnesLeOne` discharges `Lemma63ExpBoundAtLevel` at level `1` via
`Lemma61FailBoundObligation.of_avgRowOnes_le_one`. -/
def AvgRowOnesLeOne (m n : Nat) : Prop :=
  ∀ (c : MonotoneColumnSums m n), avgRowOnes c ≤ (1 : ℝ)

/-- Total ones in the monotone `0–1` model (`∑ⱼ` column height). -/
def totalColumnOnes {m n : Nat} (c : MonotoneColumnSums m n) : Nat :=
  ∑ j : Fin n, (c j).val

private theorem mem_monotoneRowOnes_iff {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m)
    (j : Fin n) :
    j ∈ monotoneRowOnes c r ↔ (m - r.val) ≤ (c j).val := by
  simp [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem card_filter_row_ge {m : Nat} (rMin : Fin m) :
    (Finset.univ.filter fun r' : Fin m => rMin ≤ r').card = m - rMin.val := by
  classical
  let e : { r' : Fin m // rMin ≤ r' } ≃ Fin (m - rMin.val) :=
    { toFun := fun r => ⟨r.1.val - rMin.val, by have := r.2; have := r.1.isLt; omega⟩
      invFun := fun i : Fin (m - rMin.val) =>
        let r' : Fin m := ⟨rMin.val + i.val, by have := i.isLt; have := rMin.isLt; omega⟩
        have hr : rMin ≤ r' := Fin.mk_le_mk.mpr (Nat.le_add_right rMin.val i.val)
        ⟨r', hr⟩
      left_inv := by
        intro r
        ext
        simp
        omega
      right_inv := by
        intro i
        ext
        simp }
  calc
    (Finset.univ.filter fun r' : Fin m => rMin ≤ r').card
        = Fintype.card { r' : Fin m // rMin ≤ r' } := by rw [Fintype.card_subtype]
    _ = Fintype.card (Fin (m - rMin.val)) := Fintype.card_congr e
    _ = m - rMin.val := Fintype.card_fin (m - rMin.val)

theorem columnHeight_eq_rowCount {m n : Nat} (c : MonotoneColumnSums m n) (j : Fin n) :
    (c j).val =
      (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r).card := by
  classical
  set k := (c j).val
  by_cases hk0 : k = 0
  · rw [hk0]
    have hempty :
        (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r) = ∅ := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_monotoneRowOnes_iff,
        Finset.notMem_empty, iff_false]
      intro hle
      have : r.val < m := r.isLt
      omega
    rw [Finset.card_eq_zero.mpr hempty]
  · have hkm : k ≤ m := Nat.lt_succ_iff.mp (c j).isLt
    set rMin : Fin m := ⟨m - k, by omega⟩
    have hrMin : rMin.val = m - k := rfl
    have hfilter :
        Finset.univ.filter (fun r : Fin m => j ∈ monotoneRowOnes c r) =
          Finset.univ.filter fun r' : Fin m => rMin ≤ r' := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_monotoneRowOnes_iff, Fin.mk_le_mk]
      rw [show (c j).val = k from rfl]
      constructor <;> intro h <;> omega
    rw [hfilter, card_filter_row_ge rMin]
    calc k = m - (m - k) := (Nat.sub_sub_self hkm).symm
      _ = m - rMin.val := by rw [hrMin]

theorem totalColumnOnes_eq_sum_rowOnes {m n : Nat} (c : MonotoneColumnSums m n) :
    totalColumnOnes c = ∑ r : Fin m, (monotoneRowOnes c r).card := by
  classical
  unfold totalColumnOnes
  calc ∑ j : Fin n, (c j).val
      = ∑ j : Fin n,
          (Finset.univ.filter fun r : Fin m => j ∈ monotoneRowOnes c r).card := by
          refine Finset.sum_congr rfl fun j _ => columnHeight_eq_rowCount c j
    _ = ∑ j : Fin n, ∑ r : Fin m, if j ∈ monotoneRowOnes c r then 1 else 0 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_filter]
    _ = ∑ r : Fin m, ∑ j : Fin n, if j ∈ monotoneRowOnes c r then 1 else 0 := Finset.sum_comm
    _ = ∑ r : Fin m, (monotoneRowOnes c r).card := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← Finset.sum_filter (s := Finset.univ)
            (p := fun j : Fin n => j ∈ monotoneRowOnes c r) (f := fun _ => (1 : Nat))]
          simp [Finset.sum_ite, Finset.mem_filter, Finset.mem_univ, true_and]

/-- For `n > 0`, average row ones `≤ 1` iff total column ones `≤ n`. -/
theorem avgRowOnes_le_one_iff_totalColumnOnes_le_n {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    avgRowOnes c ≤ (1 : ℝ) ↔ totalColumnOnes c ≤ n := by
  rw [avgRowOnes_eq]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : (∑ r : Fin m, (monotoneRowOnes c r).card : ℝ) = ↑(totalColumnOnes c) := by
    exact_mod_cast (totalColumnOnes_eq_sum_rowOnes c).symm
  rw [div_le_iff₀ hn0, hcast, one_mul, Nat.cast_le]


/-- Same strength as `AvgRowOnesLeOne` (still false for all monotone matrices when `m > 1`). -/
def TotalColumnOnesLeN (m n : Nat) : Prop :=
  ∀ (c : MonotoneColumnSums m n), totalColumnOnes c ≤ n

theorem TotalColumnOnesLeN_iff_avgRowOnesLeOne {m n : Nat} (hn : 0 < n) :
    TotalColumnOnesLeN m n ↔ AvgRowOnesLeOne m n := by
  constructor
  · intro h c
    exact (avgRowOnes_le_one_iff_totalColumnOnes_le_n hn c).2 (h c)
  · intro h c
    exact (avgRowOnes_le_one_iff_totalColumnOnes_le_n hn c).1 (h c)


theorem TotalColumnOnesLeN.of_avgRowOnesLeOne {m n : Nat} (hn : 0 < n)
    (h : AvgRowOnesLeOne m n) : TotalColumnOnesLeN m n :=
  (TotalColumnOnesLeN_iff_avgRowOnesLeOne hn).2 h

theorem avgRowOnes_le_i_of_totalColumnOnes_le {m n i : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (h : totalColumnOnes c ≤ n * i) :
    (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ (i : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hn)]
  have hsum : (∑ r : Fin m, (monotoneRowOnes c r).card : ℝ) = ↑(totalColumnOnes c) := by
    exact_mod_cast (totalColumnOnes_eq_sum_rowOnes c).symm
  rw [hsum]
  have h' : totalColumnOnes c ≤ i * n := Nat.mul_comm n i ▸ h
  exact_mod_cast h'



/-- Pipeline / decode mass class at paper level `i`: `totalColumnOnes c ≤ n·i`
    (sort–scramble decode at level `i` has equality — see `SortedColumnDecode`). -/
def TotalColumnOnesLeLevel (m n i : Nat) (c : MonotoneColumnSums m n) : Prop :=
  totalColumnOnes c ≤ n * i

private theorem le_mul_div_add (a b : Nat) (hb : 0 < b) :
    a ≤ (a + b - 1) / b * b := by
  set q := (a + b - 1) / b
  set r := (a + b - 1) % b
  have hdiv : q * b + r = a + b - 1 := by
    simpa [q, r, Nat.mul_comm] using Nat.div_add_mod (a + b - 1) b
  have hr : r ≤ b - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ hb)
  omega

private theorem div_add_le_of_le_mul (a b c : Nat) (hb : 0 < b) (h : a ≤ b * c) :
    (a + b - 1) / b ≤ c := by
  by_contra hnot
  push_neg at hnot
  have hc : c + 1 ≤ (a + b - 1) / b := Nat.succ_le_iff.mpr hnot
  have hge : (a + b - 1) / b * b ≤ a + b - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (a + b - 1) b
  have hmul : (c + 1) * b ≤ (a + b - 1) / b * b := by
    gcongr
  have hbound : (c + 1) * b ≤ a + b - 1 := hmul.trans hge
  have hcap : a + b - 1 ≤ b * c + (b - 1) := by omega
  have hle : (c + 1) * b ≤ b * c + (b - 1) := hbound.trans hcap
  have hbpos : 0 < b := hb
  have : b ≤ b - 1 := by
    have hsplit : (c + 1) * b = b * c + b := by ring_nf
    omega
  exact lt_irrefl b (lt_of_le_of_lt this (Nat.sub_lt hbpos (Nat.zero_lt_one)))

/-- Smallest level `i` with `totalColumnOnes c ≤ n·i` (`⌈totalColumnOnes c / n⌉`, or `0` if empty). -/
def matrixOnesLevel {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n) : Nat :=
  (totalColumnOnes c + n - 1) / n

theorem totalColumnOnes_le_mul_matrixOnesLevel {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) :
    totalColumnOnes c ≤ n * matrixOnesLevel hn c := by
  unfold matrixOnesLevel
  rw [Nat.mul_comm]
  exact le_mul_div_add (totalColumnOnes c) n hn

theorem matrixOnesLevel_le_of_totalColumnOnesLeLevel {m n i : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (h : TotalColumnOnesLeLevel m n i c) :
    matrixOnesLevel hn c ≤ i := by
  unfold matrixOnesLevel TotalColumnOnesLeLevel at *
  exact div_add_le_of_le_mul (totalColumnOnes c) n i hn h

theorem matrixOnesLevel_le_m {m n : Nat} (hn : 0 < n) (c : MonotoneColumnSums m n)
    (h : totalColumnOnes c ≤ m * n) : matrixOnesLevel hn c ≤ m :=
  matrixOnesLevel_le_of_totalColumnOnesLeLevel hn c (by
    dsimp [TotalColumnOnesLeLevel]
    simpa [Nat.mul_comm] using h)




theorem AvgRowOnesLeOne.sum_div_le_one {m n : Nat} (h : AvgRowOnesLeOne m n)
    (c : MonotoneColumnSums m n) :
    (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n ≤ (1 : ℝ) := by
  rw [← avgRowOnes_eq c]
  exact h c

def scrambledRowOnes {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (r : Fin m) : Finset (Fin n) :=
  (monotoneRowOnes c r).image (σ r)

def onesInColumns {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (S : Finset (Fin n)) : Nat :=
  ∑ r : Fin m, ((scrambledRowOnes c σ r) ∩ S).card

def scrambledColSum {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (j : Fin n) : Nat :=
  ∑ r : Fin m, if j ∈ scrambledRowOnes c σ r then 1 else 0

/-- Columns whose scrambled sum is at least `i` (Lemma 6.1 excess set). -/
def excessColumnSet {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) : Finset (Fin n) :=
  Finset.univ.filter fun j => i ≤ scrambledColSum c σ j

theorem mem_excessColumnSet {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (j : Fin n) :
    j ∈ excessColumnSet c σ i ↔ i ≤ scrambledColSum c σ j := by
  simp [excessColumnSet, Finset.mem_filter]

def onesAboveBottom {m n : Nat} (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) : Nat :=
  ∑ j : Fin n, (scrambledColSum c σ j - i)


def HasCombinatorialPropertyB {m n : Nat} (σ : Scramble m n) (epsB : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (i : Nat), 1 ≤ i → i ≤ m →
    (onesAboveBottom c σ i : ℝ) < (epsB / 2) * (m * n)

/-- Property B on the true pipeline matrix class (Chvátal §6 / 0–1 principle mass `≤ n·i`).
    Sufficient for sort–scramble–sort decode; strictly weaker than `HasCombinatorialPropertyB`. -/
def HasCombinatorialPropertyBOnPipeline {m n : Nat} (σ : Scramble m n) (epsB : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (i : Nat),
    TotalColumnOnesLeLevel m n i c → 1 ≤ i → i ≤ m →
      (onesAboveBottom c σ i : ℝ) < (epsB / 2) * (m * n)






theorem combinatorialPropertyB_pipeline_failWitness {m n : Nat}
    (σ : Scramble m n) (epsB : ℝ) (hnot : ¬ HasCombinatorialPropertyBOnPipeline σ epsB) :
    ∃ (c : MonotoneColumnSums m n) (i : Nat),
      TotalColumnOnesLeLevel m n i c ∧ 1 ≤ i ∧ i ≤ m ∧
        (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ) := by
  classical
  by_contra hall
  push_neg at hall
  have hB : HasCombinatorialPropertyBOnPipeline σ epsB := by
    intro c i hclass hi1 him
    exact hall c i hclass hi1 him
  exact hnot hB

/-- Legacy nested-level union (overcounts by `m`; kept for numerics comparisons). -/
noncomputable def lemma61_failFactor_pipeline (m n : Nat) : ℝ :=
  (m : ℝ) * lemma61_failFactor m n

/-- Fail-fraction bound for pipeline-class Property B (each monotone matrix counted once at
    its minimal mass level `matrixOnesLevel`). -/
structure Lemma61FailBoundOnPipeline (m n : Nat) (epsB : ℝ) : Prop where
  bound :
    ∀ (bad : Finset (Scramble m n)),
      (∀ σ ∈ bad, ¬ HasCombinatorialPropertyBOnPipeline σ epsB) →
        (bad.card : ℝ) ≤
          lemma61_failFactor m n * (Fintype.card (Scramble m n) : ℝ)



/-! **Algebra** -/

theorem lemma61_t_sq_identity (epsB : ℝ) (m n s : Nat) (hs : 0 < s) :
    2 * ((epsB / 2) * ((n : ℝ) / s)) ^ 2 * (m : ℝ) * s =
      (epsB ^ 2 * m / 2) * ((n : ℝ) ^ 2 / s) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  field_simp [hspos.ne']

theorem lemma61_exp_bound
    (m n s : Nat) (epsB : ℝ)
    (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hsn : s ≤ n) (hn : 1 ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    Real.exp (-(2 * ((epsB / 2) * ((n : ℝ) / s)) ^ 2 * m * s)) ≤
      (Real.exp 1 * m) ^ (-(n : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hm)
  have hspos : (0 : ℝ) < s := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hs1)
  have hlog0 : (0 : ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hinside_nn : (0 : ℝ) ≤ 2 * (1 + Real.log m) / m := by positivity
  have heps2 : 2 * (1 + Real.log m) / m ≤ epsB ^ 2 := by
    have hx := Real.sqrt_nonneg (2 * (1 + Real.log m) / m)
    have := mul_self_le_mul_self hx heps
    rwa [Real.mul_self_sqrt hinside_nn, ← pow_two] at this
  have hid := lemma61_t_sq_identity epsB m n s (by omega : 0 < s)
  have hrate : 1 + Real.log m ≤ epsB ^ 2 * m / 2 := by
    have := mul_le_mul_of_nonneg_left heps2 (le_of_lt hmpos)
    have h1 : (m : ℝ) * (2 * (1 + Real.log m) / m) = 2 * (1 + Real.log m) := by
      field_simp [hmpos.ne']
    linarith
  have hn2s : (n : ℝ) ≤ (n : ℝ) ^ 2 / s := by
    have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
    refine (le_div_iff₀ hspos).mpr ?_
    nlinarith
  have hlog1 : (0 : ℝ) ≤ 1 + Real.log m := by linarith
  have hcoeff :
      (1 + Real.log m) * n ≤ (epsB ^ 2 * m / 2) * ((n : ℝ) ^ 2 / s) := by
    have h := mul_le_mul_of_nonneg_left hn2s hlog1
    exact h.trans (mul_le_mul_of_nonneg_right hrate (by positivity))
  have hexp_le :
      Real.exp (-(2 * ((epsB / 2) * ((n : ℝ) / s)) ^ 2 * m * s)) ≤
        Real.exp (-((1 + Real.log m) * n)) := by
    rw [hid]
    exact Real.exp_le_exp.mpr (neg_le_neg hcoeff)
  have hrewrite :
      Real.exp (-((1 + Real.log m) * n)) = (Real.exp 1 * m) ^ (-(n : ℝ)) := by
    have hlogem : Real.log (Real.exp 1 * m) = 1 + Real.log m := by
      rw [Real.log_mul (Real.exp_pos _).ne' hmpos.ne', Real.log_exp]
    calc Real.exp (-((1 + Real.log m) * n))
        = Real.exp (-(n : ℝ) * Real.log (Real.exp 1 * m)) := by
            rw [← hlogem]; ring_nf
      _ = (Real.exp 1 * m) ^ (-(n : ℝ)) := by
            rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  exact hexp_le.trans_eq hrewrite


theorem lemma61_union_eq_failFactor (m n : Nat) (hm : 0 < m) :
    ((m + 1 : ℝ) ^ n) * ((2 / (Real.exp 1 * m)) ^ n) =
      lemma61_failFactor m n := by
  unfold lemma61_failFactor
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← mul_pow]
  congr 1
  field_simp [hmpos.ne']

/-! **Ones-above-bottom witness** -/

theorem onesInColumns_eq_sum_colSums {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    onesInColumns c σ S = ∑ j ∈ S, scrambledColSum c σ j := by
  classical
  simp only [onesInColumns, scrambledColSum]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun r => ?_
  have h1 :
      ((scrambledRowOnes c σ r) ∩ S).card =
        ∑ j ∈ S, if j ∈ scrambledRowOnes c σ r then 1 else 0 := by
    simp [Finset.inter_comm]
  exact h1

theorem onesAboveBottom_eq_sum_excess {m n : Nat}
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    onesAboveBottom c σ i =
      ∑ j ∈ excessColumnSet c σ i, (scrambledColSum c σ j - i) := by
  classical
  set S := excessColumnSet c σ i
  unfold onesAboveBottom
  refine Eq.symm (Finset.sum_subset_zero_on_sdiff (Finset.subset_univ S)
    (fun j hj => ?_) (fun _ _ => rfl))
  have : scrambledColSum c σ j < i := by
    have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
    simpa [S, mem_excessColumnSet, not_le] using hjS
  exact Nat.sub_eq_zero_of_le (le_of_lt this)

theorem lemma61_excess_columns {m n : Nat} (epsB : ℝ)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat)
    (hge : (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ)) :
    (i * (excessColumnSet c σ i).card : ℝ) + (epsB / 2) * (m * n) ≤
      (onesInColumns c σ (excessColumnSet c σ i) : ℝ) := by
  classical
  let S := excessColumnSet c σ i
  refine ?_
  have hpt : ∀ j ∈ S, i ≤ scrambledColSum c σ j := by
    intro j hj; simpa [S, mem_excessColumnSet] using hj
  have habove := onesAboveBottom_eq_sum_excess c σ i
  have hdecomp :
      ∑ j ∈ S, scrambledColSum c σ j =
        onesAboveBottom c σ i + i * S.card := by
    calc ∑ j ∈ S, scrambledColSum c σ j
        = ∑ j ∈ S, ((scrambledColSum c σ j - i) + i) := by
            refine Finset.sum_congr rfl fun j hj =>
              (Nat.sub_add_cancel (hpt j hj)).symm
      _ = ∑ j ∈ S, (scrambledColSum c σ j - i) + ∑ j ∈ S, i :=
            Finset.sum_add_distrib
      _ = onesAboveBottom c σ i + i * S.card := by
            simpa [Finset.sum_const, mul_comm] using congrArg
              (fun t => t + i * S.card) habove.symm
  have hones : onesInColumns c σ S = onesAboveBottom c σ i + i * S.card := by
    rw [onesInColumns_eq_sum_colSums, hdecomp]
  calc (i * S.card : ℝ) + (epsB / 2) * (m * n)
      ≤ (i * S.card : ℝ) + (onesAboveBottom c σ i : ℝ) := by linarith
    _ = (onesAboveBottom c σ i + i * S.card : ℝ) := by ring
    _ = (onesInColumns c σ S : ℝ) := by exact_mod_cast hones.symm

/-! **Residuals and existence glue** -/

/-- Paper Lemma 6.3 + (6.1), combinatorial form.
  `p` is the ones-density of the monotone matrix; the threshold is `(p+t)*m*|S|`. -/
structure Lemma63ExpBound (m n : Nat) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (t : ℝ),
      0 < t →
      ∀ (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad,
          (((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n) + t) *
              m * S.card ≤
            (onesInColumns c σ S : ℝ))) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * m * S.card)) *
              (Fintype.card (Scramble m n) : ℝ)

/-- Global fail-fraction bound at the end of Lemma 6.1. -/
structure Lemma61FailBound (m n : Nat) (epsB : ℝ) : Prop where
  bound :
    ∀ (bad : Finset (Scramble m n)),
      (∀ σ ∈ bad, ¬ HasCombinatorialPropertyB σ epsB) →
        (bad.card : ℝ) ≤
          lemma61_failFactor m n * (Fintype.card (Scramble m n) : ℝ)


  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB


/-! **AvgRowOnesLeOne is false at paper minima** -/

/-- Every column at full height: each row has all `n` ones, so average row ones equals `m`. -/
def maxColumnMonotone (m n : Nat) : MonotoneColumnSums m n :=
  fun _ => Fin.last m



theorem totalColumnOnes_maxColumn (m n : Nat) :
    totalColumnOnes (maxColumnMonotone m n) = m * n := by
  classical
  unfold totalColumnOnes maxColumnMonotone
  have hcols : ∀ _j : Fin n, (Fin.last m).val = m := fun _ => Fin.val_last m
  calc ∑ j : Fin n, (Fin.last m).val
      = ∑ _j : Fin n, m := Finset.sum_congr rfl fun j _ => hcols j
    _ = m * n := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

theorem not_TotalColumnOnesLeN_of_m_gt_one {m n : Nat} (hm : 1 < m) (hn : 0 < n) :
    ¬ TotalColumnOnesLeN m n := by
  intro h
  have hle := h (maxColumnMonotone m n)
  have heq := totalColumnOnes_maxColumn m n
  have hmn : n < m * n := by nlinarith
  omega



theorem not_AvgRowOnesLeOne_of_m_gt_one {m n : Nat} (hm : 1 < m) (hn : 0 < n) :
    ¬ AvgRowOnesLeOne m n := by
  intro h
  exact not_TotalColumnOnesLeN_of_m_gt_one hm hn (TotalColumnOnesLeN.of_avgRowOnesLeOne hn h)


end Chvatal
