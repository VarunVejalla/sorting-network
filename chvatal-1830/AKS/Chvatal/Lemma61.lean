module

/- Combinatorial `0–1` model for Chvátal's Lemma 6.1 (DCS-TR-294 §6): monotone matrices as column
sums, scrambles, excess columns, and the pipeline Property B. -/

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

instance (m n : Nat) : Nonempty (Scramble m n) := ⟨fun _ => 1⟩

abbrev MonotoneColumnSums (m n : Nat) : Type := Fin n → Fin (m + 1)

def monotoneRowOnes {m n : Nat} (c : MonotoneColumnSums m n) (r : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun j => (m - r.val) ≤ (c j).val

/-- Total ones in the monotone `0–1` model (`∑ⱼ` column height). -/
def totalColumnOnes {m n : Nat} (c : MonotoneColumnSums m n) : Nat := ∑ j : Fin n, (c j).val

theorem totalColumnOnes_eq_sum_rowOnes {m n : Nat} (c : MonotoneColumnSums m n) :
    totalColumnOnes c = ∑ r : Fin m, (monotoneRowOnes c r).card := by
  simp only [totalColumnOnes, monotoneRowOnes, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := (c j).isLt
  rw [Fin.sum_univ_eq_sum_range (fun r => if m - r ≤ (c j).val then 1 else 0) m, ← Finset.card_filter,
    show (Finset.range m).filter (fun r => m - r ≤ (c j).val) = Finset.Ico (m - (c j).val) m by
      ext; simp; omega, Nat.card_Ico]
  omega

def scrambledRowOnes {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (r : Fin m) :
    Finset (Fin n) := (monotoneRowOnes c r).image (σ r)

def onesInColumns {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n)
    (S : Finset (Fin n)) : Nat := ∑ r : Fin m, ((scrambledRowOnes c σ r) ∩ S).card

def scrambledColSum {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Fin n) : Nat :=
  ∑ r : Fin m, if j ∈ scrambledRowOnes c σ r then 1 else 0

/-- Columns whose scrambled sum is at least `i` (Lemma 6.1 excess set). -/
def excessColumnSet {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => i ≤ scrambledColSum c σ j

theorem mem_excessColumnSet {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat)
    (j : Fin n) : j ∈ excessColumnSet c σ i ↔ i ≤ scrambledColSum c σ j := by
  simp [excessColumnSet]

def onesAboveBottom {m n : Nat} (c : MonotoneColumnSums m n) (σ : Scramble m n) (i : Nat) : Nat :=
  ∑ j : Fin n, (scrambledColSum c σ j - i)

/-- Property B on the pipeline matrix class (total mass `≤ n·i` at level `i`). -/
def HasCombinatorialPropertyBOnPipeline {m n : Nat} (σ : Scramble m n) (epsB : ℝ) : Prop :=
  ∀ (c : MonotoneColumnSums m n) (i : Nat), totalColumnOnes c ≤ n * i → 1 ≤ i → i ≤ m →
    (onesAboveBottom c σ i : ℝ) < (epsB / 2) * (m * n)

/-- Fail-fraction bound for pipeline-class Property B. -/
structure Lemma61FailBoundOnPipeline (m n : Nat) (epsB : ℝ) : Prop where
  bound :
    ∀ (bad : Finset (Scramble m n)),
      (∀ σ ∈ bad, ¬ HasCombinatorialPropertyBOnPipeline σ epsB) →
        (bad.card : ℝ) ≤ lemma61_failFactor m n * (Fintype.card (Scramble m n) : ℝ)

theorem lemma61_exp_bound (m n s : Nat) (epsB : ℝ) (hm : 1 ≤ m) (hs1 : 1 ≤ s) (hsn : s ≤ n)
    (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    Real.exp (-(2 * ((epsB / 2) * ((n : ℝ) / s)) ^ 2 * m * s)) ≤
      (Real.exp 1 * m) ^ (-(n : ℝ)) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 hs1
  have hsn' : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have h2 : 2 * (1 + Real.log m) ≤ epsB ^ 2 * m := by
    rw [← div_le_iff₀ hm0]
    have := Real.sq_sqrt (show 0 ≤ 2 * (1 + Real.log m) / m by positivity)
    nlinarith [Real.sqrt_nonneg (2 * (1 + Real.log m) / m)]
  rw [Real.rpow_def_of_pos (by positivity), Real.log_mul (Real.exp_pos 1).ne' hm0.ne',
    Real.log_exp]
  refine Real.exp_le_exp.2 ?_
  have e : 2 * (epsB / 2 * (n / s)) ^ 2 * m * s = epsB ^ 2 * m * n ^ 2 / (2 * s) := by
    field_simp
  rw [e]
  suffices (1 + Real.log m) * n ≤ epsB ^ 2 * m * n ^ 2 / (2 * s) by linarith
  rw [le_div_iff₀ (by positivity)]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsn' (by positivity : 0 ≤ (1 + Real.log m) * n),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg (n : ℝ))]

theorem lemma61_excess_columns {m n : Nat} (epsB : ℝ) (c : MonotoneColumnSums m n)
    (σ : Scramble m n) (i : Nat) (hge : (epsB / 2) * (m * n) ≤ (onesAboveBottom c σ i : ℝ)) :
    (i * (excessColumnSet c σ i).card : ℝ) + (epsB / 2) * (m * n) ≤
      (onesInColumns c σ (excessColumnSet c σ i) : ℝ) := by
  classical
  have h1 : onesInColumns c σ (excessColumnSet c σ i) =
      ∑ j ∈ excessColumnSet c σ i, scrambledColSum c σ j := by
    simp only [onesInColumns, scrambledColSum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  have h2 : onesAboveBottom c σ i =
      ∑ j ∈ excessColumnSet c σ i, (scrambledColSum c σ j - i) := by
    unfold onesAboveBottom excessColumnSet
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> omega
  have h3 : onesInColumns c σ (excessColumnSet c σ i) =
      onesAboveBottom c σ i + i * (excessColumnSet c σ i).card := by
    rw [h1, h2, Finset.sum_congr rfl fun j hj => (Nat.sub_add_cancel
      ((mem_excessColumnSet c σ i j).1 hj)).symm, Finset.sum_add_distrib]
    simp [Finset.sum_const, mul_comm]
  rw [h3]
  push_cast
  linarith

end Chvatal
