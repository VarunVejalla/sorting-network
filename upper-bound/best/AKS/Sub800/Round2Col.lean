import AKS.Sub800.Ville
import AKS.Sub800.RowMgf
import AKS.Sub800.LayerCake
import AKS.Sub800.NegAssoc
import Mathlib.Tactic

/-! # Round 2, one column: the dual variable as two Ville walks (ROUND2.md §3)

On row subsets `ω : Fin m → Finset (Fin n)` (row `r` = the input columns that the scramble
sends into `S`), the column walk is `W(h) = #{r ≥ m-h : j ∈ ω r} - p h`. Fix a base row `b ≤ m`.
Complementing the rows `r ≥ m - b` (`unflip`), the excess over the cone around `b` splits into
* a forward walk over the rows `m-b-1, …, 0` (increments `[j ∈ ζ] - p - λ`), which becomes an
  increasing walk after `Fin.rev`, and
* a backward walk over the rows `m-b, …, m-1` (increments `[j ∈ ζ] - (1-p) - λ`). -/

open Finset BigOperators

namespace Round2Col

variable {m n : ℕ}

def Nω (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) : ℕ :=
  (Finset.univ.filter fun r : Fin m => m - h ≤ r.val ∧ j ∈ ω r).card

noncomputable def Wω (p : ℝ) (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) : ℝ :=
  (Nω ω j h : ℝ) - p * h

noncomputable def Yω (p lam : ℝ) (ω : Fin m → Finset (Fin n)) (j : Fin n) (b : ℕ) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h =>
    Wω p ω j h - Wω p ω j b - lam * |(h : ℝ) - b|

/-- The column's bit in a row subset. -/
def bit (j : Fin n) (T : Finset (Fin n)) : ℝ := if j ∈ T then 1 else 0

/-- Complement the rows `r ≥ m - b`. -/
def unflip (b : ℕ) (ζ : Fin m → Finset (Fin n)) : Fin m → Finset (Fin n) :=
  fun r => if r.val < m - b then ζ r else Finset.univ \ ζ r

noncomputable def Dfwd (p lam : ℝ) (j : Fin n) (b : ℕ) : Fin m → Finset (Fin n) → ℝ :=
  fun r' T => if b ≤ r'.val then bit j T - p - lam else 0

noncomputable def Dbwd (p lam : ℝ) (j : Fin n) (b : ℕ) : Fin m → Finset (Fin n) → ℝ :=
  fun r T => if m - b ≤ r.val then bit j T - (1 - p) - lam else 0

noncomputable def Yplus (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h =>
    Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h

noncomputable def Yminus (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) : ℝ :=
  (Finset.range (m + 1)).sup' ⟨0, by simp⟩ fun h => Ville.prefixSum (Dbwd p lam j b) ζ h

theorem Nω_eq_sum (ω : Fin m → Finset (Fin n)) (j : Fin n) (h : ℕ) :
    (Nω ω j h : ℝ) = ∑ r : Fin m, if m - h ≤ r.val then bit j (ω r) else 0 := by
  classical
  simp only [Nω, bit]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h1 : m - h ≤ r.val <;> by_cases h2 : j ∈ ω r <;> simp [h1, h2]

theorem card_rows_between (a c : ℕ) (hc : c ≤ m) :
    ((c - a : ℕ) : ℝ) = ∑ r : Fin m, if a ≤ r.val ∧ r.val < c then (1 : ℝ) else 0 := by
  classical
  rw [Finset.sum_boole]
  congr 1
  rw [show c - a = (Finset.Ico a c).card by rw [Nat.card_Ico]]
  symm
  refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    exact Finset.mem_Ico.2 hr
  · intro a _ b _ hab; exact Fin.ext hab
  · intro x hx
    rw [Finset.mem_Ico] at hx
    exact ⟨⟨x, by omega⟩, by simp [hx.1, hx.2], rfl⟩

/-- Forward identity, `b ≤ h ≤ m`. -/
theorem fwd_identity (p lam : ℝ) (j : Fin n) (b h : ℕ) (hbh : b ≤ h) (hh : h ≤ m)
    (ζ : Fin m → Finset (Fin n)) :
    Wω p (unflip b ζ) j h - Wω p (unflip b ζ) j b - lam * |(h : ℝ) - b| =
      Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h := by
  classical
  have hcnt := card_rows_between (m := m) (m - h) (m - b) (by omega)
  have hhb : ((m - b - (m - h) : ℕ) : ℝ) = (h : ℝ) - b := by
    rw [show m - b - (m - h) = h - b by omega]; push_cast [Nat.cast_sub hbh]; ring
  rw [hhb] at hcnt
  have habs : |(h : ℝ) - b| = (h : ℝ) - b := abs_of_nonneg (by
    have : (b : ℝ) ≤ h := by exact_mod_cast hbh
    linarith)
  simp only [Wω, Nω_eq_sum, habs]
  -- left side as one sum over rows in [m-h, m-b)
  have hL : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
      p * h - ((∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) - p * b) -
      lam * ((h : ℝ) - b) =
      ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) - p - lam else 0 := by
    have e1 : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
        (∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) =
        ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases h1 : m - h ≤ r.val <;> by_cases h2 : m - b ≤ r.val
      · have : ¬ r.val < m - b := by omega
        simp [h1, h2, this]
      · have h3 : r.val < m - b := by omega
        simp [h1, h2, h3, unflip]
      · omega
      · simp [h1, h2]
    have e2 : p * h - p * b + lam * ((h : ℝ) - b) =
        ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0 := by
      rw [show (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0) =
          (p + lam) * ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then (1 : ℝ) else 0 by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> ring]
      rw [← hcnt]; ring
    have e3 : (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) - p - lam else 0) =
        (∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then bit j (ζ r) else 0) -
          ∑ r : Fin m, if m - h ≤ r.val ∧ r.val < m - b then p + lam else 0 := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> ring
    rw [e3, ← e1, ← e2]; ring
  rw [hL]
  -- right side: reindex by `Fin.rev`
  simp only [Ville.prefixSum, Dfwd]
  refine (Fintype.sum_equiv Fin.revPerm _ _ fun r' => ?_).symm
  simp only [Fin.revPerm_apply, Fin.val_rev, Fin.rev_rev]
  have hr := r'.isLt
  split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; omega)

theorem bit_compl (j : Fin n) (T : Finset (Fin n)) : bit j (Finset.univ \ T) = 1 - bit j T := by
  classical
  by_cases h : j ∈ T <;> simp [bit, h]

/-- Backward identity, `h ≤ b ≤ m`. -/
theorem bwd_identity (p lam : ℝ) (j : Fin n) (b h : ℕ) (hhb : h ≤ b) (hb : b ≤ m)
    (ζ : Fin m → Finset (Fin n)) :
    Wω p (unflip b ζ) j h - Wω p (unflip b ζ) j b - lam * |(h : ℝ) - b| =
      Ville.prefixSum (Dbwd p lam j b) ζ (m - h) := by
  classical
  have hcnt := card_rows_between (m := m) (m - b) (m - h) (by omega)
  have hbh : ((m - h - (m - b) : ℕ) : ℝ) = (b : ℝ) - h := by
    rw [show m - h - (m - b) = b - h by omega]; push_cast [Nat.cast_sub hhb]; ring
  rw [hbh] at hcnt
  have habs : |(h : ℝ) - b| = (b : ℝ) - h := by
    rw [abs_sub_comm]
    exact abs_of_nonneg (by
      have : (h : ℝ) ≤ b := by exact_mod_cast hhb
      linarith)
  simp only [Wω, Nω_eq_sum, habs]
  have e1 : (∑ r : Fin m, if m - h ≤ r.val then bit j (unflip b ζ r) else 0) -
      (∑ r : Fin m, if m - b ≤ r.val then bit j (unflip b ζ r) else 0) =
      ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - 1 else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : m - h ≤ r.val <;> by_cases h2 : m - b ≤ r.val
    · have : ¬ r.val < m - h := by omega
      simp [h1, h2, this]
    · omega
    · have h3 : r.val < m - h := by omega
      have h4 : ¬ r.val < m - b := by omega
      simp only [h1, h2, h3, if_true, if_false, and_self, unflip, h4, bit_compl]
      ring
    · simp [h1, h2]
  have e2 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then (1 - p) + lam else 0) =
      ((1 - p) + lam) * ((b : ℝ) - h) := by
    rw [hcnt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have e3 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - 1 else 0) =
      (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - (1 - p) - lam else 0) +
        ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then -p + lam else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have e4 : (∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then -p + lam else 0) =
      (-p + lam) * ((b : ℝ) - h) := by
    rw [hcnt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  have hR : Ville.prefixSum (Dbwd p lam j b) ζ (m - h) =
      ∑ r : Fin m, if m - b ≤ r.val ∧ r.val < m - h then bit j (ζ r) - (1 - p) - lam else 0 := by
    simp only [Ville.prefixSum, Dbwd]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h1 : r.val < m - h <;> by_cases h2 : m - b ≤ r.val <;> simp [h1, h2]
  rw [hR]
  have := e1
  rw [e3, e4] at this
  linarith

theorem Yplus_nonneg (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    0 ≤ Yplus p lam j b ζ := by
  have := Finset.le_sup' (s := Finset.range (m + 1))
    (f := fun h => Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h)
    (Finset.mem_range.2 (Nat.succ_pos m))
  simpa [Yplus, Ville.prefixSum_zero] using this

theorem Yminus_nonneg (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) :
    0 ≤ Yminus p lam j b ζ := by
  have := Finset.le_sup' (s := Finset.range (m + 1))
    (f := fun h => Ville.prefixSum (Dbwd p lam j b) ζ h) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa [Yminus, Ville.prefixSum_zero] using this

/-- The dual variable is at most the larger of the two walk maxima. -/
theorem Yω_le_max (p lam : ℝ) (j : Fin n) (b : ℕ) (hb : b ≤ m) (ζ : Fin m → Finset (Fin n)) :
    Yω p lam (unflip b ζ) j b ≤ max (Yplus p lam j b ζ) (Yminus p lam j b ζ) := by
  apply Finset.sup'_le
  intro h hh
  rw [Finset.mem_range] at hh
  by_cases hbh : b ≤ h
  · rw [fwd_identity p lam j b h hbh (by omega) ζ]
    refine le_trans ?_ (le_max_left _ _)
    exact Finset.le_sup' (f := fun h => Ville.prefixSum (Dfwd p lam j b) (fun r => ζ (Fin.rev r)) h)
      (Finset.mem_range.2 hh)
  · push_neg at hbh
    rw [bwd_identity p lam j b h hbh.le hb ζ]
    refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup' (f := fun h => Ville.prefixSum (Dbwd p lam j b) ζ h)
      (Finset.mem_range.2 (by omega))

/-! ## Moments of one column on the flipped sample -/

/-- Row sizes of the flipped sample: `s` on the forward rows, `n - s` on the backward rows. -/
def kflip (m b s n : ℕ) : Fin m → ℕ := fun r => if r.val < m - b then s else n - s

theorem exp_max_le (t a c : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Real.exp (t * max a c) ≤ Real.exp (t * a) + Real.exp (t * c) - 1 := by
  rcases le_total a c with h | h
  · rw [max_eq_right h]
    have : 1 ≤ Real.exp (t * a) := Real.one_le_exp (by positivity)
    linarith
  · rw [max_eq_left h]
    have : 1 ≤ Real.exp (t * c) := Real.one_le_exp (by positivity)
    linarith

/-- The row condition of Ville's inequality for one column bit under a uniform `k`-subset:
`E e^{θ([j ∈ T] - q - λ)} ≤ 1` when `q = k/n` and `1 - q + q e^θ ≤ e^{θ(q+λ)}`. -/
theorem row_condition (n k : ℕ) (hn : 0 < n) (j : Fin n) (θ lam : ℝ)
    (hθ : 1 - (k : ℝ) / n + (k : ℝ) / n * Real.exp θ ≤ Real.exp (θ * ((k : ℝ) / n + lam))) :
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        Real.exp (θ * (bit j T - (k : ℝ) / n - lam)) ≤
      (((Finset.univ : Finset (Fin n)).powersetCard k).card : ℝ) := by
  classical
  have hb : ∀ T : Finset (Fin n), bit j T = if decide (j ∈ T) then 1 else 0 := fun T => by
    by_cases h : j ∈ T <;> simp [bit, h]
  simp_rw [hb]
  have := RowMgf.sum_bit n k j hn (fun β => Real.exp (θ * ((if β then 1 else 0) - (k : ℝ) / n - lam)))
  simp only at this
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hC : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  set q := (k : ℝ) / n
  have key : (1 - q) * Real.exp (θ * (0 - q - lam)) + q * Real.exp (θ * (1 - q - lam)) ≤ 1 := by
    have e1 : Real.exp (θ * (0 - q - lam)) = Real.exp θ ^ 0 * Real.exp (-(θ * (q + lam))) := by
      rw [pow_zero, one_mul]; congr 1; ring
    have e2 : Real.exp (θ * (1 - q - lam)) = Real.exp θ * Real.exp (-(θ * (q + lam))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e1, e2, pow_zero, one_mul]
    have hpos : 0 < Real.exp (θ * (q + lam)) := Real.exp_pos _
    have hinv : Real.exp (-(θ * (q + lam))) = (Real.exp (θ * (q + lam)))⁻¹ := Real.exp_neg _
    rw [hinv]
    rw [show (1 - q) * (Real.exp (θ * (q + lam)))⁻¹ + q * (Real.exp θ * (Real.exp (θ * (q + lam)))⁻¹) =
      (1 - q + q * Real.exp θ) / Real.exp (θ * (q + lam)) by field_simp]
    rw [div_le_one hpos]
    exact hθ
  calc (n.choose k : ℝ) * ((1 - q) * Real.exp (θ * ((if false = true then 1 else 0) - q - lam)) +
        q * Real.exp (θ * ((if true = true then 1 else 0) - q - lam)))
      = (n.choose k : ℝ) * ((1 - q) * Real.exp (θ * (0 - q - lam)) +
        q * Real.exp (θ * (1 - q - lam))) := by simp
    _ ≤ (n.choose k : ℝ) * 1 := mul_le_mul_of_nonneg_left key hC
    _ = _ := mul_one _

theorem Yminus_ge_iff (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) (x : ℝ) :
    x ≤ Yminus p lam j b ζ ↔ Ville.Reaches (Dbwd p lam j b) x ζ := by
  unfold Yminus Ville.Reaches
  rw [Finset.le_sup'_iff]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

theorem Yplus_ge_iff (p lam : ℝ) (j : Fin n) (b : ℕ) (ζ : Fin m → Finset (Fin n)) (x : ℝ) :
    x ≤ Yplus p lam j b ζ ↔ Ville.Reaches (Dfwd p lam j b) x (fun r => ζ (Fin.rev r)) := by
  unfold Yplus Ville.Reaches
  rw [Finset.le_sup'_iff]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- The flipped sample. -/
def Zs (m b s n : ℕ) : Finset (Fin m → Finset (Fin n)) :=
  Fintype.piFinset fun r => (Finset.univ : Finset (Fin n)).powersetCard (kflip m b s n r)

/-- Its row reversal. -/
def Zrev (m b s n : ℕ) : Finset (Fin m → Finset (Fin n)) :=
  Fintype.piFinset fun r => (Finset.univ : Finset (Fin n)).powersetCard (kflip m b s n (Fin.rev r))

theorem card_filter_rev (b s : ℕ) (P : (Fin m → Finset (Fin n)) → Prop) [DecidablePred P] :
    ((Zs m b s n).filter fun ζ => P (fun r => ζ (Fin.rev r))).card =
      ((Zrev m b s n).filter P).card := by
  refine Finset.card_bij (fun ζ _ => fun r => ζ (Fin.rev r)) ?_ ?_ ?_
  · intro ζ hζ
    rw [Finset.mem_filter] at hζ ⊢
    refine ⟨?_, hζ.2⟩
    rw [Zrev, Fintype.mem_piFinset]
    intro r
    rw [Zs, Fintype.mem_piFinset] at hζ
    exact hζ.1 (Fin.rev r)
  · intro a _ c _ h
    funext r
    have := congrFun h (Fin.rev r)
    simpa using this
  · intro ζ' hζ'
    refine ⟨fun r => ζ' (Fin.rev r), ?_, by funext r; simp⟩
    rw [Finset.mem_filter] at hζ' ⊢
    refine ⟨?_, by simpa using hζ'.2⟩
    rw [Zs, Fintype.mem_piFinset]
    intro r
    rw [Zrev, Fintype.mem_piFinset] at hζ'
    simpa using hζ'.1 (Fin.rev r)

theorem card_Zrev (b s : ℕ) : (Zrev m b s n).card = (Zs m b s n).card := by
  classical
  have h := card_filter_rev (m := m) (n := n) b s (fun _ => True)
  simpa using h.symm

theorem cast_sub_div (n s : ℕ) (hs : s ≤ n) (hn : 0 < n) :
    ((n - s : ℕ) : ℝ) / n = 1 - (s : ℝ) / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_sub hs]; field_simp

/-- Ville tail of the backward walk on the flipped sample. -/
theorem tail_minus (b s : ℕ) (hs : s ≤ n) (hn : 0 < n) (j : Fin n) (lam β : ℝ) (hβ0 : 0 ≤ β)
    (hβ : 1 - (1 - (s : ℝ) / n) + (1 - (s : ℝ) / n) * Real.exp β ≤
      Real.exp (β * ((1 - (s : ℝ) / n) + lam))) (x : ℝ) :
    (((Zs m b s n).filter fun ζ => x ≤ Yminus ((s : ℝ) / n) lam j b ζ).card : ℝ) ≤
      Real.exp (-(β * x)) * ((Zs m b s n).card : ℝ) := by
  classical
  have hfil : (Zs m b s n).filter (fun ζ => x ≤ Yminus ((s : ℝ) / n) lam j b ζ) =
      (Zs m b s n).filter (Ville.Reaches (Dbwd ((s : ℝ) / n) lam j b) x) := by
    ext ζ; simp only [Finset.mem_filter, Yminus_ge_iff]
  rw [hfil]
  refine Ville.ville β hβ0 m _ _ (fun r => ?_) x
  by_cases hr : m - b ≤ r.val
  · have hk : kflip m b s n r = n - s := by simp [kflip]; omega
    simp only [Dbwd, if_pos hr, hk]
    have hq := cast_sub_div n s hs hn
    have := row_condition n (n - s) hn j β lam (by rw [hq]; exact hβ)
    rw [hq] at this
    convert this using 3
  · simp only [Dbwd, if_neg hr, mul_zero, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact le_rfl

/-- Ville tail of the forward walk on the flipped sample. -/
theorem tail_plus (b s : ℕ) (hb : b ≤ m) (hn : 0 < n) (j : Fin n) (lam α : ℝ) (hα0 : 0 ≤ α)
    (hα : 1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp α ≤ Real.exp (α * ((s : ℝ) / n + lam)))
    (x : ℝ) :
    (((Zs m b s n).filter fun ζ => x ≤ Yplus ((s : ℝ) / n) lam j b ζ).card : ℝ) ≤
      Real.exp (-(α * x)) * ((Zs m b s n).card : ℝ) := by
  classical
  have hfil : (Zs m b s n).filter (fun ζ => x ≤ Yplus ((s : ℝ) / n) lam j b ζ) =
      (Zs m b s n).filter (fun ζ => Ville.Reaches (Dfwd ((s : ℝ) / n) lam j b) x
        (fun r => ζ (Fin.rev r))) := by
    ext ζ; simp only [Finset.mem_filter, Yplus_ge_iff]
  have hc : ((Zs m b s n).filter (fun ζ => Ville.Reaches (Dfwd ((s : ℝ) / n) lam j b) x
      (fun r => ζ (Fin.rev r)))).card =
      ((Zrev m b s n).filter (Ville.Reaches (Dfwd ((s : ℝ) / n) lam j b) x)).card := by
    convert card_filter_rev (m := m) (n := n) b s (Ville.Reaches (Dfwd ((s : ℝ) / n) lam j b) x)
  rw [hfil, hc, ← card_Zrev]
  refine Ville.ville α hα0 m _ _ (fun r => ?_) x
  by_cases hr : b ≤ r.val
  · have hk : kflip m b s n (Fin.rev r) = s := by
      simp only [kflip, Fin.val_rev]
      rw [if_pos (by omega)]
    simp only [Dfwd, if_pos hr, hk]
    exact row_condition n s hn j α lam hα
  · simp only [Dfwd, if_neg hr, mul_zero, Real.exp_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact le_rfl

/-- The layer-cake constant with `C = 1`, `k₀ = 0`. -/
noncomputable def Lb (t θ δ : ℝ) : ℝ :=
  Real.exp (t * δ) * (1 + (1 - Real.exp (-(t * δ))) / (1 - Real.exp ((t - θ) * δ)))

theorem mgf_of_tail {Ω : Type*} (Z : Finset Ω) (Y : Ω → ℝ) (hY : ∀ ω ∈ Z, 0 ≤ Y ω)
    (t θ δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htθ : t < θ)
    (htail : ∀ x : ℝ, ((Z.filter fun ω => x ≤ Y ω).card : ℝ) ≤ Real.exp (-(θ * x)) * (Z.card : ℝ)) :
    ∑ ω ∈ Z, Real.exp (t * Y ω) ≤ (Z.card : ℝ) * Lb t θ δ := by
  have := LayerCake.layer_cake Z Y hY t θ δ 1 ht hδ htθ zero_le_one 0
    (fun k _ => by simpa [one_mul] using htail (k * δ))
  simp only [Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero, pow_zero, one_mul, mul_one] at this
  simpa [Lb, mul_assoc] using this

/-- **One column.** -/
theorem column_mgf (b s : ℕ) (hb : b ≤ m) (hs : s ≤ n) (hn : 0 < n) (j : Fin n)
    (lam t α β δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) (htα : t < α) (htβ : t < β)
    (hα : 1 - (s : ℝ) / n + (s : ℝ) / n * Real.exp α ≤ Real.exp (α * ((s : ℝ) / n + lam)))
    (hβ : 1 - (1 - (s : ℝ) / n) + (1 - (s : ℝ) / n) * Real.exp β ≤
      Real.exp (β * ((1 - (s : ℝ) / n) + lam))) :
    ∑ ζ ∈ Zs m b s n, Real.exp (t * max (Yplus ((s : ℝ) / n) lam j b ζ)
        (Yminus ((s : ℝ) / n) lam j b ζ)) ≤
      ((Zs m b s n).card : ℝ) * (Lb t α δ + Lb t β δ - 1) := by
  have hα0 : 0 ≤ α := by linarith
  have hβ0 : 0 ≤ β := by linarith
  have h1 := mgf_of_tail (Zs m b s n) (Yplus ((s : ℝ) / n) lam j b)
    (fun ζ _ => Yplus_nonneg _ _ _ _ ζ) t α δ ht hδ htα (tail_plus b s hb hn j lam α hα0 hα)
  have h2 := mgf_of_tail (Zs m b s n) (Yminus ((s : ℝ) / n) lam j b)
    (fun ζ _ => Yminus_nonneg _ _ _ _ ζ) t β δ ht hδ htβ (tail_minus b s hs hn j lam β hβ0 hβ)
  calc ∑ ζ ∈ Zs m b s n, Real.exp (t * max (Yplus ((s : ℝ) / n) lam j b ζ)
        (Yminus ((s : ℝ) / n) lam j b ζ))
      ≤ ∑ ζ ∈ Zs m b s n, (Real.exp (t * Yplus ((s : ℝ) / n) lam j b ζ) +
          Real.exp (t * Yminus ((s : ℝ) / n) lam j b ζ) - 1) :=
        Finset.sum_le_sum fun ζ _ => exp_max_le t _ _ ht (Yplus_nonneg _ _ _ _ ζ)
          (Yminus_nonneg _ _ _ _ ζ)
    _ = (∑ ζ ∈ Zs m b s n, Real.exp (t * Yplus ((s : ℝ) / n) lam j b ζ)) +
          (∑ ζ ∈ Zs m b s n, Real.exp (t * Yminus ((s : ℝ) / n) lam j b ζ)) -
          ((Zs m b s n).card : ℝ) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]; simp
    _ ≤ ((Zs m b s n).card : ℝ) * Lb t α δ + ((Zs m b s n).card : ℝ) * Lb t β δ -
          ((Zs m b s n).card : ℝ) := by linarith
    _ = _ := by ring

end Round2Col
