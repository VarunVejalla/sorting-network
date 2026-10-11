module

public import AKS.Chvatal.Lemma62Tail
public import AKS.Chvatal.Lemma62TopsCount
public import AKS.Chvatal.Lemma62FailE

/-! # Two-round fringe contract (`F2ROUND.md` §1): parameters and the predicates SR, R1, R2

`F2SmallRank σ1` (SR), `F2R1 σ1` (R1) and `F2R2 σ2` (R2) are the three scramble predicates whose
conjunction gives two-round Property F (`F2Det.F2_of_SR_R1_R2`).  Every predicate is a statement
about `onesInRows c σ (topRows m g) S` for monotone column sums `c` of bounded total/shape, i.e. each
is the complement of a union of `tailBadSet`-type events:

* SR: `¬ SR σ1` ⊆ `⋃ c (total ≤ min J Jmax), tailBadSet c (topRows m g1) 1 (f - g1 + 1)`.
* R1(a): `⋃_{E ≥ 2} ⋃_{c : total ≤ j_E} tailBadSet c (topRows m g1) (κ_E+1) ((Δ+1)(κ_E+1))`.
* R1(b): `⋃_{E ≥ 2} ⋃_{c : total ≤ j_E} ⋃_{1 ≤ s ≤ κ_E} tailBadSet c (topRows m g1) s (Δ s + B_E)`.
* R2:   `⋃_{E ≥ 2} ⋃_{c : #{col | g2 < c col} ≤ κ_E, Σ (c col - g2) < B_E}
          ⋃_{s ≥ 1} tailBadSet c (topRows m g2) s (Φ s + E)`.

(The quantification over `c` is reduced to tops/`y`-vectors exactly as in `badSetF_card_le`, using
`onesInRows_topRows_depends_only_on_top`.)  The numeric parameters are bundled in `F2Params`. -/

@[expose] public section

namespace Chvatal

/-- Numeric parameters of the two-round contract (`F2ROUND.md`).  `D = δ f` with `δ = 128/4095`,
`Δ = g2 - g1`, `Φ = f - g2`; the fields are the preconditions of `f2round/cert.py`. -/
structure F2Params where
  f : ℕ
  g1 : ℕ
  g2 : ℕ
  /-- rank scale `J` (`ε = 1 / J`). -/
  J : ℕ
  c : ℝ
  b : ℝ
  hg1 : 0 < g1
  hg12 : g1 < g2
  hg2f : g2 < f
  hJ : 0 < J
  hc0 : 0 < c
  hb0 : 0 < b
  /-- `c ≤ 1/2` (R2 nonincreasing in `n`). -/
  hc_half : c ≤ 1 / 2
  /-- `Δ + 1 ≥ δ f` (R1 Chernoff validity). -/
  hD1 : (128 / 4095 : ℝ) * f ≤ ((g2 - g1 : ℕ) : ℝ) + 1
  /-- `f - g1 + 1 ≥ δ f` (SR Chernoff validity). -/
  hD2 : (128 / 4095 : ℝ) * f ≤ ((f - g1 : ℕ) : ℝ) + 1
  /-- `(g1 + 1)² ≥ δ f` (tops bound monotone in `k`). -/
  hD3 : (128 / 4095 : ℝ) * f ≤ ((g1 : ℝ) + 1) ^ 2
  /-- `c Δ ≥ J / (g1 + 1)` (R1a decreasing in `n`). -/
  hcΔ : (J : ℝ) / ((g1 : ℝ) + 1) ≤ c * ((g2 - g1 : ℕ) : ℝ)
  /-- `b ≥ J / (g1 + 1)` (R1b decreasing in `n`). -/
  hbJ : (J : ℝ) / ((g1 : ℝ) + 1) ≤ b
  /-- `Φ ≥ 2 b δ f / J` (R2 Chernoff validity). -/
  hΦ : 2 * b * ((128 / 4095 : ℝ) * f) / J ≤ ((f - g2 : ℕ) : ℝ)
  /-- `(c + 1/2)² ≤ b J / (4 δ f)` (`κ² ≤ n (B-1)`; Y-count monotone in `k`). -/
  hκ : (c + 1 / 2) ^ 2 ≤ b * J / (4 * ((128 / 4095 : ℝ) * f))

namespace F2Params

/-- `Δ = g2 - g1`. -/
def Δ (P : F2Params) : ℕ := P.g2 - P.g1

/-- `Φ = f - g2`. -/
def Φ (P : F2Params) : ℕ := P.f - P.g2

/-- `κ_E = ⌈c E⌉`. -/
noncomputable def κ (P : F2Params) (E : ℕ) : ℕ := ⌈P.c * E⌉₊

/-- `B_E = ⌈b E⌉`. -/
noncomputable def B (P : F2Params) (E : ℕ) : ℕ := ⌈P.b * E⌉₊

/-- `Jmax = ⌊δ f n⌋` (largest admissible rank on `n` columns). -/
noncomputable def jmax (P : F2Params) (n : ℕ) : ℕ := ⌊(128 / 4095 : ℝ) * (P.f * n)⌋₊

/-- `j_E = min (E J, Jmax)`. -/
noncomputable def jE (P : F2Params) (n E : ℕ) : ℕ := min (E * P.J) (P.jmax n)

/-- The concrete instance `f = 131040`, `g1 = 2f/5`, `g2 = 4f/5`, `c = 1/3`, `b = 17000`,
`J = 86·10⁶`. -/
noncomputable def std : F2Params where
  f := 131040
  g1 := 52416
  g2 := 104832
  J := 86000000
  c := 1 / 3
  b := 17000
  hg1 := by norm_num
  hg12 := by norm_num
  hg2f := by norm_num
  hJ := by norm_num
  hc0 := by norm_num
  hb0 := by norm_num
  hc_half := by norm_num
  hD1 := by norm_num
  hD2 := by norm_num
  hD3 := by norm_num
  hcΔ := by norm_num
  hbJ := by norm_num
  hΦ := by norm_num
  hκ := by norm_num

theorem B_pos (P : F2Params) {E : ℕ} (hE : 1 ≤ E) : 0 < P.B E :=
  Nat.ceil_pos.mpr (mul_pos P.hb0 (by exact_mod_cast hE))

end F2Params

/-- **SR** (small ranks): for every monotone `c` of total at most `min J Jmax`, every column
receives at most `f - g1` ones of `c` in the rows strictly above the bottom `g1`, after scramble
`σ1`.  Complement: `tailBadSet c (topRows m g1) 1 (f - g1 + 1)`. -/
def F2SmallRank {m n : ℕ} (P : F2Params) (σ1 : Scramble m n) : Prop :=
  ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ min P.J (P.jmax n) →
    ∀ S : Finset (Fin n), S.card = 1 →
      onesInRows c σ1 (topRows m P.g1) S < P.f - P.g1 + 1

/-- **R1(a)** : no `κ_E + 1` columns carry `(Δ + 1)(κ_E + 1)` hits.  Complement:
`tailBadSet c (topRows m g1) (κ_E + 1) ((Δ + 1) (κ_E + 1))`. -/
def F2R1a {m n : ℕ} (P : F2Params) (σ1 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E →
    ∀ S : Finset (Fin n), S.card = P.κ E + 1 →
      onesInRows c σ1 (topRows m P.g1) S < (P.Δ + 1) * (P.κ E + 1)

/-- **R1(b)** : no `s ∈ [1, κ_E]` columns carry `Δ s + B_E` hits.  Complement:
`tailBadSet c (topRows m g1) s (Δ s + B_E)`. -/
def F2R1b {m n : ℕ} (P : F2Params) (σ1 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n, totalColumnOnes c ≤ P.jE n E →
    ∀ S : Finset (Fin n), 1 ≤ S.card → S.card ≤ P.κ E →
      onesInRows c σ1 (topRows m P.g1) S < P.Δ * S.card + P.B E

/-- **R1** = R1(a) ∧ R1(b). -/
def F2R1 {m n : ℕ} (P : F2Params) (σ1 : Scramble m n) : Prop := F2R1a P σ1 ∧ F2R1b P σ1

/-- **R2**: for every monotone `c` whose part above `g2` (the `y`-vector `c - g2`) has support of
size at most `κ_E` and total at most `B_E - 1`, no nonempty column set `S` receives `Φ |S| + E`
ones of `c` in the rows above `g2` after scramble `σ2`.  Complement:
`tailBadSet c (topRows m g2) s (Φ s + E)`.

Note (deviation from `F2ROUND.md` §1): the note writes `onesInRows(y, σ2, all rows, S)`; the
deterministic reduction (D3) uses the rows `ℓ > g2` of `σ2` with heights `g2 + y`, i.e.
`onesInRows c σ2 (topRows m g2) S` with `c = g2 + y`.  The two have the same law for a uniform
`σ2` (rows are i.i.d.), and the `topRows m g2` form is the one that is deterministically needed. -/
def F2R2 {m n : ℕ} (P : F2Params) (σ2 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → ∀ c : MonotoneColumnSums m n,
    (Finset.univ.filter fun col => P.g2 < (c col).val).card ≤ P.κ E →
    ∑ col, ((c col).val - P.g2) < P.B E →
    ∀ S : Finset (Fin n), S.Nonempty →
      onesInRows c σ2 (topRows m P.g2) S < P.Φ * S.card + E

/-- `F2R2` restricted to the ranks `E` with `(E - 1) J ≤ jmax n` (the only ones used by
`F2Det.F2_of_SR_R1_R2`, where `E = ⌈j/J⌉` and `j ≤ jmax n`). -/
def F2R2n {m n : ℕ} (P : F2Params) (σ2 : Scramble m n) : Prop :=
  ∀ E : ℕ, 2 ≤ E → (E - 1) * P.J ≤ P.jmax n → ∀ c : MonotoneColumnSums m n,
    (Finset.univ.filter fun col => P.g2 < (c col).val).card ≤ P.κ E →
    ∑ col, ((c col).val - P.g2) < P.B E →
    ∀ S : Finset (Fin n), S.Nonempty →
      onesInRows c σ2 (topRows m P.g2) S < P.Φ * S.card + E

/-! ## Dependence on the top only -/

/-- The ones in the rows above `g` depend only on the tops `c col - g`
(generalises `event_depends_only_on_top`). -/
theorem onesInRows_topRows_depends_only_on_top {m n g : ℕ}
    (c c' : MonotoneColumnSums m n)
    (htop : ∀ col, (c col).val - g = (c' col).val - g)
    (σ : Scramble m n) (S : Finset (Fin n)) :
    onesInRows c σ (topRows m g) S = onesInRows c' σ (topRows m g) S := by
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r.val < m - g := by simpa [topRows] using hr
  have hrow : monotoneRowOnes c r = monotoneRowOnes c' r := by
    ext col
    simp only [monotoneRowOnes, Finset.mem_filter, Finset.mem_univ, true_and]
    have := htop col
    omega
  simp only [scrambledRowOnes, hrow]

/-- A matrix of total at most `j` has its `g`-top in `tops g n j`. -/
theorem topOf_mem_tops {m n : ℕ} (g j : ℕ) (c : MonotoneColumnSums m n)
    (hc : totalColumnOnes c ≤ j) : topOf g c ∈ tops g n j :=
  Finset.mem_image.mpr ⟨fun col => (c col).val, mem_sset.mpr hc, rfl⟩

end Chvatal
