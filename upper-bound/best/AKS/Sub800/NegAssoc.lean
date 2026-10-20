import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Fintype.Pi

/-! # Negative association of a uniform `k`-subset (W4.3 of LEAN-PLAN.md)

Finite (counting) form, as used by the walk bound (ROUND2.md §4): for a uniformly random
`k`-subset `S` of `U`, and nonnegative functions `f`, `g` that are monotone and depend only on
`S ∩ A`, resp. `S ∩ B` with `A`, `B` disjoint,

  `#(powersetCard k U) · Σ_S f S · g S ≤ (Σ_S f S) · (Σ_S g S)`.

Proof: decompose `S = X ∪ Y`, `X ⊆ A`, `Y ⊆ U \ A`, by `j = #X`; the averages of `f` over
`j`-subsets increase in `j`, those of `g` over `(k-j)`-subsets decrease in `j`, and a weighted
Chebyshev inequality concludes. -/

open Finset BigOperators

namespace NegAssoc

/-- Weighted Chebyshev sum inequality for antivarying sequences. -/
theorem weighted_chebyshev {ι : Type*} (s : Finset ι) (w F G : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, 0 < w i → 0 < w j → (F i - F j) * (G i - G j) ≤ 0) :
    (∑ i ∈ s, w i) * (∑ i ∈ s, w i * F i * G i) ≤
      (∑ i ∈ s, w i * F i) * (∑ i ∈ s, w i * G i) := by
  have key : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((F i - F j) * (G i - G j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    rcases (hw i hi).lt_or_eq with hwi | hwi
    · rcases (hw j hj).lt_or_eq with hwj | hwj
      · exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hwi.le hwj.le) (hanti i hi j hj hwi hwj)
      · rw [← hwj]; simp
    · rw [← hwi]; simp
  have expand : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ((F i - F j) * (G i - G j)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * F i * G i) -
        (∑ i ∈ s, w i * F i) * (∑ i ∈ s, w i * G i)) := by
    have h1 : ∀ i j, w i * w j * ((F i - F j) * (G i - G j)) =
        w j * (w i * F i * G i) + w i * (w j * F j * G j) -
          (w i * F i) * (w j * G j) - (w j * F j) * (w i * G i) := by
      intro i j; ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  linarith

variable {α : Type*} [DecidableEq α]

/-- Double counting of pairs `(T, x)`, `x ∈ T`, `#T = j+1`, against pairs `(X, y)`, `y ∉ X`,
`#X = j`, via `X = T.erase x`. -/
theorem double_count (A : Finset α) (j : ℕ) (φ : Finset α → ℝ) :
    ∑ T ∈ A.powersetCard (j + 1), ∑ x ∈ T, φ (T.erase x) =
      ∑ X ∈ A.powersetCard j, ∑ _y ∈ A \ X, φ X := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun p _ => ⟨p.1.erase p.2, p.2⟩) (fun q _ => ⟨insert q.2 q.1, q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨T, x⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp ⊢
    obtain ⟨⟨hTA, hTc⟩, hxT⟩ := hp
    refine ⟨⟨(Finset.erase_subset x T).trans hTA, ?_⟩, ?_⟩
    · rw [Finset.card_erase_of_mem hxT, hTc]; rfl
    · exact Finset.mem_sdiff.2 ⟨hTA hxT, Finset.notMem_erase x T⟩
  · rintro ⟨X, y⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powersetCard, Finset.mem_sdiff] at hq ⊢
    obtain ⟨⟨hXA, hXc⟩, hyA, hyX⟩ := hq
    refine ⟨⟨Finset.insert_subset hyA hXA, ?_⟩, Finset.mem_insert_self y X⟩
    rw [Finset.card_insert_of_notMem hyX, hXc]
  · rintro ⟨T, x⟩ hp
    simp only [Finset.mem_sigma] at hp
    simp [Finset.insert_erase hp.2]
  · rintro ⟨X, y⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_sdiff] at hq
    simp [Finset.erase_insert hq.2.2]
  · rintro ⟨T, x⟩ _
    rfl

/-- For `f` monotone on subsets of `A`, `(#A - j) · Σ_{#X = j} f X ≤ (j+1) · Σ_{#T = j+1} f T`. -/
theorem layer_mono (A : Finset α) (j : ℕ) (f : Finset α → ℝ)
    (hf : ∀ s t, s ⊆ t → t ⊆ A → f s ≤ f t) :
    ((A.card - j : ℕ) : ℝ) * ∑ X ∈ A.powersetCard j, f X ≤
      ((j + 1 : ℕ) : ℝ) * ∑ T ∈ A.powersetCard (j + 1), f T := by
  have h1 : ((A.card - j : ℕ) : ℝ) * ∑ X ∈ A.powersetCard j, f X =
      ∑ T ∈ A.powersetCard (j + 1), ∑ x ∈ T, f (T.erase x) := by
    rw [double_count, Finset.mul_sum]
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Finset.mem_powersetCard] at hX
    rw [Finset.card_sdiff_of_subset hX.1, hX.2]
  rw [h1, Finset.mul_sum]
  refine Finset.sum_le_sum fun T hT => ?_
  rw [Finset.mem_powersetCard] at hT
  calc ∑ x ∈ T, f (T.erase x) ≤ ∑ _x ∈ T, f T :=
        Finset.sum_le_sum fun x _ => hf _ _ (Finset.erase_subset x T) hT.1
    _ = ((j + 1 : ℕ) : ℝ) * f T := by rw [Finset.sum_const, nsmul_eq_mul, hT.2]

/-- Splitting a `k`-subset of `U ⊇ A` into its parts in `A` and in `U \ A`. -/
theorem split_sum (U A : Finset α) (hA : A ⊆ U) (k : ℕ) (h : Finset α → Finset α → ℝ) :
    ∑ S ∈ U.powersetCard k, h (S ∩ A) (S \ A) =
      ∑ j ∈ Finset.range (k + 1), ∑ X ∈ A.powersetCard j,
        ∑ Y ∈ (U \ A).powersetCard (k - j), h X Y := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun S => (S ∩ A).card) (t := Finset.range (k + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [← Finset.sum_product']
    refine Finset.sum_bij' (fun S _ => (S ∩ A, S \ A)) (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨hSU, hSc⟩, hSA⟩ := hS
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_right, hSA⟩, Finset.sdiff_subset_sdiff hSU (Finset.Subset.refl A), ?_⟩
      have := Finset.card_inter_add_card_sdiff S A
      omega
    · rintro ⟨X, Y⟩ hp
      simp only [Finset.mem_product, Finset.mem_powersetCard] at hp
      obtain ⟨⟨hXA, hXc⟩, hYU, hYc⟩ := hp
      have hdisj : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro x hxX hxY
        exact (Finset.mem_sdiff.1 (hYU hxY)).2 (hXA hxX)
      have hXY : (X ∪ Y) ∩ A = X := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact hx
          · exact absurd hxA (Finset.mem_sdiff.1 (hYU hx)).2
        · intro hx; exact ⟨Or.inl hx, hXA hx⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.union_subset (hXA.trans hA) (hYU.trans Finset.sdiff_subset), ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hXc, hYc]; omega
      · rw [hXY, hXc]
    · intro S _
      show S ∩ A ∪ S \ A = S
      rw [Finset.union_comm]; exact Finset.sdiff_union_inter S A
    · rintro ⟨X, Y⟩ hp
      simp only [Finset.mem_product, Finset.mem_powersetCard] at hp
      obtain ⟨⟨hXA, _⟩, hYU, _⟩ := hp
      have hYA : ∀ y ∈ Y, y ∉ A := fun y hy => (Finset.mem_sdiff.1 (hYU hy)).2
      simp only [Prod.mk.injEq]
      constructor
      · ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact hx
          · exact absurd hxA (hYA x hx)
        · intro hx; exact ⟨Or.inl hx, hXA hx⟩
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx | hx, hxA⟩
          · exact absurd (hXA hx) hxA
          · exact hx
        · intro hx; exact ⟨Or.inr hx, hYA x hx⟩
    · intro S _
      rfl
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_range]
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := A))
    omega

/-- Average of `f` over the `j`-subsets of `A`. -/
noncomputable def layerAvg (A : Finset α) (f : Finset α → ℝ) (j : ℕ) : ℝ :=
  (∑ X ∈ A.powersetCard j, f X) / (A.card.choose j : ℝ)

theorem layerAvg_succ (A : Finset α) (f : Finset α → ℝ)
    (hf : ∀ s t, s ⊆ t → t ⊆ A → f s ≤ f t) (i : ℕ) (hi : i + 1 ≤ A.card) :
    layerAvg A f i ≤ layerAvg A f (i + 1) := by
  unfold layerAvg
  have hDi : (0 : ℝ) < (A.card.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hDs : (0 : ℝ) < (A.card.choose (i + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hi
  have hid : (A.card.choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) =
      (A.card.choose i : ℝ) * ((A.card - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq A.card i
  have hl := layer_mono A i f hf
  rw [div_le_div_iff₀ hDi hDs]
  have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  refine le_of_mul_le_mul_right ?_ hpos
  calc (∑ X ∈ A.powersetCard i, f X) * (A.card.choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ)
      = (A.card.choose i : ℝ) * (((A.card - i : ℕ) : ℝ) * ∑ X ∈ A.powersetCard i, f X) := by
        rw [mul_assoc, hid]; ring
    _ ≤ (A.card.choose i : ℝ) * (((i + 1 : ℕ) : ℝ) * ∑ T ∈ A.powersetCard (i + 1), f T) :=
        mul_le_mul_of_nonneg_left hl hDi.le
    _ = (∑ T ∈ A.powersetCard (i + 1), f T) * (A.card.choose i : ℝ) * ((i + 1 : ℕ) : ℝ) := by
        ring

theorem layerAvg_mono (A : Finset α) (f : Finset α → ℝ)
    (hf : ∀ s t, s ⊆ t → t ⊆ A → f s ≤ f t) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ A.card) :
    layerAvg A f i ≤ layerAvg A f j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (layerAvg_succ A f hf j hj)

omit [DecidableEq α] in
theorem sum_eq_choose_mul_layerAvg (A : Finset α) (f : Finset α → ℝ) (j : ℕ) :
    ∑ X ∈ A.powersetCard j, f X = (A.card.choose j : ℝ) * layerAvg A f j := by
  unfold layerAvg
  by_cases h : (A.card.choose j : ℝ) = 0
  · have hc : A.card.choose j = 0 := by exact_mod_cast h
    have he : A.powersetCard j = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_powersetCard, hc]
    rw [he, h]; simp
  · field_simp

/-- **Negative association of a uniform `k`-subset**, counting form: `f` monotone in `S ∩ A`,
`g` monotone in `S ∩ B`, `A`, `B` disjoint parts of `U`. -/
theorem neg_assoc_row (U A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U \ A) (k : ℕ)
    (f g : Finset α → ℝ) (hf : ∀ s t, s ⊆ t → t ⊆ A → f s ≤ f t)
    (hg : ∀ s t, s ⊆ t → t ⊆ B → g s ≤ g t) :
    ((U.powersetCard k).card : ℝ) * ∑ S ∈ U.powersetCard k, f (S ∩ A) * g (S ∩ B) ≤
      (∑ S ∈ U.powersetCard k, f (S ∩ A)) * (∑ S ∈ U.powersetCard k, g (S ∩ B)) := by
  set C := U \ A
  let g' : Finset α → ℝ := fun Y => g (Y ∩ B)
  have hg' : ∀ s t, s ⊆ t → t ⊆ C → g' s ≤ g' t := fun s t hst _ =>
    hg _ _ (Finset.inter_subset_inter_right hst) Finset.inter_subset_right
  have hSB : ∀ S : Finset α, S ∩ B = (S \ A) ∩ B := by
    intro S; ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hxS, hxB⟩; exact ⟨⟨hxS, (Finset.mem_sdiff.1 (hB hxB)).2⟩, hxB⟩
    · rintro ⟨⟨hxS, _⟩, hxB⟩; exact ⟨hxS, hxB⟩
  let d : ℕ → ℝ := fun j => (A.card.choose j : ℝ)
  let c : ℕ → ℝ := fun j => (C.card.choose (k - j) : ℝ)
  let F : ℕ → ℝ := fun j => layerAvg A f j
  let G : ℕ → ℝ := fun j => layerAvg C g' (k - j)
  have ha : ∀ j, ∑ X ∈ A.powersetCard j, f X = d j * F j := fun j =>
    sum_eq_choose_mul_layerAvg A f j
  have hb : ∀ j, ∑ Y ∈ C.powersetCard (k - j), g' Y = c j * G j := fun j =>
    sum_eq_choose_mul_layerAvg C g' (k - j)
  have hcount : ∀ j, ∑ _Y ∈ C.powersetCard (k - j), (1 : ℝ) = c j := fun j => by
    simp [c, Finset.card_powersetCard]
  have hdcount : ∀ j, ∑ _X ∈ A.powersetCard j, (1 : ℝ) = d j := fun j => by
    simp [d, Finset.card_powersetCard]
  -- the four sums in terms of the layers
  have hfg : ∑ S ∈ U.powersetCard k, f (S ∩ A) * g (S ∩ B) =
      ∑ j ∈ Finset.range (k + 1), d j * c j * F j * G j := by
    have e := split_sum U A hA k (fun X Y => f X * g' Y)
    simp only at e
    rw [Finset.sum_congr rfl fun S _ => by rw [hSB S], e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul_sum, ha, hb]; ring
  have hf1 : ∑ S ∈ U.powersetCard k, f (S ∩ A) =
      ∑ j ∈ Finset.range (k + 1), d j * c j * F j := by
    have e := split_sum U A hA k (fun X (_ : Finset α) => f X)
    simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul] at e
    rw [e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum, ha]; simp only [c]; ring
  have hg1 : ∑ S ∈ U.powersetCard k, g (S ∩ B) =
      ∑ j ∈ Finset.range (k + 1), d j * c j * G j := by
    have e := split_sum U A hA k (fun (_ : Finset α) Y => g' Y)
    simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul] at e
    rw [Finset.sum_congr rfl fun S _ => by rw [hSB S]]
    refine e.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [hb]; simp only [d]; ring
  have hN : ((U.powersetCard k).card : ℝ) = ∑ j ∈ Finset.range (k + 1), d j * c j := by
    have e := split_sum U A hA k (fun (_ _ : Finset α) => (1 : ℝ))
    simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul, mul_one] at e
    rw [Finset.card_powersetCard, e]
  rw [hfg, hf1, hg1, hN]
  have hw : ∀ i ∈ Finset.range (k + 1), 0 ≤ d i * c i := fun i _ => by positivity
  have key := weighted_chebyshev (Finset.range (k + 1)) (fun j => d j * c j) F G hw ?_
  · simpa only [mul_assoc] using key
  intro i hi j hj hwi hwj
  rw [Finset.mem_range] at hi hj
  have hdi : i ≤ A.card := by
    by_contra h; push_neg at h
    have : A.card.choose i = 0 := Nat.choose_eq_zero_of_lt h
    simp [d, this] at hwi
  have hdj : j ≤ A.card := by
    by_contra h; push_neg at h
    have : A.card.choose j = 0 := Nat.choose_eq_zero_of_lt h
    simp [d, this] at hwj
  have hci : k - i ≤ C.card := by
    by_contra h; push_neg at h
    have : C.card.choose (k - i) = 0 := Nat.choose_eq_zero_of_lt h
    simp [c, this] at hwi
  have hcj : k - j ≤ C.card := by
    by_contra h; push_neg at h
    have : C.card.choose (k - j) = 0 := Nat.choose_eq_zero_of_lt h
    simp [c, this] at hwj
  rcases le_total i j with hij | hji
  · have h1 : F i ≤ F j := layerAvg_mono A f hf hij hdj
    have h2 : G j ≤ G i := layerAvg_mono C g' hg' (by omega) hci
    nlinarith
  · have h1 : F j ≤ F i := layerAvg_mono A f hf hji hdi
    have h2 : G i ≤ G j := layerAvg_mono C g' hg' (by omega) hcj
    nlinarith

section Closure

/-- Negative covariance of the two projections `a`, `b` of a finite uniform sample `s`:
every pair of monotone functions of `a` and of `b` has nonpositive covariance. -/
def CovNeg {Ω X Y : Type*} [Preorder X] [Preorder Y] (s : Finset Ω) (a : Ω → X) (b : Ω → Y) :
    Prop :=
  ∀ f : X → ℝ, Monotone f → ∀ g : Y → ℝ, Monotone g →
    (s.card : ℝ) * ∑ ω ∈ s, f (a ω) * g (b ω) ≤ (∑ ω ∈ s, f (a ω)) * (∑ ω ∈ s, g (b ω))

/-- Independent product: negative covariance passes to `s₁ ×ˢ s₂` with componentwise orders. -/
theorem CovNeg.prod {Ω₁ Ω₂ X₁ X₂ Y₁ Y₂ : Type*} [Preorder X₁] [Preorder X₂] [Preorder Y₁]
    [Preorder Y₂] {s₁ : Finset Ω₁} {s₂ : Finset Ω₂} {a₁ : Ω₁ → X₁} {a₂ : Ω₂ → X₂}
    {b₁ : Ω₁ → Y₁} {b₂ : Ω₂ → Y₂} (h₁ : CovNeg s₁ a₁ b₁) (h₂ : CovNeg s₂ a₂ b₂) :
    CovNeg (s₁ ×ˢ s₂) (fun p => (a₁ p.1, a₂ p.2)) (fun p => (b₁ p.1, b₂ p.2)) := by
  intro f hf g hg
  set n₂ : ℝ := (s₂.card : ℝ)
  have hn₂ : 0 ≤ n₂ := by positivity
  -- inner step: for fixed ω₁, apply h₂ to the sections
  have inner : ∀ ω₁ ∈ s₁, n₂ * ∑ ω₂ ∈ s₂, f (a₁ ω₁, a₂ ω₂) * g (b₁ ω₁, b₂ ω₂) ≤
      (∑ ω₂ ∈ s₂, f (a₁ ω₁, a₂ ω₂)) * (∑ ω₂ ∈ s₂, g (b₁ ω₁, b₂ ω₂)) := fun ω₁ _ =>
    h₂ (fun x => f (a₁ ω₁, x)) (fun x y hxy => hf ⟨le_rfl, hxy⟩)
      (fun y => g (b₁ ω₁, y)) (fun x y hxy => hg ⟨le_rfl, hxy⟩)
  -- outer step: the section sums are monotone functions of a₁ ω₁, b₁ ω₁
  let F : X₁ → ℝ := fun x => ∑ ω₂ ∈ s₂, f (x, a₂ ω₂)
  let G : Y₁ → ℝ := fun y => ∑ ω₂ ∈ s₂, g (y, b₂ ω₂)
  have hF : Monotone F := fun x y hxy => Finset.sum_le_sum fun ω₂ _ => hf ⟨hxy, le_rfl⟩
  have hG : Monotone G := fun x y hxy => Finset.sum_le_sum fun ω₂ _ => hg ⟨hxy, le_rfl⟩
  have outer := h₁ F hF G hG
  rw [Finset.card_product, Finset.sum_product, Finset.sum_product, Finset.sum_product]
  push_cast
  calc ((s₁.card : ℝ) * n₂) * ∑ ω₁ ∈ s₁, ∑ ω₂ ∈ s₂, f (a₁ ω₁, a₂ ω₂) * g (b₁ ω₁, b₂ ω₂)
      = (s₁.card : ℝ) * ∑ ω₁ ∈ s₁, n₂ * ∑ ω₂ ∈ s₂, f (a₁ ω₁, a₂ ω₂) * g (b₁ ω₁, b₂ ω₂) := by
        rw [mul_assoc]; congr 1; rw [Finset.mul_sum]
    _ ≤ (s₁.card : ℝ) * ∑ ω₁ ∈ s₁, F (a₁ ω₁) * G (b₁ ω₁) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum inner) (by positivity)
    _ ≤ (∑ ω₁ ∈ s₁, F (a₁ ω₁)) * (∑ ω₁ ∈ s₁, G (b₁ ω₁)) := outer
    _ = _ := rfl

/-- One row: a uniform `k`-subset of `U`, projected to its parts in disjoint `A`, `B ⊆ U`. -/
theorem covNeg_row (U A B : Finset α) (hA : A ⊆ U) (hB : B ⊆ U \ A) (k : ℕ) :
    CovNeg (U.powersetCard k) (fun S => S ∩ A) (fun S => S ∩ B) := by
  intro f hf g hg
  exact neg_assoc_row U A B hA hB k f g (fun s t hst _ => hf hst) (fun s t hst _ => hg hst)

/-- Transport along a bijection of samples that preserves the projections. -/
theorem CovNeg.of_bij {Ω Ω' X Y : Type*} [Preorder X] [Preorder Y] {s : Finset Ω}
    {t : Finset Ω'} {a : Ω → X} {b : Ω → Y} {a' : Ω' → X} {b' : Ω' → Y}
    (h : CovNeg s a b) (e : Ω → Ω') (he : ∀ ω ∈ s, e ω ∈ t)
    (hinj : ∀ ω₁ ∈ s, ∀ ω₂ ∈ s, e ω₁ = e ω₂ → ω₁ = ω₂)
    (hsurj : ∀ ω' ∈ t, ∃ ω ∈ s, e ω = ω')
    (ha : ∀ ω ∈ s, a' (e ω) = a ω) (hb : ∀ ω ∈ s, b' (e ω) = b ω) : CovNeg t a' b' := by
  intro f hf g hg
  have hsurj' : ∀ ω' ∈ t, ∃ ω, ∃ _ : ω ∈ s, e ω = ω' := fun ω' hω' => by
    obtain ⟨ω, hω, h⟩ := hsurj ω' hω'
    exact ⟨ω, hω, h⟩
  have hcard : t.card = s.card :=
    (Finset.card_bij (fun ω _ => e ω) he hinj hsurj').symm
  have hsum : ∀ φ : Ω' → ℝ, ∑ ω' ∈ t, φ ω' = ∑ ω ∈ s, φ (e ω) := fun φ =>
    (Finset.sum_bij (fun ω _ => e ω) he hinj hsurj' (fun _ _ => rfl)).symm
  rw [hcard, hsum, hsum, hsum]
  have e1 : ∑ ω ∈ s, f (a' (e ω)) * g (b' (e ω)) = ∑ ω ∈ s, f (a ω) * g (b ω) :=
    Finset.sum_congr rfl fun ω hω => by rw [ha ω hω, hb ω hω]
  have e2 : ∑ ω ∈ s, f (a' (e ω)) = ∑ ω ∈ s, f (a ω) :=
    Finset.sum_congr rfl fun ω hω => by rw [ha ω hω]
  have e3 : ∑ ω ∈ s, g (b' (e ω)) = ∑ ω ∈ s, g (b ω) :=
    Finset.sum_congr rfl fun ω hω => by rw [hb ω hω]
  rw [e1, e2, e3]
  exact h f hf g hg

/-- Monotone maps of the projections preserve negative covariance. -/
theorem CovNeg.comp_mono {Ω X Y X' Y' : Type*} [Preorder X] [Preorder Y] [Preorder X']
    [Preorder Y'] {s : Finset Ω} {a : Ω → X} {b : Ω → Y} (h : CovNeg s a b)
    {u : X → X'} {v : Y → Y'} (hu : Monotone u) (hv : Monotone v) :
    CovNeg s (fun ω => u (a ω)) (fun ω => v (b ω)) := fun f hf g hg =>
  h (fun x => f (u x)) (hf.comp hu) (fun y => g (v y)) (hg.comp hv)

/-- Independent rows: a product of `R` row samples, projected coordinatewise. -/
theorem covNeg_pi {Ω X Y : Type*} [DecidableEq Ω] [Preorder X] [Preorder Y] (a : Ω → X)
    (b : Ω → Y) : ∀ (R : ℕ) (s : Fin R → Finset Ω), (∀ r, CovNeg (s r) a b) →
      CovNeg (Fintype.piFinset s) (fun ω r => a (ω r)) (fun ω r => b (ω r)) := by
  intro R
  induction R with
  | zero =>
    intro s _ f _ g _
    have hs : Fintype.piFinset s = {Fin.elim0} := by
      ext ω
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => funext fun r => r.elim0, fun _ r => r.elim0⟩
    rw [hs]; simp
  | succ R ih =>
    intro s hs
    have hprod := CovNeg.prod (hs 0) (ih (fun r => s r.succ) fun r => hs r.succ)
    have hmono := hprod.comp_mono (u := fun q : X × (Fin R → X) => (Fin.cons q.1 q.2 : Fin (R + 1) → X))
      (v := fun q : Y × (Fin R → Y) => (Fin.cons q.1 q.2 : Fin (R + 1) → Y))
      (fun q q' hq => by
        intro r
        refine Fin.cases ?_ (fun i => ?_) r
        · simpa using hq.1
        · simpa using hq.2 i)
      (fun q q' hq => by
        intro r
        refine Fin.cases ?_ (fun i => ?_) r
        · simpa using hq.1
        · simpa using hq.2 i)
    refine hmono.of_bij (fun p => (Fin.cons p.1 p.2 : Fin (R + 1) → Ω)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨x, ω⟩ hp
      rw [Finset.mem_product, Fintype.mem_piFinset] at hp
      rw [Fintype.mem_piFinset]
      intro r
      refine Fin.cases ?_ (fun i => ?_) r
      · simpa using hp.1
      · simpa using hp.2 i
    · rintro ⟨x, ω⟩ _ ⟨x', ω'⟩ _ h
      have h0 := congrFun h 0
      have ht : ω = ω' := funext fun i => by simpa using congrFun h i.succ
      simp only [Fin.cons_zero] at h0
      rw [h0, ht]
    · intro ω hω
      rw [Fintype.mem_piFinset] at hω
      refine ⟨(ω 0, Fin.tail ω), ?_, Fin.cons_self_tail ω⟩
      rw [Finset.mem_product, Fintype.mem_piFinset]
      exact ⟨hω 0, fun i => hω i.succ⟩
    · rintro ⟨x, ω⟩ _
      funext r
      refine Fin.cases ?_ (fun i => ?_) r <;> simp
    · rintro ⟨x, ω⟩ _
      funext r
      refine Fin.cases ?_ (fun i => ?_) r <;> simp

/-- **Product form** (ROUND2 §4, the NA step): independent rows, each a uniform `k r`-subset of
`U`, and nonnegative monotone functions of pairwise disjoint column sets `A j`:
`N^{#J} · Σ_ω Π_j φ_j(ω ∩ A_j) ≤ N · Π_j Σ_ω φ_j(ω ∩ A_j)`, `N` the number of samples. -/
theorem neg_assoc_prod {ι : Type*} [DecidableEq ι] (U : Finset α) (R : ℕ) (k : Fin R → ℕ)
    (A : ι → Finset α) (φ : ι → (Fin R → Finset α) → ℝ)
    (hφ0 : ∀ j y, 0 ≤ φ j y) (hφm : ∀ j, Monotone (φ j)) :
    ∀ J : Finset ι, (∀ j ∈ J, A j ⊆ U) → (J : Set ι).PairwiseDisjoint A →
      ((Fintype.piFinset fun r => U.powersetCard (k r)).card : ℝ) ^ J.card *
          ∑ ω ∈ Fintype.piFinset (fun r => U.powersetCard (k r)),
            ∏ j ∈ J, φ j (fun r => ω r ∩ A j) ≤
        ((Fintype.piFinset fun r => U.powersetCard (k r)).card : ℝ) *
          ∏ j ∈ J, ∑ ω ∈ Fintype.piFinset (fun r => U.powersetCard (k r)),
            φ j (fun r => ω r ∩ A j) := by
  set Ω := Fintype.piFinset fun r => U.powersetCard (k r)
  set N : ℝ := (Ω.card : ℝ)
  have hN : 0 ≤ N := by positivity
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _ _
    simp [N]
  | @insert j0 J hj0 ih =>
    intro hU hdisj
    have hU' : ∀ j ∈ J, A j ⊆ U := fun j hj => hU j (Finset.mem_insert_of_mem hj)
    have hdisj' : (J : Set ι).PairwiseDisjoint A :=
      hdisj.subset (by intro x hx; simp [hx])
    set B := J.biUnion A
    have hBU : B ⊆ U \ A j0 := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨j, hj, hxj⟩ := hx
      refine Finset.mem_sdiff.2 ⟨hU' j hj hxj, fun hx0 => ?_⟩
      have hne : j0 ≠ j := fun h => hj0 (h ▸ hj)
      have := hdisj (by simp) (by simp [hj]) hne
      exact Finset.disjoint_left.1 this hx0 hxj
    have hcov := covNeg_pi (fun S : Finset α => S ∩ A j0) (fun S : Finset α => S ∩ B) R
      (fun r => U.powersetCard (k r))
      (fun r => covNeg_row U (A j0) B (hU j0 (Finset.mem_insert_self j0 J)) hBU (k r))
    let Ψ : (Fin R → Finset α) → ℝ := fun y => ∏ j ∈ J, φ j (fun r => y r ∩ A j)
    have hΨ : Monotone Ψ := fun y y' hy => Finset.prod_le_prod
      (fun j _ => hφ0 j _) (fun j _ => hφm j fun r => Finset.inter_subset_inter_right (hy r))
    have hΨB : ∀ ω : Fin R → Finset α, Ψ (fun r => ω r ∩ B) = ∏ j ∈ J, φ j (fun r => ω r ∩ A j) := by
      intro ω
      refine Finset.prod_congr rfl fun j hj => ?_
      congr 1
      funext r
      have hAB : A j ⊆ B := Finset.subset_biUnion_of_mem A hj
      rw [Finset.inter_assoc, Finset.inter_eq_right.2 hAB]
    have key := hcov (φ j0) (hφm j0) Ψ hΨ
    simp only [hΨB] at key
    rw [Finset.card_insert_of_notMem hj0, Finset.prod_insert hj0]
    simp_rw [Finset.prod_insert hj0]
    have hS0 : 0 ≤ ∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0) :=
      Finset.sum_nonneg fun ω _ => hφ0 j0 _
    calc N ^ (J.card + 1) * ∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0) *
            ∏ j ∈ J, φ j (fun r => ω r ∩ A j)
        = N ^ J.card * (N * ∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0) *
            ∏ j ∈ J, φ j (fun r => ω r ∩ A j)) := by ring
      _ ≤ N ^ J.card * ((∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0)) *
            ∑ ω ∈ Ω, ∏ j ∈ J, φ j (fun r => ω r ∩ A j)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = (∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0)) *
            (N ^ J.card * ∑ ω ∈ Ω, ∏ j ∈ J, φ j (fun r => ω r ∩ A j)) := by ring
      _ ≤ (∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0)) *
            (N * ∏ j ∈ J, ∑ ω ∈ Ω, φ j (fun r => ω r ∩ A j)) :=
          mul_le_mul_of_nonneg_left (ih hU' hdisj') hS0
      _ = N * ((∑ ω ∈ Ω, φ j0 (fun r => ω r ∩ A j0)) *
            ∏ j ∈ J, ∑ ω ∈ Ω, φ j (fun r => ω r ∩ A j)) := by ring

end Closure

end NegAssoc
