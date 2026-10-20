import AKS.Sub800.R1Final

/-! # Subtree decomposition at `k = 16` (W1, step 14)

`subtreeBags w = {w} ∪ ⋃_j subtreeBags (child_j w)` (disjoint), so subtree sums split as
`Σ_{subtree w} a = a w + Σ_j Σ_{subtree child_j} a` (`sum_subtree_split`); hence with
`G b = 16^(d − b.l) − Σ_{subtree b} a`, `a w = Σ_j G (child_j) − G w` (`a_eq_deficits`). -/

namespace R1T

open Finset
open Chvatal (KBag subtreeBags descendants mem_descendants descendants_disjoint subtreeBags_l_ge)

variable {d : ℕ}

theorem descendants_zero (w : KBag 16 d) : descendants 16 d (by norm_num) w 0 = {w} := by
  ext z
  rw [mem_descendants, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩; apply KBag.ext <;> simp_all
  · rintro rfl; simp

theorem descendants_succ (w : KBag 16 d) (hw : w.l < d) (h : ℕ) :
    descendants 16 d (by norm_num) w (h + 1) =
      (Finset.univ : Finset (Fin 16)).biUnion
        (fun j => descendants 16 d (by norm_num) (w.child j.val j.isLt hw) h) := by
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_descendants]
  constructor
  · rintro ⟨hl, hx⟩
    refine ⟨⟨(z.x / 16 ^ h) % 16, Nat.mod_lt _ (by norm_num)⟩, ?_, ?_⟩
    · show z.l = w.l + 1 + h; omega
    · show z.x / 16 ^ h = 16 * w.x + (z.x / 16 ^ h) % 16
      have e1 : z.x / 16 ^ (h + 1) = z.x / 16 ^ h / 16 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      rw [e1] at hx
      have := Nat.div_add_mod (z.x / 16 ^ h) 16
      omega
  · rintro ⟨j, hl, hx⟩
    have hl' : z.l = w.l + 1 + h := hl
    have hx' : z.x / 16 ^ h = 16 * w.x + j.val := hx
    refine ⟨by omega, ?_⟩
    rw [pow_succ, ← Nat.div_div_eq_div_mul, hx']
    have := j.isLt
    omega

theorem subtreeBags_eq (w : KBag 16 d) (hw : w.l < d) :
    subtreeBags 16 d (by norm_num) w =
      insert w ((Finset.univ : Finset (Fin 16)).biUnion
        (fun j => subtreeBags 16 d (by norm_num) (w.child j.val j.isLt hw))) := by
  unfold subtreeBags
  have hd : d - w.l + 1 = (d - (w.l + 1) + 1) + 1 := by omega
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨h, hh, hz⟩
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · left; rw [descendants_zero] at hz; exact Finset.mem_singleton.mp hz
    · right
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      rw [descendants_succ w hw] at hz
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
      obtain ⟨j, hj⟩ := hz
      exact ⟨j, h', by show h' < d - (w.l + 1) + 1; omega, hj⟩
  · rintro (rfl | ⟨j, h', hh, hz⟩)
    · exact ⟨0, by omega, by rw [descendants_zero]; exact Finset.mem_singleton_self _⟩
    · refine ⟨h' + 1, ?_, ?_⟩
      · have : h' < d - (w.l + 1) + 1 := hh
        omega
      · rw [descendants_succ w hw]
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨j, hz⟩

theorem not_mem_subtree_child (w : KBag 16 d) (hw : w.l < d) (j : Fin 16) :
    w ∉ subtreeBags 16 d (by norm_num) (w.child j.val j.isLt hw) := by
  intro h
  have := subtreeBags_l_ge (by norm_num) _ _ h
  have : (w.child j.val j.isLt hw).l = w.l + 1 := rfl
  omega

theorem subtree_child_disjoint (w : KBag 16 d) (hw : w.l < d) (j j' : Fin 16) (hne : j ≠ j') :
    Disjoint (subtreeBags 16 d (by norm_num) (w.child j.val j.isLt hw))
      (subtreeBags 16 d (by norm_num) (w.child j'.val j'.isLt hw)) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  unfold subtreeBags at hz hz'
  simp only [Finset.mem_biUnion, Finset.mem_range] at hz hz'
  obtain ⟨h, _, hz⟩ := hz
  obtain ⟨h', _, hz'⟩ := hz'
  rw [mem_descendants] at hz hz'
  have hl1 : z.l = w.l + 1 + h := hz.1
  have hl2 : z.l = w.l + 1 + h' := hz'.1
  have hhh : h = h' := by omega
  subst hhh
  have hx1 : z.x / 16 ^ h = 16 * w.x + j.val := hz.2
  have hx2 : z.x / 16 ^ h = 16 * w.x + j'.val := hz'.2
  exact hne (Fin.ext (by omega))

/-- Subtree sums split at the root of the subtree. -/
theorem sum_subtree_split (w : KBag 16 d) (hw : w.l < d) (A : KBag 16 d → ℤ) :
    ∑ z ∈ subtreeBags 16 d (by norm_num) w, A z =
      A w + ∑ j : Fin 16, ∑ z ∈ subtreeBags 16 d (by norm_num) (w.child j.val j.isLt hw), A z := by
  rw [subtreeBags_eq w hw, Finset.sum_insert]
  · congr 1
    rw [Finset.sum_biUnion]
    intro j _ j' _ hne
    exact subtree_child_disjoint w hw j j' hne
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    exact fun j => not_mem_subtree_child w hw j

/-- A leaf's subtree is itself. -/
theorem subtreeBags_leaf (w : KBag 16 d) (hw : w.l = d) :
    subtreeBags 16 d (by norm_num) w = {w} := by
  unfold subtreeBags
  rw [show d - w.l + 1 = 1 by omega, Finset.range_one, Finset.singleton_biUnion, descendants_zero]

/-- The deficit `R b − Σ_{subtree b} a` (in `ℤ`). -/
def Gof (A : KBag 16 d → ℕ) (b : KBag 16 d) : ℤ :=
  (16 : ℤ) ^ (d - b.l) - ∑ z ∈ subtreeBags 16 d (by norm_num) b, (A z : ℤ)

/-- **`a = Σ G(children) − G`.** -/
theorem a_eq_deficits (A : KBag 16 d → ℕ) (w : KBag 16 d) (hw : w.l < d) :
    (A w : ℤ) = ∑ j : Fin 16, Gof A (w.child j.val j.isLt hw) - Gof A w := by
  unfold Gof
  rw [sum_subtree_split w hw (fun z => (A z : ℤ)), Finset.sum_sub_distrib]
  have hc : ∑ j : Fin 16, (16 : ℤ) ^ (d - (w.child j.val j.isLt hw).l) = 16 * (16 : ℤ) ^ (d - (w.l + 1)) := by
    rw [Finset.sum_congr rfl (fun j _ => show (16 : ℤ) ^ (d - (w.child j.val j.isLt hw).l) =
      (16 : ℤ) ^ (d - (w.l + 1)) from rfl), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; push_cast; ring
  have hpow : (16 : ℤ) ^ (d - w.l) = 16 * (16 : ℤ) ^ (d - (w.l + 1)) := by
    rw [show d - w.l = (d - (w.l + 1)) + 1 by omega, pow_succ]; ring
  rw [hc, hpow]
  ring

theorem a_eq_leaf (A : KBag 16 d → ℕ) (w : KBag 16 d) (hw : w.l = d) :
    (A w : ℤ) = (16 : ℤ) ^ (d - w.l) - Gof A w := by
  unfold Gof; rw [subtreeBags_leaf w hw, Finset.sum_singleton]; ring

end R1T
