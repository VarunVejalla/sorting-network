module

public import AKS.Paterson.RootRebuildCards
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Exact counts in fixed positional grids -/

@[expose] public section

namespace Paterson.Bags

open Finset

theorem filter_card_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ a, P a ↔ Q (e a)) :
    (univ.filter P).card = (univ.filter Q).card := by
  apply card_bij (fun a _ ↦ e a)
  · intro a ha
    exact mem_filter.mpr ⟨mem_univ _, (h a).mp (mem_filter.mp ha).2⟩
  · intro a _ b _ hab; exact e.injective hab
  · intro b hb
    refine ⟨e.symm b, mem_filter.mpr ⟨mem_univ _, ?_⟩, e.apply_symm_apply b⟩
    apply (h _).mpr
    simpa only [e.apply_symm_apply] using (mem_filter.mp hb).2

theorem grid_filter_card {m width : ℕ} (hw : 0 < width)
    (P : ℕ → Prop) (Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] :
    (univ.filter (fun i : Fin (m * width) ↦ P (i.val / width) ∧ Q (i.val % width))).card =
      (univ.filter (fun x : Fin m ↦ P x.val)).card *
        (univ.filter (fun y : Fin width ↦ Q y.val)).card := by
  rw [filter_card_equiv finProdFinEquiv.symm
    (fun i : Fin (m * width) ↦ P (i.val / width) ∧ Q (i.val % width))
    (fun z : Fin m × Fin width ↦ P z.1.val ∧ Q z.2.val) (by intro i; rfl)]
  rw [← card_product, ← filter_product]
  simp only [univ_product_univ]

theorem fin_filter_card_cast {m n : ℕ} (h : m = n) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter (fun i : Fin m ↦ P i.val)).card =
      (univ.filter (fun i : Fin n ↦ P i.val)).card := by
  subst n
  rfl

theorem four_row_count (x : ℕ) (hx : x < 4) :
    (univ.filter (fun i : Fin 16 ↦ i.val / 4 = x)).card = 4 := by
  have hfilter : univ.filter (fun i : Fin 16 ↦ i.val / 4 = x) =
      univ.filter (fun i : Fin 16 ↦ x * 4 ≤ i.val ∧ i.val < x * 4 + 4) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    have h := div_mod_segment (a := i.val) (width := 4) (x := x) (n := 4)
      (by norm_num) (by omega)
    simpa only [Nat.mod_lt _ (by norm_num : 0 < 4), and_true] using h
  rw [hfilter, positional_interval_card _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem rebuildUpper_two_card {root : ℚ} {k t : ℕ} (hk : 5 ≤ k)
    (pl : StoredPlacement k) (ha : AllocationInvariant root t pl) (hp : t % 2 = 0)
    (n2 n4 : ℕ) (hw : 0 < (upperRegisters pl hk).card / 16)
    (hdiv : 16 ∣ (upperRegisters pl hk).card)
    (hfit : n4 + n2 / 4 ≤ (upperRegisters pl hk).card / 16)
    (hn2 : 4 ∣ n2) (b : Bag k) (hb : b.l = 2) :
    ((rebuildUpper pl hk n2 n4).regs b).card = n2 := by
  rw [rebuildUpper_two_filter hk pl ha hp n2 n4 hw hdiv b hb, filter_regs_card]
  simp only [registerOrdinal_enum]
  let width := (upperRegisters pl hk).card / 16
  have hsize : (upperRegisters pl hk).card = 16 * width :=
    (Nat.mul_div_cancel' hdiv).symm
  rw [fin_filter_card_cast hsize (fun a ↦ a / width / 4 = b.x ∧
    n4 ≤ a % width ∧ a % width < n4 + n2 / 4)]
  rw [grid_filter_card hw (fun x ↦ x / 4 = b.x)
    (fun y ↦ n4 ≤ y ∧ y < n4 + n2 / 4)]
  rw [four_row_count b.x (by have := b.hx; simpa only [hb] using this),
    positional_interval_card _ _ _ hfit, Nat.add_sub_cancel_left, Nat.mul_div_cancel' hn2]

end Paterson.Bags
