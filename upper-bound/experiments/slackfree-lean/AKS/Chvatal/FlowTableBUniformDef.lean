module

public import AKS.Chvatal.FlowTableB
public import AKS.Chvatal.FlowSizes7

@[expose] public section

/-! The uniform (equal-block) table as a `FlowTableB`; split from `FlowTableBUniform` so that the
placement layer's consumers (`KernelSetup`, `BadSendField`, `RealBlocks`, ...) can use it. -/

namespace Chvatal

open Finset

/-- The uniform table `flowSizes7`, viewed as a per-bag table with equal blocks. -/
def uniformB (d : ℕ) (hd : 7 ≤ d) : FlowTableB d (tf7 d) where
  a := fun t b => flowA7 d hd b.l t
  up := fun t b => flowUp7 d hd b.l t
  down := fun t b _ => flowDown7 d hd b.l t
  ha_root := by simp [flowA7, KBag.root]
  ha_init := by
    intro b hb
    have hl : b.l ≠ 0 := by
      intro h0
      apply hb
      have hx := b.hx
      rw [h0] at hx
      exact KBag.ext h0 (by simpa using hx)
    simp [flowA7, hl]
  hup_even := fun t b ht => (flowSizes7 d hd).hup_even b.l t ht
  hup_root := fun t ht => (flowSizes7 d hd).hup_root t ht
  hdown_leaf := fun t b _ ht hb => by
    rw [hb]; exact (flowSizes7 d hd).hdown_leaf t ht
  hsplit := fun t b ht => by
    show flowA7 d hd b.l t = flowUp7 d hd b.l t + ∑ _j : Fin 64, flowDown7 d hd b.l t
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact flowSizes7_split d hd b.l t ht
  hcons := fun t b ht => by
    have h := flowSizes7_cons d hd b.l t ht
    show flowA7 d hd b.l (t + 1) =
      (if 1 ≤ b.l then flowDown7 d hd b.parent.l t else 0) +
      (if hh : b.l < d then ∑ j : Fin 64, flowUp7 d hd (b.child j j.isLt hh).l t else 0)
    have e1 : b.parent.l = b.l - 1 := rfl
    have e2 : ∀ (hh : b.l < d) (j : Fin 64), (b.child j j.isLt hh).l = b.l + 1 := fun _ _ => rfl
    simp only [e1, e2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact h


theorem uniformB_a (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) :
    (uniformB d hd).a t b = flowA7 d hd b.l t := rfl

theorem uniformB_up (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) :
    (uniformB d hd).up t b = flowUp7 d hd b.l t := rfl

theorem uniformB_down (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) (j : Fin 64) :
    (uniformB d hd).down t b j = flowDown7 d hd b.l t := rfl

/-- `uniformB`'s fields in terms of the old `flowSizes7` fields (bridge to `FlowSizes`). -/
theorem uniformB_a_fs (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) :
    (uniformB d hd).a t b = (flowSizes7 d hd).a b.l t := rfl

theorem uniformB_up_fs (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) :
    (uniformB d hd).up t b = (flowSizes7 d hd).up b.l t := rfl

theorem uniformB_down_fs (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) (j : Fin 64) :
    (uniformB d hd).down t b j = (flowSizes7 d hd).down b.l t := rfl

end Chvatal
