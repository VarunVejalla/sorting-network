import R1Fields

/-! # Invariant `P` at every stage (W1, step 12)

`P_all`: for a flow table `F` with the parity and residual facts and node networks meeting
`R1Specs`, invariant `P` holds at every stage `t ≤ t_f`, for every input. -/

namespace R1T

open Finset
open Chvatal (KBag Placement)

variable {d tf : ℕ}

/-- `P` at stage `0`: only the root holds keys, and it has no outsiders of order `≥ 1`. -/
theorem P_zero (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n) (v : Equiv.Perm (Fin (16 ^ d))) :
    OutsiderBoundLe d 0 (execPlacement F nets v 0 (Nat.zero_le _)) id := by
  intro b r hr
  have hc := (cap_pos d b.l 0).le
  have hrhs : 0 ≤ mu * delta ^ r * cap d b.l 0 := by
    have := mu_pos.le; have := delta_pos.le; positivity
  by_cases hb : b = KBag.root 16 d
  · subst hb
    rw [KBag.strangers_eq_zero_of_lt_order _ (r + 1) id _ (by norm_num) (by omega)
      (by show 0 < r + 1; omega)]
    simpa using hrhs
  · have h0 : (execPlacement F nets v 0 (Nat.zero_le _)).regs b = ∅ := by
      have hcard := execPlacement_card F nets v 0 (Nat.zero_le _) b
      rw [F.ha_init b hb] at hcard
      exact Finset.card_eq_zero.mp hcard
    rw [h0, KBag.strangers_empty]
    simpa using hrhs

/-- **`P` at every stage.** -/
theorem P_all (F : FlowTableB d tf)
    (nets : ℕ → (b : KBag 16 d) → (n : ℕ) → ComparatorNetwork n)
    (hspec : R1Specs F nets) (hpar : ∀ t, t ≤ tf → ParityFact F t) (hres : ResidFact F)
    (v : Equiv.Perm (Fin (16 ^ d))) :
    ∀ t (ht : t ≤ tf), OutsiderBoundLe d t (execPlacement F nets v t ht) id
  | 0, _ => P_zero F nets v
  | t + 1, ht => by
    have hP := P_all F nets hspec hpar hres v t (by omega)
    have K := realStageKernel F nets v t ht hP
      (badSend_field F nets v t ht hspec (hpar t (by omega)) hres hP)
      (fringeSend_field F nets v t ht hspec hP)
    exact outsiderBound_step d t _ _ id id hP K

end R1T
