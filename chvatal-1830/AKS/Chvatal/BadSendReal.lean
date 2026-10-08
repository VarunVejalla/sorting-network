module
/-
  # Chvátal Lemma 4.2 for the real network: the order-0 parent-send bound (task H1)

  Source: V. Chvátal, *Lecture Notes on the New AKS Sorting Network*,
  Rutgers DCS-TR-294 (1992), Lemma 4.2.  For a node `q` with `a = π + 64 τ` keys at time `t`
  sorted by its node network (`NodeSpec`), the keys sent to child `j` are the outputs on the
  cell window `[π/2 + jτ, π/2 + (j+1)τ)`.  At most `2·EB` of them have rank outside the window
  (`NodeSpec.intruder_keys`); the keys of rank inside the window that are not addressed below
  the child are bounded by the pure sorted-window count, using Lemma 4.1 (`hM`) for `q`.

  Main result: `bad_send0_real`.

  Note on `BW`: `BlockWindow` cannot be imported together with `WireFlow` (both define
  `Chvatal.rankIn`), so the pure `ℕ`-set window counting of `BlockWindow` is reproduced
  verbatim in namespace `Chvatal.BW` with `rankIn` renamed to `rankN`.
-/

public import AKS.Chvatal.NodeKeys
public import AKS.Chvatal.Tree
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Chvatal

open Finset

namespace BW

/-- Rank of a key in the sorted order of `K`. -/
def rankN (K : Finset ℕ) (κ : ℕ) : ℕ := (K.filter (· < κ)).card

theorem rankN_lt_of_lt {K : Finset ℕ} {κ κ' : ℕ} (hκ : κ ∈ K) (h : κ < κ') :
    rankN K κ < rankN K κ' := by
  unfold rankN
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨κ, by simp [hκ, h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem rankN_injOn (K : Finset ℕ) : Set.InjOn (rankN K) (K : Set ℕ) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (ne_of_lt (rankN_lt_of_lt hx h))
  · exact h
  · exact absurd hxy.symm (ne_of_lt (rankN_lt_of_lt hy h))

/-- Keys below `lo` have rank below `L`. -/
theorem rankN_lt_of_lt_lo {K : Finset ℕ} {κ lo : ℕ} (hκ : κ ∈ K) (h : κ < lo) :
    rankN K κ < (K.filter (· < lo)).card := by
  unfold rankN
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨κ, by simp [hκ, h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 h⟩

theorem card_lt_add_card_ge (K : Finset ℕ) (hi : ℕ) :
    (K.filter (· < hi)).card + (K.filter (hi ≤ ·)).card = K.card := by
  have := Finset.card_filter_add_card_filter_not (s := K) (fun x => x < hi)
  simpa [not_lt] using this

/-- Keys at least `hi` have rank at least `a - R`. -/
theorem le_rankN_of_hi_le {K : Finset ℕ} {κ hi : ℕ} (h : hi ≤ κ) :
    K.card - (K.filter (hi ≤ ·)).card ≤ rankN K κ := by
  have h1 := card_lt_add_card_ge K hi
  have h2 : (K.filter (· < hi)).card ≤ rankN K κ := by
    unfold rankN
    apply Finset.card_le_card
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩
  omega

/-- W-A: the sorted window contains few keys outside the address interval. -/
theorem sorted_window_wrong_le (K : Finset ℕ) (s τ lo hi : ℕ) (hsτ : s + τ ≤ K.card) :
    (K.filter fun κ => s ≤ rankN K κ ∧ rankN K κ < s + τ ∧ ¬ (lo ≤ κ ∧ κ < hi)).card ≤
      ((K.filter (· < lo)).card - s) +
        ((K.filter (hi ≤ ·)).card - (K.card - s - τ)) := by
  set L := (K.filter (· < lo)).card with hL
  set R := (K.filter (hi ≤ ·)).card with hR
  have hRa : R ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  let t : Finset ℕ := Finset.Ico s (min L (s + τ)) ∪ Finset.Ico (max (K.card - R) s) (s + τ)
  have hsub : (K.filter fun κ => s ≤ rankN K κ ∧ rankN K κ < s + τ ∧
      ¬ (lo ≤ κ ∧ κ < hi)).card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (rankN K)
    · intro κ hκ
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hκ
      obtain ⟨hmem, h1, h2, h3⟩ := hκ
      simp only [Finset.mem_coe, t, Finset.mem_union, Finset.mem_Ico, lt_min_iff, max_le_iff]
      by_cases hlo : κ < lo
      · left
        exact ⟨h1, rankN_lt_of_lt_lo hmem hlo, h2⟩
      · have hhi : hi ≤ κ := by
          by_contra hh
          exact h3 ⟨by omega, by omega⟩
        right
        exact ⟨⟨le_rankN_of_hi_le hhi, h1⟩, h2⟩
    · exact (rankN_injOn K).mono (by intro x hx; simp only [Finset.coe_filter] at hx; exact hx.1)
  have hcard : t.card ≤ (L - s) + (R - (K.card - s - τ)) := by
    refine le_trans (Finset.card_union_le _ _) ?_
    simp only [Nat.card_Ico]
    omega
  exact le_trans hsub hcard


/-! ### Counting keys below the child intervals -/

theorem card_lt_split (K : Finset ℕ) {lo hi : ℕ} (h : lo ≤ hi) :
    (K.filter (· < hi)).card =
      (K.filter (· < lo)).card + (K.filter fun κ => lo ≤ κ ∧ κ < hi).card := by
  have : K.filter (· < hi) = K.filter (· < lo) ∪ K.filter (fun κ => lo ≤ κ ∧ κ < hi) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hx, hh⟩
      by_cases hl : x < lo
      · exact Or.inl ⟨hx, hl⟩
      · exact Or.inr ⟨hx, by omega, hh⟩
    · rintro (⟨hx, hl⟩ | ⟨hx, _, hh⟩)
      · exact ⟨hx, by omega⟩
      · exact ⟨hx, hh⟩
  rw [this, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro x _ h1 h2
  omega

theorem lower_count_le (K : Finset ℕ) (k τ S Ulo : ℕ) (ρ : ℝ)
    (hM : ∀ j' < k, ((K.filter fun κ => Ulo + j'*S ≤ κ ∧ κ < Ulo + (j'+1)*S).card : ℝ) ≤ τ + ρ)
    (m n : ℕ) (hn : m + n ≤ k) :
    ((K.filter (· < Ulo + (m + n)*S)).card : ℝ) ≤
      (K.filter (· < Ulo + m*S)).card + n * (τ + ρ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := ih (by omega)
    have h2 := hM (m + n) (by omega)
    have hle : Ulo + (m + n)*S ≤ Ulo + (m + n + 1)*S :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    have h3 := card_lt_split K hle
    have h4 : ((K.filter (· < Ulo + (m + (n+1))*S)).card : ℝ) =
        (K.filter (· < Ulo + (m + n)*S)).card +
          (K.filter fun κ => Ulo + (m + n)*S ≤ κ ∧ κ < Ulo + (m + n + 1)*S).card := by
      rw [show m + (n+1) = m + n + 1 by ring, h3]; push_cast; ring
    rw [h4]
    push_cast
    nlinarith

/-- W-C (Lemma 4.2). -/
theorem window_wrong_le (K : Finset ℕ) (k π τ S Ulo j : ℕ) (hj : j < k)
    (ha : K.card = π + k * τ) (hπ : 2 ∣ π) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hM : ∀ j' < k, ((K.filter fun κ => Ulo + j'*S ≤ κ ∧ κ < Ulo + (j'+1)*S).card : ℝ) ≤ τ + ρ)
    (hpos : (π : ℝ) / 2 ≤ (K.filter (· < Ulo)).card + (K.filter (Ulo + k*S ≤ ·)).card +
      ((k : ℝ) - 1) * ρ) :
    ((K.filter fun κ => π/2 + j*τ ≤ rankN K κ ∧ rankN K κ < π/2 + (j+1)*τ ∧
        ¬ (Ulo + j*S ≤ κ ∧ κ < Ulo + (j+1)*S)).card : ℝ) ≤
      (K.filter (· < Ulo)).card + (K.filter (Ulo + k*S ≤ ·)).card +
        ((k : ℝ) - 1) * ρ - π / 2 := by
  obtain ⟨p, rfl⟩ := hπ
  have hp : 2 * p / 2 = p := by omega
  rw [hp]
  obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - (j+1), by omega⟩
  set OL := (K.filter (· < Ulo)).card with hOL
  set OR := (K.filter (Ulo + (j+1+m)*S ≤ ·)).card with hOR
  have hW := sorted_window_wrong_le K (p + j*τ) τ (Ulo + j*S) (Ulo + (j+1)*S) (by
    rw [ha]; nlinarith [Nat.zero_le (m*τ)])
  have hwin : (p + j*τ) + τ = p + (j+1)*τ := by ring
  rw [hwin] at hW
  set L := (K.filter (· < Ulo + j*S)).card with hLdef
  set R := (K.filter (Ulo + (j+1)*S ≤ ·)).card with hRdef
  have hT : K.card - (p + j*τ) - τ = p + m*τ := by
    rw [ha]; apply Nat.sub_eq_of_eq_add; apply Nat.sub_eq_of_eq_add; ring
  -- real bounds
  have hLb : (L : ℝ) ≤ OL + j * (τ + ρ) := by
    have := lower_count_le K (j+1+m) τ S Ulo ρ hM 0 j (by omega)
    simpa [hLdef, hOL] using this
  have hRtot := card_lt_add_card_ge K (Ulo + (j+1)*S)
  have hk := lower_count_le K (j+1+m) τ S Ulo ρ hM (j+1) m (by omega)
  have hkt := card_lt_add_card_ge K (Ulo + (j+1+m)*S)
  have hRb : (R : ℝ) ≤ OR + m * (τ + ρ) := by
    have e1 : ((K.filter (· < Ulo + (j+1+m)*S)).card : ℝ) + OR = K.card := by
      exact_mod_cast hkt
    have e2 : ((K.filter (· < Ulo + (j+1)*S)).card : ℝ) + R = K.card := by
      exact_mod_cast hRtot
    linarith
  rw [hT] at hW
  have hx : (((L - (p + j*τ) : ℕ)) : ℝ) ≤ max 0 ((OL : ℝ) + j*ρ - p) := by
    by_cases h : L ≤ p + j*τ
    · rw [Nat.sub_eq_zero_of_le h]; simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by linarith)
  have hy : (((R - (p + m*τ) : ℕ)) : ℝ) ≤ max 0 ((OR : ℝ) + m*ρ - p) := by
    by_cases h : R ≤ p + m*τ
    · rw [Nat.sub_eq_zero_of_le h]; simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by linarith)
  have hWr : ((K.filter fun κ => p + j*τ ≤ rankN K κ ∧ rankN K κ < p + (j+1)*τ ∧
        ¬ (Ulo + j*S ≤ κ ∧ κ < Ulo + (j+1)*S)).card : ℝ) ≤
      (((L - (p + j*τ) : ℕ)) : ℝ) + (((R - (p + m*τ) : ℕ)) : ℝ) := by
    exact_mod_cast hW
  have hOLn : (0 : ℝ) ≤ OL := Nat.cast_nonneg _
  have hORn : (0 : ℝ) ≤ OR := Nat.cast_nonneg _
  have hpn : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hmρ : 0 ≤ (m : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hjρ : 0 ≤ (j : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have goal : ((((j+1+m : ℕ) : ℝ) - 1) * ρ) = j * ρ + m * ρ := by push_cast; ring
  have h2 : ((2 * p : ℕ) : ℝ) / 2 = p := by push_cast; ring
  rw [goal, h2] at hpos ⊢
  rcases max_cases 0 ((OL : ℝ) + j*ρ - p) with ⟨c1, _⟩ | ⟨c1, _⟩ <;>
    rcases max_cases 0 ((OR : ℝ) + m*ρ - p) with ⟨c2, _⟩ | ⟨c2, _⟩ <;>
    · rw [c1] at hx; rw [c2] at hy; linarith


end BW

/-! ### Native intervals -/

section Native

variable {d tf : ℕ}

theorem ancestor_zero_eq (b : KBag 64 d) : b.ancestor 0 = b := by
  apply KBag.ext <;> simp [KBag.ancestor]

/-- `strangers 1` is the number of non-native keys. -/
theorem strangers_one_eq (b : KBag 64 d) (S : Finset (Fin (64 ^ d))) :
    b.strangers 1 id S = (S.filter fun κ => ¬ b.Native κ id).card := by
  unfold KBag.strangers
  congr 1
  apply Finset.filter_congr
  intro κ _
  simp [KBag.Strange, ancestor_zero_eq]

theorem pow_sub_succ (d l : ℕ) (hl : l < d) : (64 : ℕ) ^ (d - l) = 64 * 64 ^ (d - l - 1) := by
  rw [← pow_succ' ]; congr 1; omega

theorem native_child_iff (q : KBag 64 d) (hq : q.l < d) (j : ℕ) (hj : j < 64)
    (κ : Fin (64 ^ d)) :
    (q.child j hj hq).Native κ id ↔
      q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) ≤ κ.val ∧
        κ.val < q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  have e2 : d - (q.l + 1) = d - q.l - 1 := by omega
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, KBag.child, id, e2]
  have h1 : (64 * q.x + j) * 64 ^ (d - q.l - 1) =
      q.x * 64 ^ (d - q.l) + j * 64 ^ (d - q.l - 1) := by rw [e]; ring
  have h2 : (64 * q.x + j + 1) * 64 ^ (d - q.l - 1) =
      q.x * 64 ^ (d - q.l) + (j + 1) * 64 ^ (d - q.l - 1) := by rw [e]; ring
  rw [h1, h2]

theorem native_self_iff (q : KBag 64 d) (hq : q.l < d) (κ : Fin (64 ^ d)) :
    q.Native κ id ↔
      q.x * 64 ^ (d - q.l) ≤ κ.val ∧
        κ.val < q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) := by
  rw [KBag.native_iff _ _ _ (by norm_num)]
  have e := pow_sub_succ d q.l hq
  simp only [KBag.lo, KBag.hi, KBag.size, bagSize, id]
  have h2 : (q.x + 1) * 64 ^ (d - q.l) = q.x * 64 ^ (d - q.l) + 64 * 64 ^ (d - q.l - 1) := by
    rw [← e]; ring
  rw [h2]

end Native

/-! ### Transfer from `Fin M` keys to `ℕ` keys -/

section Transfer

variable {M : ℕ}

theorem card_filter_val (K : Finset (Fin M)) (P : ℕ → Prop) [DecidablePred P] :
    ((K.image Fin.val).filter P).card = (K.filter fun κ => P κ.val).card := by
  rw [Finset.filter_image, Finset.card_image_of_injective _ Fin.val_injective]

theorem rankN_val (K : Finset (Fin M)) (κ : Fin M) :
    BW.rankN (K.image Fin.val) κ.val = rk K κ := by
  unfold BW.rankN rk
  rw [card_filter_val K (fun m => m < κ.val)]
  rfl

end Transfer

/-- The key-level window count for `Fin` keys (Lemma 4.2 sorted part, with Lemma 4.1 as `hM`). -/
theorem window_real {d : ℕ} (K : Finset (Fin (64 ^ d))) (q : KBag 64 d) (hq : q.l < d)
    (j : Fin 64) (π τ : ℕ) (hKc : K.card = π + 64 * τ) (hπ : 2 ∣ π) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hM : ∀ j' : Fin 64,
      ((K.filter fun κ => (q.child j'.val j'.isLt hq).Native κ id).card : ℝ) ≤ τ + ρ)
    (hpos : (π : ℝ) / 2 ≤ (q.strangers 1 id K : ℝ) + 63 * ρ) :
    ((K.filter fun κ => π / 2 + j.val * τ ≤ rk K κ ∧ rk K κ < π / 2 + j.val * τ + τ ∧
        ¬ (q.child j.val j.isLt hq).Native κ id).card : ℝ) ≤
      (q.strangers 1 id K : ℝ) + 63 * ρ - π / 2 := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = 64 ^ (d - q.l - 1) := ⟨_, rfl⟩
  obtain ⟨Ulo, hUlo⟩ : ∃ U : ℕ, U = q.x * 64 ^ (d - q.l) := ⟨_, rfl⟩
  have e := pow_sub_succ d q.l hq
  have hOL : ((K.image Fin.val).filter (· < Ulo)).card = (K.filter fun κ => κ.val < Ulo).card :=
    card_filter_val K (fun m => m < Ulo)
  have hOR : ((K.image Fin.val).filter (Ulo + 64 * S ≤ ·)).card =
      (K.filter fun κ => Ulo + 64 * S ≤ κ.val).card :=
    card_filter_val K (fun m => Ulo + 64 * S ≤ m)
  have hstr : (q.strangers 1 id K : ℝ) =
      (((K.image Fin.val).filter (· < Ulo)).card : ℝ) +
        (((K.image Fin.val).filter (Ulo + 64 * S ≤ ·)).card : ℝ) := by
    rw [hOL, hOR, strangers_one_eq, ← Nat.cast_add]
    congr 1
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext κ
      simp only [Finset.mem_filter, Finset.mem_union, native_self_iff q hq]
      simp only [← hS, ← hUlo]
      by_cases hk : κ ∈ K
      · simp only [hk, true_and]; omega
      · simp [hk]
    · rw [Finset.disjoint_filter]
      intro κ _ h1 h2
      omega
  have hcard : (K.image Fin.val).card = π + 64 * τ := by
    rw [Finset.card_image_of_injective _ Fin.val_injective]; exact hKc
  have hM' : ∀ j' < 64, (((K.image Fin.val).filter fun κ =>
      Ulo + j' * S ≤ κ ∧ κ < Ulo + (j' + 1) * S).card : ℝ) ≤ τ + ρ := by
    intro j' hj'
    rw [card_filter_val K (fun m => Ulo + j' * S ≤ m ∧ m < Ulo + (j' + 1) * S)]
    have := hM ⟨j', hj'⟩
    convert this using 3
    ext κ
    simp only [Finset.mem_filter]
    simp only [native_child_iff q hq j' hj', ← hS, ← hUlo]
  have hpos' : (π : ℝ) / 2 ≤ (((K.image Fin.val).filter (· < Ulo)).card : ℝ) +
      (((K.image Fin.val).filter (Ulo + 64 * S ≤ ·)).card : ℝ) + (((64 : ℕ) : ℝ) - 1) * ρ := by
    have h63 : ((64 : ℕ) : ℝ) - 1 = 63 := by norm_num
    rw [h63, ← hstr]; exact hpos
  have key := BW.window_wrong_le (K.image Fin.val) 64 π τ S Ulo j.val j.isLt hcard hπ ρ hρ hM'
    hpos'
  rw [← hstr] at key
  have hfilt := card_filter_val K (fun m => π / 2 + j.val * τ ≤ BW.rankN (K.image Fin.val) m ∧
    BW.rankN (K.image Fin.val) m < π / 2 + (j.val + 1) * τ ∧
      ¬ (Ulo + j.val * S ≤ m ∧ m < Ulo + (j.val + 1) * S))
  have heq : (K.filter fun κ => π / 2 + j.val * τ ≤ rk K κ ∧ rk K κ < π / 2 + j.val * τ + τ ∧
        ¬ (q.child j.val j.isLt hq).Native κ id) =
      K.filter fun κ => π / 2 + j.val * τ ≤ BW.rankN (K.image Fin.val) κ.val ∧
        BW.rankN (K.image Fin.val) κ.val < π / 2 + (j.val + 1) * τ ∧
          ¬ (Ulo + j.val * S ≤ κ.val ∧ κ.val < Ulo + (j.val + 1) * S) := by
    apply Finset.filter_congr
    intro κ _
    simp only [native_child_iff q hq j.val j.isLt, ← hS, ← hUlo]
    rw [rankN_val, Nat.add_mul (j.val) 1 τ, one_mul,
      add_assoc (π / 2)]
  rw [heq, ← hfilt]
  have : ((64 : ℕ) : ℝ) - 1 = 63 := by norm_num
  rw [this] at key
  exact key

/-! ### The real order-0 parent-send bound -/

section Main

variable {d tf : ℕ}

/-- **Lemma 4.2 (real network, order 0).**  Keys of `q` sent down to child `b = q.child j` in
stage `t` that are not addressed to `b`. -/
theorem bad_send0_real (F : FlowSizes d tf)
    (nets : ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Equiv.Perm (Fin (64 ^ d))) (t : ℕ) (ht : t < tf) (q : KBag 64 d) (hq : q.l < d)
    (j : Fin 64) (EB : ℝ) (Jmax : ℕ) (εF ρ : ℝ) (hρ : 0 ≤ ρ)
    (hspec : NodeSpec (wireSets F t q).card (F.up q.l t) (F.down q.l t)
      (nets t q (wireSets F t q).card) EB Jmax εF)
    (hM : ∀ j' : Fin 64,
      ((((execPlacement F nets v t ht.le).regs q).filter fun κ =>
        (q.child j'.val j'.isLt hq).Native κ id).card : ℝ) ≤ F.down q.l t + ρ)
    (hpos : (F.up q.l t : ℝ) / 2 ≤
      (q.strangers 1 id ((execPlacement F nets v t ht.le).regs q) : ℝ) + 63 * ρ) :
    (((q.child j.val j.isLt hq).strangers 1 id
        (fromParentK F nets v t (q.child j.val j.isLt hq)) : ℕ) : ℝ) ≤
      (q.strangers 1 id ((execPlacement F nets v t ht.le).regs q) : ℝ) + 63 * ρ -
        (F.up q.l t : ℝ) / 2 + 2 * EB := by
  classical
  have hπ : 2 ∣ F.up q.l t := F.hup_even q.l t ht
  have hsplit := F.hsplit q.l t q.hl ht
  have hcardS : (wireSets F t q).card = F.a q.l t := wireSets_card F ht.le q
  have ha : (wireSets F t q).card = F.up q.l t + 64 * F.down q.l t := by rw [hcardS, hsplit]
  set K := (execPlacement F nets v t ht.le).regs q with hK
  have hKc : K.card = F.up q.l t + 64 * F.down q.l t := by
    rw [hK, execPlacement_card F nets v t ht.le q, ← hsplit]
  let xr : Fin (wireSets F t q).card → Fin (64 ^ d) := fun i =>
    X F nets v t ((wireSets F t q).orderEmbOfFin rfl i)
  have hxr : Function.Injective xr :=
    (X_injective F nets v t).comp ((wireSets F t q).orderEmbOfFin rfl).injective
  have hkey : keySet xr = K := by
    ext κ
    simp only [keySet, Finset.mem_image, Finset.mem_univ, true_and, hK, execPlacement]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨c, rfl⟩ := exists_orderEmb_eq hw
      exact ⟨c, rfl⟩
  -- the set of keys sent to child `j`
  set b := q.child j.val j.isLt hq with hb
  have hbp : b.parent = q := KBag.parent_child' q j.val j.isLt hq
  have hbl : b.l - 1 = q.l := by simp [hb, KBag.child]
  have hbx : b.x % 64 = j.val := by
    show (64 * q.x + j.val) % 64 = j.val
    omega
  have hW : fromParentK F nets v t b =
      ((Finset.univ : Finset (Fin (wireSets F t q).card)).filter fun c =>
        F.up q.l t / 2 + j.val * F.down q.l t ≤ c.val ∧
          c.val < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t).image
        ((nets t q (wireSets F t q).card).exec xr) := by
    unfold fromParentK
    rw [hbp, hbl, hbx]
    ext κ
    rw [mem_image_downSet_iff F nets v t ht q]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, h1, h2, rfl⟩
      exact ⟨c, ⟨h1, by rw [Nat.add_mul, one_mul, ← add_assoc] at h2; exact h2⟩, rfl⟩
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      exact ⟨c, h1, by rw [Nat.add_mul, one_mul, ← add_assoc]; exact h2, rfl⟩
  rw [hW, strangers_one_eq]
  set Wn := ((Finset.univ : Finset (Fin (wireSets F t q).card)).filter fun c =>
        F.up q.l t / 2 + j.val * F.down q.l t ≤ c.val ∧
          c.val < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t).image
        ((nets t q (wireSets F t q).card).exec xr) with hWn
  have hWK : ∀ κ ∈ Wn, κ ∈ K := by
    intro κ hκ
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hκ
    rw [← hkey]; exact exec_mem_keySet _ c
  have hI := hspec.intruder_keys hxr ha hπ j.val j.isLt
  rw [hkey] at hI
  have hsub : (Wn.filter fun κ => ¬ b.Native κ id) ⊆
      (Wn.filter fun κ => ¬ (F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t)) ∪
      (K.filter fun κ => F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t ∧
            ¬ b.Native κ id) := by
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_union] at hκ ⊢
    by_cases hw : F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
        rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t
    · exact Or.inr ⟨hWK κ hκ.1, hw.1, hw.2, hκ.2⟩
    · exact Or.inl ⟨hκ.1, hw⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    (Wn.filter fun κ => ¬ (F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t))
    (K.filter fun κ => F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t ∧
            ¬ b.Native κ id)
  have h3 := window_real K q hq j (F.up q.l t) (F.down q.l t) hKc hπ ρ hρ hM hpos
  have h4 : (((Wn.filter fun κ => ¬ b.Native κ id).card : ℕ) : ℝ) ≤
      ((Wn.filter fun κ => ¬ (F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t)).card : ℝ) +
      ((K.filter fun κ => F.up q.l t / 2 + j.val * F.down q.l t ≤ rk K κ ∧
          rk K κ < F.up q.l t / 2 + j.val * F.down q.l t + F.down q.l t ∧
            ¬ b.Native κ id).card : ℝ) := by
    exact_mod_cast h1.trans h2
  linarith

end Main

end Chvatal
