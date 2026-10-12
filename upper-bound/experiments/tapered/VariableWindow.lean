import AKS.Chvatal.BadSendReal
import AKS.Chvatal.Lemma41Real
import SignedReserve
import Mathlib.Tactic

namespace Chvatal.BW

/-- A lower key tail can be charged to the entire non-native population plus
the part of the native interval below the cut. This is the elementary input
set estimate needed before applying the variable-window rank lemma; it makes
no assumption on how the outsider keys are distributed. -/
theorem prefix_count_le_of_outsider_budget
    (K N : Finset ℕ) (lo : ℕ) (O J : ℝ)
    (hPrefix : ((N.filter (· < lo)).card : ℝ) ≤ J)
    (hOutside : ((K.filter (fun κ => κ ∉ N)).card : ℝ) ≤ O) :
    ((K.filter (· < lo)).card : ℝ) ≤ O + J := by
  let L := K.filter (· < lo)
  let P := N.filter (· < lo)
  let X := K.filter (fun κ => κ ∉ N)
  have hsub : L ⊆ P ∪ X := by
    intro κ hκ
    simp only [L, Finset.mem_filter] at hκ
    simp only [Finset.mem_union, P, X, Finset.mem_filter]
    by_cases hn : κ ∈ N
    · exact Or.inl ⟨hn, hκ.2⟩
    · exact Or.inr ⟨hκ.1, hn⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le P X)
  have hreal : (L.card : ℝ) ≤ (P.card : ℝ) + (X.card : ℝ) := by
    exact_mod_cast hcard
  have hP : (P.card : ℝ) ≤ J := by simpa [P] using hPrefix
  have hX : (X.card : ℝ) ≤ O := by simpa [X] using hOutside
  simpa [L, add_comm] using le_trans hreal (add_le_add hP hX)

/-- The dual upper key-tail estimate. -/
theorem suffix_count_le_of_outsider_budget
    (K N : Finset ℕ) (hi : ℕ) (O J : ℝ)
    (hSuffix : ((N.filter (hi ≤ ·)).card : ℝ) ≤ J)
    (hOutside : ((K.filter (fun κ => κ ∉ N)).card : ℝ) ≤ O) :
    ((K.filter (hi ≤ ·)).card : ℝ) ≤ O + J := by
  let R := K.filter (hi ≤ ·)
  let P := N.filter (hi ≤ ·)
  let X := K.filter (fun κ => κ ∉ N)
  have hsub : R ⊆ P ∪ X := by
    intro κ hκ
    simp only [R, Finset.mem_filter] at hκ
    simp only [Finset.mem_union, P, X, Finset.mem_filter]
    by_cases hn : κ ∈ N
    · exact Or.inl ⟨hn, hκ.2⟩
    · exact Or.inr ⟨hκ.1, hn⟩
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le P X)
  have hreal : (R.card : ℝ) ≤ (P.card : ℝ) + (X.card : ℝ) := by
    exact_mod_cast hcard
  have hP : (P.card : ℝ) ≤ J := by simpa [P] using hSuffix
  have hX : (X.card : ℝ) ≤ O := by simpa [X] using hOutside
  simpa [R, add_comm] using le_trans hreal (add_le_add hP hX)

/-- Split a lower tail at a reference interval boundary. The only extra keys
are among the `cut - L` natural numbers in the intervening interval. -/
theorem prefix_count_le_of_cut
    (K : Finset ℕ) (L cut : ℕ) (hcut : L ≤ cut) :
    (K.filter (· < cut)).card ≤ (K.filter (· < L)).card + (cut - L) := by
  have hsplit := Chvatal.BW.card_lt_split K hcut
  have hsub : K.filter (fun κ => L ≤ κ ∧ κ < cut) ⊆ Finset.Ico L cut := by
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_Ico] at hκ ⊢
    exact hκ.2
  have hcard := Finset.card_le_card hsub
  have hIco : (Finset.Ico L cut).card = cut - L := by simp
  rw [hsplit]
  rw [hIco] at hcard
  omega

/-- The dual upper-tail estimate, split at the upper end of a reference
interval. -/
theorem suffix_count_le_of_cut
    (K : Finset ℕ) (cut H : ℕ) (hcut : cut ≤ H) :
    (K.filter (cut ≤ ·)).card ≤ (H - cut) + (K.filter (H ≤ ·)).card := by
  have hunion : K.filter (cut ≤ ·) =
      K.filter (fun κ => cut ≤ κ ∧ κ < H) ∪ K.filter (H ≤ ·) := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hκ, hlo⟩
      by_cases hhi : κ < H
      · exact Or.inl ⟨hκ, hlo, hhi⟩
      · exact Or.inr ⟨hκ, le_of_not_gt hhi⟩
    · rintro (⟨hκ, hlo, _⟩ | ⟨hκ, hhi⟩)
      · exact ⟨hκ, hlo⟩
      · exact ⟨hκ, le_trans hcut hhi⟩
  have hsplit : (K.filter (cut ≤ ·)).card =
      (K.filter (fun κ => cut ≤ κ ∧ κ < H)).card + (K.filter (H ≤ ·)).card := by
    rw [hunion, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro κ hleft hright
    simp only [Finset.mem_filter] at hleft hright
    omega
  rw [hsplit]
  have hsub : K.filter (fun κ => cut ≤ κ ∧ κ < H) ⊆ Finset.Ico cut H := by
    intro κ hκ
    simp only [Finset.mem_filter, Finset.mem_Ico] at hκ ⊢
    exact hκ.2
  have hcard := Finset.card_le_card hsub
  have hIco : (Finset.Ico cut H).card = H - cut := by simp
  omega

/-- Convert a prefix-width inequality into the left cumulative-tail premise
of `variable_window_wrong_le`. The baseline `OL` is the number of keys below
the parent native interval. -/
theorem prefix_tail_budget_of_width
    (K : Finset ℕ) (U S j pre : ℕ) (OL rho x : ℝ)
    (hBase : ((K.filter (· < U)).card : ℝ) ≤ OL)
    (hWidth : (j * S : ℝ) ≤ (pre : ℝ) + j * rho + x) :
    ((K.filter (· < U + j * S)).card : ℝ) ≤
      OL + pre + j * rho + x := by
  have hcut := prefix_count_le_of_cut K U (U + j * S) (by omega)
  have hnat : U + j * S - U = j * S := by omega
  have hcutR : ((K.filter (· < U + j * S)).card : ℝ) ≤
      ((K.filter (· < U)).card : ℝ) + (j * S : ℝ) := by
    have hcut' := hcut
    rw [hnat] at hcut'
    exact_mod_cast hcut'
  linarith

/-- The right-tail counterpart, using the parent native interval's upper end. -/
theorem suffix_tail_budget_of_width
    (K : Finset ℕ) (U S j post : ℕ) (OR rho x : ℝ)
    (hBase : ((K.filter (U + 64 * S ≤ ·)).card : ℝ) ≤ OR)
    (hWidth : ((63 - j) * S : ℝ) ≤ (post : ℝ) + (63 - j) * rho + x)
    (hj : j ≤ 63) :
    ((K.filter (U + (j + 1) * S ≤ ·)).card : ℝ) ≤
      OR + post + (63 - j) * rho + x := by
  have hhi : U + (j + 1) * S ≤ U + 64 * S := by
    have : j + 1 ≤ 64 := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right S this) U
  have hcut := suffix_count_le_of_cut K (U + (j + 1) * S) (U + 64 * S) hhi
  have hjmul : (j + 1) * S = j * S + S := by
    rw [Nat.add_mul]
    simp
  have hnat : U + 64 * S - (U + (j + 1) * S) = (63 - j) * S := by
    rw [hjmul]
    have hcoeff : 64 = j + 1 + (63 - j) := by omega
    have hmul : 64 * S = j * S + S + (63 - j) * S := by
      calc
        64 * S = (j + 1 + (63 - j)) * S := by rw [hcoeff]
        _ = (j + 1) * S + (63 - j) * S := Nat.add_mul _ _ _
        _ = j * S + S + (63 - j) * S := by rw [Nat.add_mul]; simp [Nat.add_assoc]
    rw [hmul]
    omega
  have hcutR : ((K.filter (U + (j + 1) * S ≤ ·)).card : ℝ) ≤
      ((U + 64 * S - (U + (j + 1) * S) : ℕ) : ℝ) +
        ((K.filter (U + 64 * S ≤ ·)).card : ℝ) := by
    exact_mod_cast hcut
  rw [hnat] at hcutR
  have hsubcast : ((63 - j : ℕ) : ℝ) = 63 - j := by
    rw [Nat.cast_sub hj]
    norm_num
  push_cast at hcutR hWidth
  rw [hsubcast] at hcutR
  linarith

/-- Accumulate per-slot bounds across an initial segment of equal native address intervals.
Output widths may vary, and the real per-slot errors may be signed. -/
theorem prefix_slots_count_le
    (K : Finset ℕ) (U S n : ℕ) (tau : ℕ → ℕ) (err : ℕ → ℝ)
    (hM : ∀ j < n,
      ((K.filter fun κ => U + j * S ≤ κ ∧ κ < U + (j + 1) * S).card : ℝ) ≤
        (tau j : ℝ) + err j) :
    ((K.filter (· < U + n * S)).card : ℝ) ≤
      ((K.filter (· < U)).card : ℝ) +
        ∑ j ∈ Finset.range n, ((tau j : ℝ) + err j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj => hM j (by omega))
    have hmul : n * S ≤ (n + 1) * S := Nat.mul_le_mul_right S (Nat.le_succ n)
    have hcut : U + n * S ≤ U + (n + 1) * S := Nat.add_le_add_left hmul U
    have hsplit := card_lt_split K hcut
    have hsplitR :
        ((K.filter (· < U + (n + 1) * S)).card : ℝ) =
          ((K.filter (· < U + n * S)).card : ℝ) +
            ((K.filter fun κ => U + n * S ≤ κ ∧ κ < U + (n + 1) * S).card : ℝ) := by
      exact_mod_cast hsplit
    have hslot := hM n (by omega)
    rw [hsplitR, Finset.sum_range_succ]
    linarith

/-- Split an interval at an intermediate address cut. -/
theorem card_interval_split (K : Finset ℕ) (lo mid hi : ℕ)
    (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    (K.filter fun κ => lo ≤ κ ∧ κ < hi).card =
      (K.filter fun κ => lo ≤ κ ∧ κ < mid).card +
        (K.filter fun κ => mid ≤ κ ∧ κ < hi).card := by
  have hunion : K.filter (fun κ => lo ≤ κ ∧ κ < hi) =
      K.filter (fun κ => lo ≤ κ ∧ κ < mid) ∪
        K.filter (fun κ => mid ≤ κ ∧ κ < hi) := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hκ, hlow, hhigh⟩
      by_cases hm : κ < mid
      · exact Or.inl ⟨hκ, hlow, hm⟩
      · exact Or.inr ⟨hκ, by omega, hhigh⟩
    · rintro (⟨hκ, hlow, hm⟩ | ⟨hκ, hm, hhigh⟩)
      · exact ⟨hκ, hlow, lt_of_lt_of_le hm h₂⟩
      · exact ⟨hκ, le_trans h₁ hm, hhigh⟩
  rw [hunion, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro κ hleft hright
  simp only [Finset.mem_filter] at hleft hright
  omega

/-- Count any consecutive range of equal address slots using its separate slot bounds. -/
theorem interval_slots_count_le
    (K : Finset ℕ) (U S m n : ℕ) (tau : ℕ → ℕ) (err : ℕ → ℝ)
    (hM : ∀ j,
      ((K.filter fun κ => U + j * S ≤ κ ∧ κ < U + (j + 1) * S).card : ℝ) ≤
        (tau j : ℝ) + err j) :
    ((K.filter fun κ => U + m * S ≤ κ ∧ κ < U + (m + n) * S).card : ℝ) ≤
      ∑ r ∈ Finset.range n, ((tau (m + r) : ℝ) + err (m + r)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hidx : m + (n + 1) = m + n + 1 := by omega
    have hmul : (m + n) * S ≤ (m + n + 1) * S :=
      Nat.mul_le_mul_right S (Nat.le_succ (m + n))
    have hmid : U + (m + n) * S ≤ U + (m + n + 1) * S :=
      Nat.add_le_add_left hmul U
    have hstart : U + m * S ≤ U + (m + n) * S := by
      have hmle : m ≤ m + n := Nat.le_add_right m n
      exact Nat.add_le_add_left (Nat.mul_le_mul_right S hmle) U
    have hsplit := card_interval_split K (U + m * S) (U + (m + n) * S)
      (U + (m + n + 1) * S) hstart hmid
    have hsplitR :
        ((K.filter fun κ => U + m * S ≤ κ ∧ κ < U + (m + n + 1) * S).card : ℝ) =
          ((K.filter fun κ => U + m * S ≤ κ ∧ κ < U + (m + n) * S).card : ℝ) +
            ((K.filter fun κ => U + (m + n) * S ≤ κ ∧ κ < U + (m + n + 1) * S).card : ℝ) := by
      exact_mod_cast hsplit
    have hslot := hM (m + n)
    rw [hidx, hsplitR, Finset.sum_range_succ]
    linarith

/-- Split a set's upper tail into a finite interval and the tail beyond it. -/
theorem card_ge_split (K : Finset ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (K.filter (lo ≤ ·)).card =
      (K.filter fun κ => lo ≤ κ ∧ κ < hi).card + (K.filter (hi ≤ ·)).card := by
  have hunion : K.filter (lo ≤ ·) =
      K.filter (fun κ => lo ≤ κ ∧ κ < hi) ∪ K.filter (hi ≤ ·) := by
    ext κ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hκ, hlo⟩
      by_cases hhi : κ < hi
      · exact Or.inl ⟨hκ, hlo, hhi⟩
      · exact Or.inr ⟨hκ, by omega⟩
    · rintro (⟨hκ, hlo, _⟩ | ⟨hκ, hhi⟩)
      · exact ⟨hκ, hlo⟩
      · exact ⟨hκ, le_trans hle hhi⟩
  rw [hunion, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro κ hleft hright
  simp only [Finset.mem_filter] at hleft hright
  omega

/-- Bound a right tail by the outsiders beyond the complete native interval and the remaining
per-slot allowances. -/
theorem suffix_slots_count_le
    (K : Finset ℕ) (U S k j : ℕ) (tau : ℕ → ℕ) (err : ℕ → ℝ)
    (hj : j < k)
    (hM : ∀ h,
      ((K.filter fun κ => U + h * S ≤ κ ∧ κ < U + (h + 1) * S).card : ℝ) ≤
        (tau h : ℝ) + err h) :
    ((K.filter (U + (j + 1) * S ≤ ·)).card : ℝ) ≤
      ((K.filter (U + k * S ≤ ·)).card : ℝ) +
        ∑ r ∈ Finset.range (k - (j + 1)),
          ((tau (j + 1 + r) : ℝ) + err (j + 1 + r)) := by
  let m := j + 1
  let n := k - (j + 1)
  have hmn : m + n = k := by dsimp [m, n]; omega
  have hcuts : U + m * S ≤ U + k * S := by
    have hmle : m ≤ k := by omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right S hmle) U
  have hsplit := card_ge_split K (U + m * S) (U + k * S) hcuts
  have hinterval := interval_slots_count_le K U S m n tau err hM
  have hsum :
      ∑ r ∈ Finset.range n, ((tau (m + r) : ℝ) + err (m + r)) =
        ∑ r ∈ Finset.range n, ((tau (j + 1 + r) : ℝ) + err (j + 1 + r)) := by
    simp [m]
  have hsplitR :
      ((K.filter (U + m * S ≤ ·)).card : ℝ) =
        ((K.filter fun κ => U + m * S ≤ κ ∧ κ < U + k * S).card : ℝ) +
          ((K.filter (U + k * S ≤ ·)).card : ℝ) := by
    exact_mod_cast hsplit
  rw [show U + (j + 1) * S = U + m * S by rfl, hsplitR]
  rw [hmn] at hinterval
  rw [hsum] at hinterval
  linarith

/-- The bounded signed correction has an address-independent next occupancy whenever the
centered child corrections sum to zero. -/
theorem signed_child_debt_sum (q : Fin 64 → ℝ) (C e : ℝ)
    (hq : ∑ j : Fin 64, q j = 0) :
    (∑ j : Fin 64, (q j * C + e / 64)) = e := by
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq]
  simp
  field_simp

theorem signed_flow_occupancy_uniform
    (q : Fin 64 → ℝ) (parentCap A rbar s rj qj e : ℝ)
    (hq : ∑ l : Fin 64, q l = 0)
    (hr : rj - qj = rbar) :
    (rj * parentCap + e / 64) +
      (∑ l : Fin 64,
        (s * A ^ 2 * parentCap -
          (q l * (A * parentCap) + (qj * parentCap + e / 64) / 64))) =
      (rbar + 64 * s * A ^ 2) * parentCap := by
  have hdebt := signed_child_debt_sum q (A * parentCap) (qj * parentCap + e / 64) hq
  have hconst : (∑ _l : Fin 64, (s * A ^ 2 * parentCap : ℝ)) =
      64 * (s * A ^ 2 * parentCap) := by simp
  rw [Finset.sum_sub_distrib, hconst, hdebt]
  calc
    (rj * parentCap + e / 64) +
        (64 * (s * A ^ 2 * parentCap) - (qj * parentCap + e / 64)) =
        (rj - qj + 64 * s * A ^ 2) * parentCap := by ring
    _ = (rbar + 64 * s * A ^ 2) * parentCap := by rw [hr]

/-- Unequal-width sorted-window estimate with the left and right tails kept separate.
`pre` and `post` are output widths before and after the target child; `dLeft` and `dRight`
are real upper errors in the corresponding cumulative native-slot counts. -/
theorem variable_window_wrong_le
    (K : Finset ℕ) (p pre tau post : ℕ) (lo hi : ℕ)
    (OL OR dLeft dRight : ℝ)
    (hcard : K.card = 2 * p + pre + tau + post)
    (hL : ((K.filter (· < lo)).card : ℝ) ≤ OL + pre + dLeft)
    (hR : ((K.filter (hi ≤ ·)).card : ℝ) ≤ OR + post + dRight) :
    ((K.filter fun κ => p + pre ≤ rankN K κ ∧
        rankN K κ < p + pre + tau ∧ ¬ (lo ≤ κ ∧ κ < hi)).card : ℝ) ≤
      max 0 (OL + dLeft - p) + max 0 (OR + dRight - p) := by
  set L := (K.filter (· < lo)).card
  set R := (K.filter (hi ≤ ·)).card
  have hsτ : p + pre + tau ≤ K.card := by omega
  have hT : K.card - (p + pre) - tau = p + post := by omega
  have hW := sorted_window_wrong_le K (p + pre) tau lo hi hsτ
  rw [hT] at hW
  have hx : ((L - (p + pre) : ℕ) : ℝ) ≤ max 0 (OL + dLeft - p) := by
    by_cases h : L ≤ p + pre
    · rw [Nat.sub_eq_zero_of_le h]
      simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by dsimp [L] at hL; linarith)
  have hy : ((R - (p + post) : ℕ) : ℝ) ≤ max 0 (OR + dRight - p) := by
    by_cases h : R ≤ p + post
    · rw [Nat.sub_eq_zero_of_le h]
      simp
    · rw [Nat.cast_sub (by omega)]
      push_cast
      exact le_max_of_le_right (by dsimp [R] at hR; linarith)
  have hWr :
      ((K.filter fun κ => p + pre ≤ rankN K κ ∧
        rankN K κ < p + pre + tau ∧ ¬ (lo ≤ κ ∧ κ < hi)).card : ℝ) ≤
        ((L - (p + pre) : ℕ) : ℝ) + ((R - (p + post) : ℕ) : ℝ) := by
    exact_mod_cast hW
  linarith

/-- The native-slot estimate reduces to a local subtree-mass identity and an outsider bound.
`C` is the reference capacity of `u`; the subtree mass is the complement of `C/64` in one
native child interval. This does not assume bag sizes depend only on depth. -/
theorem native_child_count_from_subtree_budget
    {d : ℕ} (pl : Placement 64 d) (u : KBag 64 d) (hu : u.l < d)
    (j : Fin 64) (C B : ℝ)
    (hMass : ((subtreeKeys 64 d pl (by norm_num) (u.child j.val j.isLt hu)).card : ℝ) =
      ((64 : ℝ) ^ d / 64 ^ u.l - C) / 64)
    (hBad : (((subtreeKeys 64 d pl (by norm_num) (u.child j.val j.isLt hu)).filter
      fun κ => ¬ (u.child j.val j.isLt hu).Native κ id).card : ℝ) ≤ B) :
    (((pl.regs u).filter fun κ => (u.child j.val j.isLt hu).Native κ id).card : ℝ) ≤
      C / 64 + B := by
  let w := u.child j.val j.isLt hu
  set S := subtreeKeys 64 d pl (by norm_num) w with hSdef
  let X := (pl.regs u).filter fun κ => w.Native κ id
  let Y := S.filter fun κ => w.Native κ id
  let Z := (Finset.univ : Finset (Fin (64 ^ d))).filter fun κ => w.Native κ id
  have hAcard : Z.card = 64 ^ (d - u.l - 1) := by
    change (Finset.univ.filter fun κ : Fin (64 ^ d) => w.Native κ id).card = _
    have h := native_card (by norm_num : 1 ≤ 64) w
    rw [show w.l = u.l + 1 from rfl,
      show d - (u.l + 1) = d - u.l - 1 by omega] at h
    exact h
  have hdisj : Disjoint (pl.regs u) S := by
    rw [hSdef, subtreeKeys, subtreeBags, Finset.disjoint_biUnion_right]
    intro z hz
    apply pl.disjoint u z
    intro heq
    have hlevel := subtreeBags_l_ge (by norm_num : 1 ≤ 64) w z hz
    rw [← heq] at hlevel
    have hwlevel : w.l = u.l + 1 := rfl
    omega
  have hXY : X.card + Y.card ≤ Z.card := by
    have hXYdisj : Disjoint X Y :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _)
        (Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdisj)
    rw [← Finset.card_union_of_disjoint hXYdisj]
    apply Finset.card_le_card
    intro κ hκ
    rcases Finset.mem_union.mp hκ with hx | hy
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun κ => w.Native κ id)
  have hZ : (Z.card : ℝ) = (64 : ℝ) ^ d / 64 ^ u.l / 64 := by
    rw [hAcard]
    push_cast
    have hpow : (64 : ℝ) ^ d = (64 : ℝ) ^ (d - u.l - 1) * 64 * (64 : ℝ) ^ u.l := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega
    rw [hpow]
    field_simp
  have hS : (S.card : ℝ) = ((64 : ℝ) ^ d / 64 ^ u.l - C) / 64 := by
    simpa [S, w] using hMass
  have hX : (X.card : ℝ) + (Y.card : ℝ) ≤ Z.card := by exact_mod_cast hXY
  have hYbad : (Y.card : ℝ) + ((S.filter fun κ => ¬ w.Native κ id).card : ℝ) = S.card := by
    exact_mod_cast hsplit
  have hBad' : ((S.filter fun κ => ¬ w.Native κ id).card : ℝ) ≤ B := by
    simpa [S, w] using hBad
  change (X.card : ℝ) ≤ C / 64 + B
  linarith

/-- The unequal-width window bound with the signed-flow reserve discharged.
The only remaining inputs are the two actual cumulative native-slot counts;
this theorem supplies the mathematical tail calculation once those counts
are established by the schedule-specific outsider induction. -/
theorem max_outsider_add_le (O x : ℝ) (hO : 0 ≤ O) :
    max 0 (O + x) ≤ O + max 0 x := by
  by_cases hx : 0 ≤ x
  · have hOx : 0 ≤ O + x := add_nonneg hO hx
    rw [max_eq_right hOx, max_eq_right hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hsum : O + x ≤ O := by linarith
    have hmax : max 0 (O + x) ≤ O := max_le hO hsum
    rw [max_eq_left hx']
    linarith

theorem variable_window_wrong_le_signed_path
    (K : Finset ℕ) (p pre tau post lo hi : ℕ)
    (OL OR rho : ℝ) (C : Rat) (j : Nat) (qs : List Rat)
    (hcard : K.card = 2 * p + pre + tau + post)
    (hC : 0 ≤ C) (hOL : 0 ≤ OL) (hOR : 0 ≤ OR) (hρ : 0 ≤ rho)
    (hj1 : 1 ≤ j) (hj62 : j ≤ 62)
    (hq : ∀ q ∈ qs, Tapered945.qEnd ≤ q ∧ q ≤ Tapered945.qMid)
    (hL : ((K.filter (· < lo)).card : ℝ) ≤
      OL + pre + j * rho + p + ((C / (2 * Tapered945.cap) +
        ((32 : Rat) - j) * Tapered945.debtPath qs * C / 64 : Rat) : ℝ))
    (hR : ((K.filter (hi ≤ ·)).card : ℝ) ≤
      OR + post + (63 - j) * rho + p + ((C / (2 * Tapered945.cap) +
        ((j : Rat) - 31) * Tapered945.debtPath qs * C / 64 : Rat) : ℝ)) :
    ((K.filter fun κ => p + pre ≤ rankN K κ ∧
      rankN K κ < p + pre + tau ∧ ¬ (lo ≤ κ ∧ κ < hi)).card : ℝ) ≤
      OL + OR + 63 * rho + ((Tapered945.reserve * C : Rat) : ℝ) := by
  let xL : ℝ := ((C / (2 * Tapered945.cap) +
    ((32 : Rat) - j) * Tapered945.debtPath qs * C / 64 : Rat) : ℝ)
  let xR : ℝ := ((C / (2 * Tapered945.cap) +
    ((j : Rat) - 31) * Tapered945.debtPath qs * C / 64 : Rat) : ℝ)
  have hj63 : j ≤ 63 := by omega
  have hsplitCount : (j : ℝ) * rho + ((63 - j : Nat) : ℝ) * rho = 63 * rho := by
    have hcast : (j : ℝ) + ((63 - j : Nat) : ℝ) = 63 := by
      exact_mod_cast Nat.add_sub_of_le hj63
    rw [← add_mul, hcast]
  have hL' : ((K.filter (· < lo)).card : ℝ) ≤
      OL + pre + ((p : ℝ) + (j : ℝ) * rho + xL) := by
    dsimp [xL]
    convert hL using 1 <;> push_cast <;> ring
  have hR' : ((K.filter (hi ≤ ·)).card : ℝ) ≤
      OR + post + ((p : ℝ) + ((63 - j : Nat) : ℝ) * rho + xR) := by
    dsimp [xR]
    convert hR using 1 <;> push_cast <;> rw [Nat.cast_sub hj63] <;> ring
  have hw := variable_window_wrong_le K p pre tau post lo hi OL OR
    ((p : ℝ) + (j : ℝ) * rho + xL)
    ((p : ℝ) + ((63 - j : Nat) : ℝ) * rho + xR) hcard hL' hR'
  have hOL' : 0 ≤ OL + (j : ℝ) * rho :=
    add_nonneg hOL (mul_nonneg (Nat.cast_nonneg _) hρ)
  have hOR' : 0 ≤ OR + ((63 - j : Nat) : ℝ) * rho :=
    add_nonneg hOR (mul_nonneg (Nat.cast_nonneg _) hρ)
  have htailL := max_outsider_add_le (OL + (j : ℝ) * rho) xL hOL'
  have htailR := max_outsider_add_le (OR + ((63 - j : Nat) : ℝ) * rho) xR hOR'
  have hreserve := Tapered945.signed_path_internal_reserve j C hC hj1 hj62 qs hq
  have hreserveR : max 0 xL + max 0 xR ≤ ((Tapered945.reserve * C : Rat) : ℝ) := by
    dsimp [xL, xR]
    exact_mod_cast hreserve
  have hargL : OL + ((p : ℝ) + (j : ℝ) * rho + xL) - (p : ℝ) =
      OL + (j : ℝ) * rho + xL := by ring
  have hargR : OR + ((p : ℝ) + ((63 - j : Nat) : ℝ) * rho + xR) - (p : ℝ) =
      OR + ((63 - j : Nat) : ℝ) * rho + xR := by ring
  rw [hargL, hargR] at hw
  have hsum := add_le_add htailL htailR
  apply hw.trans
  calc
    _ ≤ OL + (j : ℝ) * rho + max 0 xL +
        (OR + ((63 - j : Nat) : ℝ) * rho + max 0 xR) := hsum
    _ = OL + OR + ((j : ℝ) * rho + ((63 - j : Nat) : ℝ) * rho) +
        (max 0 xL + max 0 xR) := by ring
    _ ≤ OL + OR + 63 * rho + ((Tapered945.reserve * C : Rat) : ℝ) := by
      rw [hsplitCount]
      linarith [hreserveR]

/-- Endpoint-child version of the signed window argument. The endpoint has
only one surviving signed tail; the opposite tail is absorbed directly into
the nonnegative outsider count. -/
theorem endpoint_window_wrong_le_signed_path
    (K : Finset ℕ) (p pre tau post lo hi : ℕ)
    (OL OR rho : ℝ) (C : Rat) (qs : List Rat)
    (hcard : K.card = 2 * p + pre + tau + post)
    (hC : 0 ≤ C) (hOL : 0 ≤ OL) (hOR : 0 ≤ OR) (hρ : 0 ≤ rho)
    (hq : ∀ q ∈ qs, Tapered945.qEnd ≤ q ∧ q ≤ Tapered945.qMid)
    (hL : ((K.filter (· < lo)).card : ℝ) ≤ OL + pre)
    (hR : ((K.filter (hi ≤ ·)).card : ℝ) ≤
      OR + post + 63 * rho + p +
        ((C / (2 * Tapered945.cap) -
          31 * Tapered945.debtPath qs * C / 64 : Rat) : ℝ)) :
    ((K.filter fun κ => p + pre ≤ rankN K κ ∧
      rankN K κ < p + pre + tau ∧ ¬ (lo ≤ κ ∧ κ < hi)).card : ℝ) ≤
      OL + OR + 63 * rho + ((Tapered945.reserve * C : Rat) : ℝ) := by
  let x : ℝ := ((C / (2 * Tapered945.cap) -
    31 * Tapered945.debtPath qs * C / 64 : Rat) : ℝ)
  have hL' : ((K.filter (· < lo)).card : ℝ) ≤ OL + pre + 0 := by
    linarith [hL]
  have hR' : ((K.filter (hi ≤ ·)).card : ℝ) ≤
      OR + post + ((p : ℝ) + 63 * rho + x) := by
    dsimp [x]
    convert hR using 1 <;> push_cast <;> ring
  have hw := variable_window_wrong_le K p pre tau post lo hi OL OR
    (0 : ℝ) ((p : ℝ) + 63 * rho + x) hcard hL' hR'
  have hleft : max 0 (OL + (0 : ℝ) - p) ≤ OL := by
    apply max_le hOL
    linarith
  have hbaseR : 0 ≤ OR + 63 * rho := by positivity
  have hright := max_outsider_add_le (OR + 63 * rho) x hbaseR
  have hreserve := Tapered945.signed_path_endpoint_reserve C hC qs hq
  have hreserveR : max 0 x ≤ ((Tapered945.reserve * C : Rat) : ℝ) := by
    dsimp [x]
    exact_mod_cast hreserve
  have harg : OR + ((p : ℝ) + 63 * rho + x) - (p : ℝ) = OR + 63 * rho + x := by ring
  rw [harg] at hw
  have hsum := add_le_add hleft hright
  exact hw.trans (by linarith [hreserveR])

end Chvatal.BW
