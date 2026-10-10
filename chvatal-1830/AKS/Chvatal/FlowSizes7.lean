module

/-
  # Natural-number flow sizes for the §7 schedule (B2c + B2d)

  Shows that the rational allocation and flows of `FlowTable` at the §7 parameters
  (`k = 64`, `A = 4096`, `ν = 1/64`) are natural numbers for `2 ≤ t ≤ t_f`
  (and that the parent sends `π` are even), and adds the special steps `t = 0, 1`
  (DCS-TR-294 p. 6) to obtain `flowSizes7 d hd : FlowSizes d (tf7 d)`.

  With `capacity d i t = 64^(d+2i) / 64^(t+2)` and `capacityRatio = 64^6`,
  the exponent bounds `e(i,t) = d+2i-t-2 ≥ 3` (top), `≥ 6` (rising top), `≥ 7` (non-top)
  make every formula an explicit natural number.
-/

public import AKS.Chvatal.FlowTable

@[expose] public section

namespace Chvatal

/-- Natural-number flow sizes for `br = 64`, depth `d`, final time `tf`. -/
structure FlowSizes (d tf : Nat) where
  a : Nat → Nat → Nat
  up : Nat → Nat → Nat
  down : Nat → Nat → Nat
  ha_root : a 0 0 = 64 ^ d
  ha_init : ∀ l, 1 ≤ l → a l 0 = 0
  hup_even : ∀ l t, t < tf → 2 ∣ up l t
  hup_root : ∀ t, t < tf → up 0 t = 0
  hdown_leaf : ∀ t, t < tf → down d t = 0
  /-- A node sends out exactly its wires. -/
  hsplit : ∀ l t, l ≤ d → t < tf → a l t = up l t + 64 * down l t
  /-- Wires arriving at a node at time `t+1`: from its parent (if any) and its children. -/
  hcons : ∀ l t, l ≤ d → t < tf →
    a l (t + 1) = (if 1 ≤ l then down (l - 1) t else 0) + (if l < d then 64 * up (l + 1) t else 0)

theorem capacityRatio_eq : capacityRatio = (64 : ℚ) ^ 6 := by
  unfold capacityRatio; norm_num

theorem exp_nontop (d t i : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (h1 : alpha7 d t + 2 ≤ i) (h2 : i % 2 = t % 2) : t + 9 ≤ d + 2 * i := by
  rw [alpha7_of_ge_two d t ht2] at h1
  unfold tf7 at ht
  unfold ceilParity alphaStarLower at h1
  split_ifs at h1 <;> omega

theorem exp_top (d t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) :
    t + 5 ≤ d + 2 * alpha7 d t := by
  rw [alpha7_of_ge_two d t ht2]
  unfold tf7 at ht
  unfold ceilParity alphaStarLower
  split_ifs <;> omega

theorem exp_top_rise (d t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d)
    (hs : alpha7 d (t + 1) < alpha7 d t) : t + 8 ≤ d + 2 * alpha7 d t := by
  rw [alpha7_of_ge_two d t ht2] at hs ⊢
  rw [alpha7_of_ge_two d (t + 1) (by omega)] at hs
  unfold tf7 at ht
  unfold ceilParity alphaStarLower at hs ⊢
  split_ifs at hs ⊢ <;> omega

theorem omega7_lt_d (d t : ℕ) (hd : 7 ≤ d) (ht : t ≤ tf7 d) : omega7 d t + 1 ≤ d := by
  by_cases h2 : 2 ≤ t
  · rw [omega7_of_ge_two d t h2]
    unfold tf7 at ht
    unfold ceilParity omegaStarLower
    split_ifs <;> omega
  · unfold omega7; split_ifs <;> omega

theorem omega7_bounds (d t : ℕ) (ht2 : 2 ≤ t) :
    t + 2 ≤ 3 * omega7 d t ∧ 3 * omega7 d t ≤ t + 6 := by
  rw [omega7_of_ge_two d t ht2]
  unfold ceilParity omegaStarLower
  split_ifs <;> omega

/-- Ordinary stage `t ≥ 2` and position `i` on the parity class strictly between the top and the
bottom frontier. -/
def Inner (d t i : ℕ) : Prop := 2 ≤ t ∧ alpha7 d t ≤ i ∧ i < omega7 d t ∧ i % 2 = t % 2

/-- **Node classification: the one place where node types are enumerated.**  For `t ≥ 1`, the
sizes `(a, π, τ)` of a node (wires, wires up, wires down per child) at position `(t, i)` are in one
of these closed forms (`capacity d i t = 64^e` with `e` as in the exponent equation):
inactive (`off`), top-descending, top-rising (also the level-1 node at `t = 1`), interior,
bottom-descending, bottom-rising (`τ = 0`).  Everything downstream (integrality of the sizes,
`NodeFacts`, `NodeGeom`) is obtained by a single `cases` on this predicate. -/
inductive NodeShape (d t i : ℕ) : ℕ → ℕ → ℕ → Prop
  | off : NodeShape d t i 0 0 0
  | topDesc (g : ℕ) (e : d + 2 * i = t + 3 + g) (hi : Inner d t i) (h : i = 0 ∨ g ≤ 4) :
      NodeShape d t i (64 ^ (g + 1)) 0 (64 ^ g)
  | topRise (f : ℕ) (e : d + 2 * i = t + 8 + f) (h : Inner d t i ∨ (t = 1 ∧ i = 1)) :
      NodeShape d t i (64 ^ (6 + f)) (2 * (32 * 64 ^ (1 + f))) (16777215 * 64 ^ (1 + f))
  | mid (g : ℕ) (e : d + 2 * i = t + 9 + g) (h : Inner d t i) :
      NodeShape d t i (64 ^ (7 + g) - 64 ^ (1 + g)) (2 * (4095 * 32 * 64 ^ g))
        (16777215 * 64 ^ (2 + g))
  | botDesc (g h : ℕ) (hgh : h + 2 ≤ g) (hg : g ≤ h + 6) (e : d + 2 * i = t + 9 + h)
      (hd : d = i + (g + 1)) :
      NodeShape d t i (64 ^ (g + 1) - 64 ^ (h + 1)) (2 * (4095 * 32 * 64 ^ h))
        (64 ^ g - 64 ^ (h + 2))
  | botRise (g h : ℕ) (hgh : h ≤ g) :
      NodeShape d t i (64 ^ (g + 1) - 64 ^ (h + 1)) (64 ^ (g + 1) - 64 ^ (h + 1)) 0

theorem NodeShape.even {d t i a u n : ℕ} (h : NodeShape d t i a u n) : 2 ∣ u := by
  cases h with
  | off | topDesc => simp
  | topRise | mid | botDesc => exact dvd_mul_right _ _
  | botRise g h _ =>
    exact Nat.dvd_sub (dvd_pow (by norm_num) (by omega)) (dvd_pow (by norm_num) (by omega))

theorem NodeShape.split {d t i a u n : ℕ} (h : NodeShape d t i a u n) : a = u + 64 * n := by
  cases h with
  | off => rfl
  | topDesc => ring
  | topRise => ring
  | mid => apply Nat.sub_eq_of_eq_add; ring
  | botDesc g h hgh =>
    have h1 : 64 ^ (h + 1) ≤ 64 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 64 ^ (h + 2) ≤ 64 ^ g := Nat.pow_le_pow_right (by norm_num) hgh
    zify [h1, h2]; ring
  | botRise => rfl

theorem shape_rat (d : ℕ) (hd : 7 ≤ d) (t i : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ∃ a u n : ℕ, allocation d i t = a ∧ flowUp d i t = u ∧ flowDown d i t = n ∧
      NodeShape d t i a u n := by
  by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ i ∧ i ≤ omega7 d t ∧ i % 2 = t % 2
  swap
  · exact ⟨0, 0, 0, by simp [allocation_inactive _ _ _ hact], by simp [flowUp_inactive _ hact],
      by simp [flowDown_inactive _ hact], .off⟩
  have hlt := alpha7_lt_omega7 d hd t ht2 ht
  have hp1 := alpha7_parity d t
  have hp2 := alpha7_parity d (t + 1)
  have hst := alpha7_step d t hd ht
  have hq1 := omega7_parity d t
  have hq2 := omega7_parity d (t + 1)
  have hqt := omega7_step d t hd ht
  have hact' := hact
  obtain ⟨-, hαle, hωle, hpar⟩ := hact'
  by_cases hα : i = alpha7 d t
  · by_cases hs : alpha7 d t < alpha7 d (t + 1)
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 3 + g :=
        ⟨d + 2 * i - (t + 3), by have := exp_top d t ht2 ht.le; omega⟩
      have hc := capacity_eq_pow d i t (g + 1) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .topDesc g hg ⟨ht2, by omega, by omega, by omega⟩ ?_⟩
      · rw [alloc_top d hact hα, hc]
      · rw [flowUp_top_desc d hact hα hs]; simp
      · rw [flowDown_top_desc d hact hα hs, hc]; push_cast; ring
      · rcases lemma32_schedule7 d hd t hs with h0 | h
        · left; omega
        · right
          rw [← hα, hc] at h
          by_contra hg5
          have : ((64 ^ 6 : ℕ) : ℚ) ≤ ((64 ^ (g + 1) : ℕ) : ℚ) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
          push_cast at h this
          linarith
    · obtain ⟨f, hf⟩ : ∃ f, d + 2 * i = t + 8 + f :=
        ⟨d + 2 * i - (t + 8), by have := exp_top_rise d t ht2 ht (by omega); omega⟩
      have hc := capacity_eq_pow d i t (6 + f) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .topRise f hf (Or.inl ⟨ht2, by omega, by omega, by omega⟩)⟩
      · rw [alloc_top d hact hα, hc]
      · rw [flowUp_top_rise d hact hα hs, hc]; push_cast; ring
      · rw [flowDown_mid d hact (fun _ => hs) (by omega), hc]; push_cast; ring
  · have hne := exp_nontop d t i ht2 ht (by omega) hpar
    by_cases hω : i = omega7 d t
    · obtain ⟨g, hgi⟩ : ∃ g, d = i + (g + 1) :=
        ⟨d - i - 1, by have := omega7_lt_d d t hd ht.le; omega⟩
      obtain ⟨h, hh⟩ : ∃ h, d + 2 * i = t + 9 + h := ⟨d + 2 * i - (t + 9), by omega⟩
      have hb := omega7_bounds d t ht2
      have hc := capacity_eq_pow d i t (7 + h) (by omega)
      have hle : 64 ^ (h + 1) ≤ 64 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hA : allocation d i t = ((64 ^ (g + 1) - 64 ^ (h + 1) : ℕ) : ℚ) := by
        rw [alloc_bot d hact hα hω, hc, capacityRatio_eq, Nat.cast_sub hle]
        show ((64 ^ d : ℕ) : ℚ) / ((64 : ℕ) : ℚ) ^ i - _ = _
        rw [hgi]; push_cast
        simp only [pow_add]
        field_simp
      by_cases hs : omega7 d t < omega7 d (t + 1)
      · have hU : flowUp d i t = ((2 * (4095 * 32 * 64 ^ h) : ℕ) : ℚ) := by
          rw [flowUp_mid d hact hα (fun _ => hs), hc, capacityRatio_eq]; push_cast; ring
        refine ⟨_, _, _, hA, hU, ?_, .botDesc g h (by omega) (by omega) hh hgi⟩
        have hsend := flow_send7 d hd t ht2 ht i
        rw [hA, hU, Nat.cast_sub hle] at hsend
        rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
        push_cast at hsend ⊢
        ring_nf at hsend ⊢
        linarith
      · refine ⟨_, _, _, hA, ?_, ?_, .botRise g h (by omega)⟩
        · rw [flowUp_bot_rise d hact hα hω hs, hA]
        · rw [flowDown_bot_rise d hact hα hω hs]; simp
    · obtain ⟨g, hg⟩ : ∃ g, d + 2 * i = t + 9 + g := ⟨d + 2 * i - (t + 9), by omega⟩
      have hc := capacity_eq_pow d i t (7 + g) (by omega)
      have hle : 64 ^ (1 + g) ≤ 64 ^ (7 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine ⟨_, _, _, ?_, ?_, ?_, .mid g hg ⟨ht2, by omega, by omega, by omega⟩⟩
      · rw [alloc_mid d hact hα hω, hc, capacityRatio_eq, Nat.cast_sub hle]
        push_cast; rw [pow_add, pow_add]; field_simp
      · rw [flowUp_mid d hact hα (fun h => absurd h hω), hc, capacityRatio_eq]; push_cast; ring
      · rw [flowDown_mid d hact (fun h => absurd h hα) hω, hc]; push_cast; ring

/-- The allocation at a final-time node is a natural number. -/
theorem allocNat (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) (i : ℕ) :
    ∃ n : ℕ, allocation d i t = n := by
  rcases ht.lt_or_eq with ht | rfl
  · obtain ⟨a, -, -, h, -⟩ := shape_rat d hd t i ht2 ht
    exact ⟨a, h⟩
  by_cases hact : tf7 d ≤ tf7 d ∧ alpha7 d (tf7 d) ≤ i ∧ i ≤ omega7 d (tf7 d) ∧
      i % 2 = tf7 d % 2
  swap
  · exact ⟨0, by rw [allocation_inactive _ _ _ hact]; simp⟩
  have := alpha7_tf_eq_omega7_tf d hd
  have hα : i = alpha7 d (tf7 d) := by omega
  have he := exp_top d _ ht2 le_rfl
  exact ⟨_, by rw [alloc_top d hact hα, capacity_eq_pow d i _ (d + 2 * i - (tf7 d + 2)) (by omega)]⟩


/-! ## The flow sizes -/

/-- Wires per node: the paper's special steps `t = 0, 1`, and `⌊allocation⌋` for `t ≥ 2`. -/
def flowA7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then (if l = 0 then 64 ^ d else 0)
  else if t = 1 then (if l = 1 then 64 ^ (d - 1) else 0)
  else ⌊allocation d l t⌋₊

/-- Wires sent to the parent. -/
def flowUp7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then 0
  else if t = 1 then (if l = 1 then 64 ^ (d - 5) else 0)
  else ⌊flowUp d l t⌋₊

/-- Wires sent to each child. -/
def flowDown7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) : ℕ :=
  if t = 0 then (if l = 0 then 64 ^ (d - 1) else 0)
  else if t = 1 then (if l = 1 then 64 ^ (d - 2) - 64 ^ (d - 6) else 0)
  else ⌊flowDown d l t⌋₊

theorem floor_of_eq (x : ℚ) (n : ℕ) (h : x = n) : ⌊x⌋₊ = n := by
  rw [h, Nat.floor_natCast]

theorem cast_flowA7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t ≤ tf7 d) :
    ((flowA7 d hd l t : ℕ) : ℚ) = allocation d l t := by
  obtain ⟨n, hn⟩ := allocNat d hd t ht2 ht l
  have : flowA7 d hd l t = n := by
    unfold flowA7
    rw [if_neg (by omega), if_neg (by omega)]
    exact floor_of_eq _ _ hn
  rw [this, hn]

theorem flow7_shape (d : ℕ) (hd : 7 ≤ d) (t i : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    NodeShape d t i (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t) ∧
      ((flowUp7 d hd i t : ℕ) : ℚ) = flowUp d i t ∧
      ((flowDown7 d hd i t : ℕ) : ℚ) = flowDown d i t := by
  obtain ⟨a, u, n, h1, h2, h3, hs⟩ := shape_rat d hd t i ht2 ht
  unfold flowA7 flowUp7 flowDown7
  simp only [if_neg (show t ≠ 0 by omega), if_neg (show t ≠ 1 by omega),
    floor_of_eq _ _ h1, floor_of_eq _ _ h2, floor_of_eq _ _ h3]
  exact ⟨hs, h2.symm, h3.symm⟩

theorem cast_flowUp7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowUp7 d hd l t : ℕ) : ℚ) = flowUp d l t ∧ 2 ∣ flowUp7 d hd l t :=
  ⟨(flow7_shape d hd t l ht2 ht).2.1, (flow7_shape d hd t l ht2 ht).1.even⟩

theorem cast_flowDown7 (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowDown7 d hd l t : ℕ) : ℚ) = flowDown d l t :=
  (flow7_shape d hd t l ht2 ht).2.2

/-- `NodeShape` for every `1 ≤ t < tf`: for `t = 1` the level-1 node is a rising top. -/
theorem node_shape (d : ℕ) (hd : 7 ≤ d) (t i : ℕ) (ht1 : 1 ≤ t) (ht : t < tf7 d) :
    NodeShape d t i (flowA7 d hd i t) (flowUp7 d hd i t) (flowDown7 d hd i t) := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl : t = 1 := by omega
    by_cases hi : i = 1
    · subst hi
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
      have e1 : flowA7 (e + 7) hd 1 1 = 64 ^ (6 + e) := by
        simp [flowA7, show e + 7 - 1 = 6 + e by omega]
      have e2 : flowUp7 (e + 7) hd 1 1 = 2 * (32 * 64 ^ (1 + e)) := by
        simp [flowUp7]; ring
      have e3 : flowDown7 (e + 7) hd 1 1 = 16777215 * 64 ^ (1 + e) := by
        simp [flowDown7]
        rw [show 64 ^ (e + 5) = 64 ^ (e + 1) * 16777216 by ring, show 1 + e = e + 1 by omega]
        omega
      rw [e1, e2, e3]
      exact .topRise e (by omega) (Or.inr ⟨rfl, rfl⟩)
    · simpa [flowA7, flowUp7, flowDown7, hi] using NodeShape.off
  · exact (flow7_shape d hd t i h ht).1

private theorem alpha7_two (d : ℕ) (hd : 7 ≤ d) : alpha7 d 2 = 0 := by
  rw [alpha7_of_ge_two d 2 le_rfl]; unfold ceilParity alphaStarLower; split_ifs <;> omega

private theorem omega7_two (d : ℕ) : omega7 d 2 = 2 := by
  rw [omega7_of_ge_two d 2 le_rfl]; unfold ceilParity omegaStarLower; split_ifs <;> omega

/-- Allocation at `t = 2` (`α 2 = 0`, `ω 2 = 2`): `N/k²·(…)`, explicit values. -/
theorem flowA7_two (d : ℕ) (hd : 7 ≤ d) (h2 : 2 ≤ tf7 d) (l : ℕ) :
    flowA7 d hd l 2 =
      if l = 0 then 64 ^ (d - 4) else if l = 2 then 64 ^ (d - 2) - 64 ^ (d - 6) else 0 := by
  have ha := alpha7_two d hd
  have ho := omega7_two d
  unfold flowA7
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases h0 : l = 0
  · subst h0
    rw [if_pos rfl]
    apply floor_of_eq
    have hact : 2 ≤ tf7 d ∧ alpha7 d 2 ≤ 0 ∧ 0 ≤ omega7 d 2 ∧ 0 % 2 = 2 % 2 := by
      refine ⟨h2, ?_, ?_, ?_⟩ <;> omega
    rw [alloc_top d hact (by show 0 = alpha7 d 2; omega),
      capacity_eq_pow d 0 2 (d - 4) (by omega)]
  by_cases h2' : l = 2
  · subst h2'
    rw [if_neg (by omega), if_pos rfl]
    apply floor_of_eq
    have hact : 2 ≤ tf7 d ∧ alpha7 d 2 ≤ 2 ∧ 2 ≤ omega7 d 2 ∧ 2 % 2 = 2 % 2 := by
      refine ⟨h2, ?_, ?_, ?_⟩ <;> omega
    rw [alloc_bot d hact (by show 2 ≠ alpha7 d 2; omega)
      (by show 2 = omega7 d 2; omega), capacity_eq_pow d 2 2 d (by omega),
      capacityRatio_eq]
    show (((64 ^ d : ℕ) : ℚ)) / ((64 : ℕ) : ℚ) ^ 2 - _ = _
    rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (by omega))]
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 6 := ⟨d - 6, by omega⟩
    have e1 : e + 6 - 2 = e + 4 := by omega
    have e2 : e + 6 - 6 = e := by omega
    rw [e1, e2]
    push_cast
    rw [pow_add, pow_add]
    field_simp
  · rw [if_neg h0, if_neg h2']
    apply floor_of_eq
    rw [allocation_inactive _ _ _ (by
      show ¬(2 ≤ tf7 d ∧ alpha7 d 2 ≤ l ∧ l ≤ omega7 d 2 ∧ l % 2 = 2 % 2)
      omega)]
    simp

theorem flowSizes7_split (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht : t < tf7 d) :
    flowA7 d hd l t = flowUp7 d hd l t + 64 * flowDown7 d hd l t := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · unfold flowA7 flowUp7 flowDown7
    by_cases hl : l = 0
    · subst hl
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      simp [pow_succ]; ring
    · simp [hl]
  · exact (node_shape d hd t l h ht).split

theorem flowSizes7_up_root (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t < tf7 d) :
    flowUp7 d hd 0 t = 0 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    all_goals simp [flowUp7]
  · have hc := cast_flowUp7 d hd 0 t h ht
    have hz : flowUp d 0 t = 0 := by
      by_cases hact : t ≤ tf7 d ∧ alpha7 d t ≤ 0 ∧ 0 ≤ omega7 d t ∧ 0 % 2 = t % 2
      swap
      · exact flowUp_inactive _ hact
      have hp1 := alpha7_parity d t
      have hp2 := alpha7_parity d (t + 1)
      have hst := alpha7_step d t hd ht
      exact flowUp_top_desc d hact (by show 0 = alpha7 d t; omega)
        (by show alpha7 d t < alpha7 d (t + 1); omega)
    rw [hz] at hc
    exact_mod_cast hc.1

theorem flowSizes7_down_leaf (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (ht : t < tf7 d) :
    flowDown7 d hd d t = 0 := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · simp [flowDown7]; omega
    · simp [flowDown7]; omega
  · have hc := cast_flowDown7 d hd d t h ht
    have hz : flowDown d d t = 0 := by
      apply flowDown_inactive
      have := omega7_lt_d d t hd ht.le
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ d ∧ d ≤ omega7 d t ∧ d % 2 = t % 2)
      omega
    rw [hz] at hc
    exact_mod_cast hc

theorem flowSizes7_cons (d : ℕ) (hd : 7 ≤ d) (l t : ℕ) (ht : t < tf7 d) :
    flowA7 d hd l (t + 1) =
      (if 1 ≤ l then flowDown7 d hd (l - 1) t else 0) +
        (if l < d then 64 * flowUp7 d hd (l + 1) t else 0) := by
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
    · unfold flowA7 flowUp7 flowDown7
      by_cases hl : l = 0
      · subst hl; simp
      · by_cases hl1 : l = 1
        · subst hl1; simp
        · simp [hl1]; intro h; omega
    · rw [flowA7_two d hd (by omega) l]
      unfold flowUp7 flowDown7
      by_cases hl : l = 0
      · subst hl
        simp only [show (0 : ℕ) < d by omega, if_true, show ¬ (1 ≤ 0) by omega, if_false,
          zero_add]
        simp only [show (1 : ℕ) ≠ 0 by omega, if_false]
        obtain ⟨e, rfl⟩ : ∃ e, d = e + 7 := ⟨d - 7, by omega⟩
        rw [show e + 7 - 4 = e + 3 by omega, show e + 7 - 5 = e + 2 by omega, ← pow_succ']
      · by_cases hl2 : l = 2
        · subst hl2
          simp
        · simp only [hl, hl2, if_false]
          by_cases hl1 : l = 1
          · subst hl1; simp
          · simp [hl, hl2]
  · have hc := flow_conservation7 d hd t h (by omega) l
    have ha := cast_flowA7 d hd l (t + 1) (by omega) (by omega)
    have hdn : 1 ≤ l → ((flowDown7 d hd (l - 1) t : ℕ) : ℚ) =
        flowDown d (l - 1) t :=
      fun _ => cast_flowDown7 d hd (l - 1) t h ht
    have hup := (cast_flowUp7 d hd (l + 1) t h ht).1
    have hupz : ¬ l < d → flowUp d (l + 1) t = 0 := by
      intro hl
      apply flowUp_inactive
      have := omega7_lt_d d t hd ht.le
      show ¬(t ≤ tf7 d ∧ alpha7 d t ≤ l + 1 ∧ l + 1 ≤ omega7 d t ∧ (l + 1) % 2 = t % 2)
      omega
    have : ((flowA7 d hd l (t + 1) : ℕ) : ℚ) =
        (((if 1 ≤ l then flowDown7 d hd (l - 1) t else 0) +
          (if l < d then 64 * flowUp7 d hd (l + 1) t else 0) : ℕ) : ℚ) := by
      rw [ha, hc]
      by_cases h1 : 1 ≤ l <;> by_cases h2 : l < d
      · simp only [h1, h2, if_true]; push_cast; rw [hdn h1, hup]
      · simp only [h1, h2, if_false]; push_cast; rw [hdn h1, hupz h2]; simp
      · simp only [h1, h2, if_true, if_false]; push_cast; rw [hup]
      · simp only [h1, h2, if_false]; push_cast; rw [hupz h2]; simp
    exact_mod_cast this

/-- **B2c + B2d.** Natural-number flow sizes for the §7 schedule. -/
def flowSizes7 (d : ℕ) (hd : 7 ≤ d) : FlowSizes d (tf7 d) where
  a := flowA7 d hd
  up := flowUp7 d hd
  down := flowDown7 d hd
  ha_root := by simp [flowA7]
  ha_init := fun l hl => by simp [flowA7]; omega
  hup_even := fun l t ht => by
    rcases Nat.lt_or_ge t 2 with h | h
    · obtain rfl | rfl : t = 0 ∨ t = 1 := by omega
      · simp [flowUp7]
      · unfold flowUp7
        by_cases hl : l = 1
        · subst hl
          simp only [if_true, show (1 : ℕ) ≠ 0 by omega, if_false]
          exact Dvd.dvd.pow (by norm_num) (by omega)
        · simp [hl]
    · exact (cast_flowUp7 d hd l t h ht).2
  hup_root := fun t ht => flowSizes7_up_root d hd t ht
  hdown_leaf := fun t ht => flowSizes7_down_leaf d hd t ht
  hsplit := fun l t _ ht => flowSizes7_split d hd l t ht
  hcons := fun l t _ ht => flowSizes7_cons d hd l t ht

end Chvatal
