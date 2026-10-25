import AKS.Bounds.Kahale
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit finite lower bounds on `D(n)`

Three folklore/finite bounds, proved for every `n` and every sorting network in the
repository model (`ComparatorNetwork.Sorts.{0}`, greedy `depth`):

* fan-in: `n ≤ 2^depth`, so `⌈lg n⌉ ≤ D(n)` (`clog_le_minimum`).  A suffix of `d`
  parallel layers moves the value on one wire to at most `2^d` positions
  (`Kahale.suffixReach_card`), and permutation inputs send it everywhere.
* counting: `n! ≤ 2^(depth·⌊n/2⌋)`, so `⌈lg(n!)/⌊n/2⌋⌉ ≤ D(n)`
  (`countingBound_le_minimum`).  On a fixed input a comparator acts as the identity or
  as a transposition, so it is at most two-to-one on any finite set of inputs; a
  sorting network maps all `n!` permutations to `id`; a parallel layer has at most
  `⌊n/2⌋` comparators.
* Kahale's finite Fibonacci inequality `n·fib(d+1) ≤ 2^(d+1)(d+1)^2`, packaged as its
  least solution `kahaleBound n ≤ D(n)`.

`minimum_ge_max_bounds` combines them.  `two_mul_sub_two_le_minimum_two_pow` evaluates
the counting bound at powers of two through `n! ≥ n^n / e^n` and `e² < 8`:
`D(2^k) ≥ 2k - 2`, e.g. `D(2^16) ≥ 30`.
-/

namespace SortingDepth

open Finset

/-! ### One comparator is at most two-to-one -/

theorem comparator_apply_eq_or_swap {n : ℕ} {α : Type*} [LinearOrder α]
    (c : Comparator n) (v : Fin n → α) :
    c.apply v = v ∨ c.apply v = v ∘ Equiv.swap c.i c.j := by
  by_cases h : v c.i ≤ v c.j
  · left
    funext k
    unfold Comparator.apply
    split_ifs with h₁ h₂
    · subst h₁; exact min_eq_left h
    · subst h₂; exact max_eq_right h
    · rfl
  · right
    push_neg at h
    funext k
    unfold Comparator.apply
    simp only [Function.comp]
    split_ifs with h₁ h₂
    · subst h₁; rw [min_eq_right h.le, Equiv.swap_apply_left]
    · subst h₂; rw [max_eq_left h.le, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]

theorem card_le_two_mul_card_image_apply {n : ℕ} (c : Comparator n)
    (A : Finset (Fin n → Fin n)) :
    A.card ≤ 2 * (A.image c.apply).card := by
  classical
  have hsub : A ⊆ (A.image c.apply).biUnion
      (fun τ ↦ ({τ, τ ∘ Equiv.swap c.i c.j} : Finset (Fin n → Fin n))) := by
    intro v hv
    refine mem_biUnion.2 ⟨c.apply v, mem_image_of_mem _ hv, ?_⟩
    rcases comparator_apply_eq_or_swap c v with h | h
    · rw [h]; exact mem_insert_self _ _
    · rw [h]
      apply mem_insert_of_mem
      apply mem_singleton.2
      funext k
      simp [Function.comp]
  calc A.card
      ≤ ((A.image c.apply).biUnion
          (fun τ ↦ ({τ, τ ∘ Equiv.swap c.i c.j} : Finset (Fin n → Fin n)))).card :=
        card_le_card hsub
    _ ≤ ∑ τ ∈ A.image c.apply,
          ({τ, τ ∘ Equiv.swap c.i c.j} : Finset (Fin n → Fin n)).card := card_biUnion_le
    _ ≤ ∑ _τ ∈ A.image c.apply, 2 := sum_le_sum fun _ _ ↦ card_le_two
    _ = 2 * (A.image c.apply).card := by rw [sum_const, smul_eq_mul, mul_comm]

theorem card_le_two_pow_mul_card_image_exec {n : ℕ} (cs : List (Comparator n))
    (A : Finset (Fin n → Fin n)) :
    A.card ≤ 2 ^ cs.length * (A.image (ComparatorNetwork.mk cs).exec).card := by
  classical
  induction cs generalizing A with
  | nil =>
    have h : (ComparatorNetwork.mk ([] : List (Comparator n))).exec =
        fun v : Fin n → Fin n ↦ v := rfl
    rw [h, image_id']
    simp
  | cons c cs ih =>
    have h₁ := card_le_two_mul_card_image_apply c A
    have h₂ := ih (A.image c.apply)
    rw [image_image] at h₂
    have he : (ComparatorNetwork.mk cs).exec ∘ c.apply =
        (ComparatorNetwork.mk (c :: cs)).exec (α := Fin n) := rfl
    rw [he] at h₂
    calc A.card ≤ 2 * (A.image c.apply).card := h₁
      _ ≤ 2 * (2 ^ cs.length * (A.image (ComparatorNetwork.mk (c :: cs)).exec).card) :=
        Nat.mul_le_mul_left _ h₂
      _ = _ := by rw [List.length_cons, pow_succ]; ring

/-- Counting: a sorting network with `s` comparators satisfies `n! ≤ 2^s`. -/
theorem factorial_le_two_pow_size {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) : n.factorial ≤ 2 ^ net.size := by
  classical
  let A : Finset (Fin n → Fin n) :=
    univ.image (fun σ : Equiv.Perm (Fin n) ↦ (σ : Fin n → Fin n))
  have hA : A.card = n.factorial := by
    rw [card_image_of_injective _ DFunLike.coe_injective, card_univ, Fintype.card_perm,
      Fintype.card_fin]
  have himg : A.image net.exec ⊆ {id} := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := mem_image.1 hw
    obtain ⟨σ, -, rfl⟩ := mem_image.1 hv
    exact mem_singleton.2 (Kahale.sorting_rank_identity net hs σ)
  have h := card_le_two_pow_mul_card_image_exec net.comparators A
  have h₁ : (A.image net.exec).card ≤ 1 := (card_le_card himg).trans (card_singleton _).le
  rw [hA] at h
  calc n.factorial ≤ 2 ^ net.comparators.length * (A.image net.exec).card := h
    _ ≤ 2 ^ net.comparators.length * 1 := Nat.mul_le_mul_left _ h₁
    _ = 2 ^ net.size := by rw [mul_one]; rfl

/-! ### Parallel layers have at most `⌊n/2⌋` comparators -/

theorem parallelLayer_two_mul_length_le {n : ℕ} (cs : List (Comparator n))
    (hp : IsParallelLayer cs) : 2 * cs.length ≤ n := by
  have hnd : (cs.flatMap fun c ↦ [c.i, c.j]).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun c _ ↦ ?_, hp.imp fun {a b} hab ↦ ?_⟩
    · simpa using ne_of_lt c.h
    · unfold Comparator.overlaps at hab
      push_neg at hab
      simp only [Function.onFun, List.disjoint_cons_left, List.disjoint_cons_right,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp_all [eq_comm]
  have h := hnd.length_le_card
  simp only [List.length_flatMap, List.length_cons, List.length_nil, Fintype.card_fin,
    List.map_const', List.sum_replicate, smul_eq_mul] at h
  omega

theorem flatten_length_le_length_mul {n : ℕ} (layers : List (List (Comparator n)))
    (hp : ∀ cs ∈ layers, IsParallelLayer cs) :
    layers.flatten.length ≤ layers.length * (n / 2) := by
  induction layers with
  | nil => simp
  | cons cs ls ih =>
    have h₁ : cs.length ≤ n / 2 := by
      have := parallelLayer_two_mul_length_le cs (hp cs List.mem_cons_self)
      omega
    have h₂ := ih (fun d hd ↦ hp d (List.mem_cons_of_mem _ hd))
    rw [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

/-- Counting through the depth: a sorting network satisfies `n! ≤ 2^(depth·⌊n/2⌋)`. -/
theorem factorial_le_two_pow_depth_mul {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) :
    n.factorial ≤ 2 ^ (net.depth * (n / 2)) := by
  have hs' : ComparatorNetwork.Sorts.{0} ⟨(Kahale.greedyLayers net).flatten⟩ := by
    intro α _ v
    rw [Kahale.greedyLayers_exec]
    exact hs α v
  have h := factorial_le_two_pow_size _ hs'
  have hl := flatten_length_le_length_mul _ (Kahale.greedyLayers_parallel net)
  rw [Kahale.greedyLayers_length] at hl
  exact h.trans (Nat.pow_le_pow_right (by norm_num) hl)

/-! ### Fan-in -/

/-- Fan-in: a sorting network satisfies `n ≤ 2^depth`. -/
theorem le_two_pow_depth {n : ℕ} (net : ComparatorNetwork n)
    (hs : ComparatorNetwork.Sorts.{0} net) : n ≤ 2 ^ net.depth := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  let i₀ : Fin n := ⟨0, hn⟩
  have hs' : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk (Kahale.greedyLayers net).flatten).exec
        ((ComparatorNetwork.mk ([] : List (Comparator n))).exec σ) = id := by
    intro σ
    rw [Kahale.greedyLayers_exec]
    exact Kahale.sorting_rank_identity net hs σ
  have hcover : (univ : Finset (Fin n)) ⊆ Kahale.suffixReach (Kahale.greedyLayers net) {i₀} := by
    intro j _
    have h := Kahale.sorted_suffix_rank_cover ⟨[]⟩ (Kahale.greedyLayers net)
      (Kahale.greedyLayers_parallel net) hs' i₀ (Equiv.swap i₀ j)
    have he : (ComparatorNetwork.mk ([] : List (Comparator n))).exec
        (⇑(Equiv.swap i₀ j)) i₀ = j := Equiv.swap_apply_left i₀ j
    rwa [he] at h
  have h := (card_le_card hcover).trans (Kahale.suffixReach_card _ _)
  simpa [Kahale.greedyLayers_length] using h

/-! ### The three bounds on `D(n)` -/

/-- Fan-in bound: `⌈lg n⌉ ≤ D(n)`. -/
theorem clog_le_minimum (n : ℕ) : Nat.clog 2 n ≤ minimum n := by
  obtain ⟨net, hs, hd⟩ := minimum_attained n
  rw [← hd]
  exact Nat.clog_le_of_le_pow (le_two_pow_depth net hs)

/-- Counting bound: `n! ≤ 2^(D(n)·⌊n/2⌋)`. -/
theorem factorial_le_two_pow_minimum_mul (n : ℕ) :
    n.factorial ≤ 2 ^ (minimum n * (n / 2)) := by
  obtain ⟨net, hs, hd⟩ := minimum_attained n
  rw [← hd]
  exact factorial_le_two_pow_depth_mul net hs

theorem clog_factorial_le_minimum_mul (n : ℕ) :
    Nat.clog 2 n.factorial ≤ minimum n * (n / 2) :=
  Nat.clog_le_of_le_pow (factorial_le_two_pow_minimum_mul n)

/-- The counting bound `⌈⌈lg n!⌉ / ⌊n/2⌋⌉ = ⌈lg(n!) / ⌊n/2⌋⌉` (and `0` for `n < 2`). -/
def countingBound (n : ℕ) : ℕ := (Nat.clog 2 n.factorial + n / 2 - 1) / (n / 2)

theorem countingBound_le_minimum (n : ℕ) : countingBound n ≤ minimum n := by
  unfold countingBound
  rcases Nat.eq_zero_or_pos (n / 2) with h | h
  · rw [h, Nat.div_zero]
    exact Nat.zero_le _
  · have hc := clog_factorial_le_minimum_mul n
    apply Nat.lt_succ_iff.1
    rw [Nat.div_lt_iff_lt_mul h, Nat.succ_mul]
    generalize minimum n * (n / 2) = P at hc ⊢
    omega

/-- The least `d` allowed by Kahale's finite Fibonacci inequality
`n·fib(d+1) ≤ 2^(d+1)(d+1)^2`; `D(n)` itself satisfies it. -/
def kahaleBound (n : ℕ) : ℕ :=
  Nat.find (⟨minimum n, minimum_fibonacci_bound n⟩ :
    ∃ d : ℕ, n * Nat.fib (d + 1) ≤ 2 ^ (d + 1) * (d + 1) ^ 2)

theorem kahaleBound_spec (n : ℕ) :
    n * Nat.fib (kahaleBound n + 1) ≤ 2 ^ (kahaleBound n + 1) * (kahaleBound n + 1) ^ 2 :=
  Nat.find_spec (⟨minimum n, minimum_fibonacci_bound n⟩ :
    ∃ d : ℕ, n * Nat.fib (d + 1) ≤ 2 ^ (d + 1) * (d + 1) ^ 2)

theorem kahaleBound_le_minimum (n : ℕ) : kahaleBound n ≤ minimum n :=
  Nat.find_min' _ (minimum_fibonacci_bound n)

/-- **LB-01.** For every `n`,
`max(⌈lg n⌉, ⌈lg(n!)/⌊n/2⌋⌉, least d with n·fib(d+1) ≤ 2^(d+1)(d+1)^2) ≤ D(n)`. -/
theorem minimum_ge_max_bounds (n : ℕ) :
    max (Nat.clog 2 n) (max (countingBound n) (kahaleBound n)) ≤ minimum n :=
  max_le (clog_le_minimum n) (max_le (countingBound_le_minimum n) (kahaleBound_le_minimum n))

/-! ### The counting bound at powers of two -/

theorem exp_two_lt_eight : Real.exp 2 < 8 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h₁ := Real.exp_one_lt_d9
  have h₀ := Real.exp_pos 1
  rw [h]
  nlinarith

/-- `n^n < 8^(n/2) · n!` for `n = 2m` with `m ≥ 1`, from `x^n/n! ≤ e^x` and `e² < 8`. -/
theorem pow_self_lt_eight_pow_mul_factorial {m : ℕ} (hm : 0 < m) :
    ((2 * m : ℕ) : ℝ) ^ (2 * m) < (8 : ℝ) ^ m * ((2 * m).factorial : ℝ) := by
  have hf : (0 : ℝ) < ((2 * m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h := Real.pow_div_factorial_le_exp (x := ((2 * m : ℕ) : ℝ)) (by positivity) (2 * m)
  have he : Real.exp ((2 * m : ℕ) : ℝ) = Real.exp 2 ^ m := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he, div_le_iff₀ hf] at h
  have hlt : Real.exp 2 ^ m < (8 : ℝ) ^ m :=
    pow_lt_pow_left₀ exp_two_lt_eight (Real.exp_pos 2).le hm.ne'
  exact h.trans_lt (mul_lt_mul_of_pos_right hlt hf)

/-- `D(2^k) ≥ 2k - 2` for `k ≥ 2`, from the counting bound. -/
theorem two_mul_sub_two_le_minimum_two_pow (k : ℕ) (hk : 2 ≤ k) :
    2 * k - 2 ≤ minimum (2 ^ k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  set m := 2 ^ j with hmdef
  have hm : 0 < m := by positivity
  have hn : 2 ^ (j + 1) = 2 * m := by rw [pow_succ, mul_comm]
  rw [hn]
  -- `2^(2m(j+1)) < 2^(3m) · (2m)!` in `ℕ`
  have hreal := pow_self_lt_eight_pow_mul_factorial hm
  have hnat : 2 ^ ((j + 1) * (2 * m)) < 2 ^ (3 * m) * (2 * m).factorial := by
    have e₁ : ((2 * m : ℕ) : ℝ) ^ (2 * m) = ((2 ^ ((j + 1) * (2 * m)) : ℕ) : ℝ) := by
      rw [← hn, pow_mul]; push_cast; rfl
    have e₂ : (8 : ℝ) ^ m = ((2 ^ (3 * m) : ℕ) : ℝ) := by
      rw [pow_mul]; norm_num
    rw [e₁, e₂] at hreal
    exact_mod_cast hreal
  have hsplit : 2 ^ ((j + 1) * (2 * m)) = 2 ^ (3 * m) * 2 ^ (m * (2 * (j + 1) - 3)) := by
    rw [← pow_add]
    congr 1
    rw [Nat.mul_sub, mul_comm (j + 1) (2 * m)]
    have : 3 * m ≤ m * (2 * (j + 1)) := by nlinarith
    rw [show 2 * m * (j + 1) = m * (2 * (j + 1)) by ring]
    rw [mul_comm m 3]
    omega
  rw [hsplit] at hnat
  have hlt : 2 ^ (m * (2 * (j + 1) - 3)) < (2 * m).factorial :=
    Nat.lt_of_mul_lt_mul_left hnat
  have hclog : m * (2 * (j + 1) - 3) < Nat.clog 2 (2 * m).factorial :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hlt
  have hc := clog_factorial_le_minimum_mul (2 * m)
  rw [show 2 * m / 2 = m by omega] at hc
  have h₃ : m * (2 * (j + 1) - 3) < m * minimum (2 * m) := by
    rw [mul_comm m (minimum _)]; omega
  have := Nat.lt_of_mul_lt_mul_left h₃
  omega

/-- Table entry: `D(2^16) ≥ 30` (the counting bound; fan-in gives 16, Kahale's finite
inequality 20). -/
theorem minimum_two_pow_sixteen_ge : 30 ≤ minimum (2 ^ 16) :=
  two_mul_sub_two_le_minimum_two_pow 16 (by norm_num)

end SortingDepth
