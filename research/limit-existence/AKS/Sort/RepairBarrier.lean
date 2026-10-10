import AKS.Sort.Dependency
import AKS.Kahale.RankInputs
import AKS.Kahale.Fanout
import Mathlib.Analysis.SpecificLimits.Basic

/-! # A cut obstruction to cheap repair after local modules

For the last wire of a prefix, an input support A and a cover R of all
attainable output ranks satisfy n+1 <= |A|+|R|. The support may be a
coarse module cone rather than the binary cone. A sorting suffix supplies R.
No asymptotic convergence theorem or new sorting coefficient is claimed.
-/

namespace SortingRepair

open Finset

theorem support_rank_cover_cut {n : ℕ} (hn : 0 < n)
    (pre : ComparatorNetwork n) (A R : Finset (Fin n))
    (hA : ∀ x y : Fin n → Bool, (∀ i ∈ A, x i = y i) →
      pre.exec x ⟨n-1, by omega⟩ = pre.exec y ⟨n-1, by omega⟩)
    (hR : ∀ σ : Equiv.Perm (Fin n), pre.exec σ ⟨n-1, by omega⟩ ∈ R) :
    n + 1 ≤ A.card + R.card := by
  classical
  let last : Fin n := ⟨n-1, by omega⟩
  let v : Fin n → Bool := fun i => if i ∈ A then false else true
  have hvcount : univ.filter (fun i => v i = false) = A := by
    ext i
    simp [v]
  have hconst : pre.exec (fun _ : Fin n => false) = (fun _ => false) :=
    pre.exec_eq_of_monotone (fun _ _ _ => le_refl _)
  have hv : pre.exec v last = false := by
    have he := hA v (fun _ => false) (by intro i hi; simp [v, hi])
    simpa only [hconst] using he
  obtain ⟨σ, hg⟩ := exists_sorting_perm v
  let g : Fin n → Bool := v ∘ σ.symm
  have hvg : v = g ∘ σ := by funext i; simp [g]
  have hgz : g (pre.exec σ last) = false := by
    rw [hvg, ComparatorNetwork.exec_comp_mono pre hg] at hv
    exact hv
  have hlo := Kahale.monotone_zero_rank g hg (pre.exec σ last) hgz
  have hcount := Kahale.permuted_zero_count v σ
  change (univ.filter (fun i => g i = false)).card = _ at hcount
  rw [hcount, hvcount] at hlo
  have hspan := Kahale.rank_interval_card_le pre last R hR σ (Equiv.refl _)
  have hid : pre.exec (Equiv.refl (Fin n)) last = last := by
    exact congrFun (pre.exec_eq_of_monotone (v := id) monotone_id) last
  rw [hid] at hspan
  change n - 1 + 1 - (pre.exec σ last).val ≤ R.card at hspan
  omega

/-- The concrete binary input cone and suffix value cone satisfy the cut
inequality. This exposes the obstruction in the actual network model. -/
theorem source_suffix_cut {n : ℕ} (hn : 0 < n) (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec σ) = id) :
    n + 1 ≤ (sources pre ⟨n-1, by omega⟩).card +
      (Kahale.suffixReach suffix {⟨n-1, by omega⟩}).card := by
  apply support_rank_cover_cut hn pre
  · intro x y hxy
    exact exec_eq_of_agree_sources pre _ x y hxy
  · exact Kahale.sorted_suffix_rank_cover pre suffix hp hs _

/-- A fixed-depth lifted prefix cannot be completed at uniformly small
depth on arbitrarily many copies: its repair tail must satisfy this bound. -/
theorem binary_cut_bound {n : ℕ} (hn : 0 < n) (pre : ComparatorNetwork n)
    (suffix : List (List (Comparator n)))
    (hp : ∀ cs ∈ suffix, IsParallelLayer cs)
    (hs : ∀ σ : Equiv.Perm (Fin n),
      (ComparatorNetwork.mk suffix.flatten).exec (pre.exec σ) = id) :
    n + 1 ≤ 2 ^ pre.depth + 2 ^ suffix.length := by
  have hc := source_suffix_cut hn pre suffix hp hs
  have ha := sources_card_le_depth pre ⟨n-1, by omega⟩
  have hr := Kahale.suffixReach_card suffix ({⟨n-1, by omega⟩} : Finset (Fin n))
  simp only [card_singleton, mul_one] at hr
  omega

/-- Arithmetic at a cut just before its prefix product reaches half the
input count. K bounds the arity of the crossing stage. -/
theorem crossing_product_barrier (n K P Q : ℕ)
    (hsmall : 2 * P ≤ n) (hcross : n ≤ 2 * K * P)
    (hcut : n ≤ P + Q) : n ^ 2 ≤ 4 * K * (P * Q) := by
  have hq : n ≤ 2 * Q := by omega
  have h := Nat.mul_le_mul hcross hq
  nlinarith

private theorem exists_product_crossing (xs : List ℕ) (K start n : ℕ)
    (hm : ∀ a ∈ xs, a ≤ K) (hsmall : 2 * start < n)
    (hfinal : n ≤ 2 * start * xs.prod) :
    ∃ pre a post, xs = pre ++ a :: post ∧
      2 * (start * pre.prod) < n ∧ n ≤ 2 * K * (start * pre.prod) := by
  induction xs generalizing start with
  | nil => simp at hfinal; omega
  | cons a xs ih =>
    have ha := hm a List.mem_cons_self
    by_cases hc : n ≤ 2 * (start * a)
    · refine ⟨[], a, xs, rfl, ?_, ?_⟩
      · simpa using hsmall
      · simp only [List.prod_nil, mul_one]
        nlinarith
    · have ht : n ≤ 2 * (start * a) * xs.prod := by
        simpa only [List.prod_cons, mul_assoc] using hfinal
      obtain ⟨pre, b, post, he, hs, hb⟩ := ih (start * a)
        (fun c hc => hm c (List.mem_cons_of_mem a hc)) (by omega) ht
      refine ⟨a :: pre, b, post, ?_, ?_, ?_⟩
      · simp [he]
      · simpa only [List.prod_cons, mul_assoc] using hs
      · simpa only [List.prod_cons, mul_assoc] using hb

/-- Variable-arity product obstruction, conditional on the cut inequalities.
For actual staged local modules, their dependency and value cones supply
those inequalities through `support_rank_cover_cut`. -/
theorem layer_product_barrier (xs : List ℕ) (n K : ℕ) (hn : 3 ≤ n)
    (hm : ∀ a ∈ xs, a ≤ K)
    (hcut : ∀ pre post, xs = pre ++ post → n ≤ pre.prod + post.prod) :
    n ^ 2 ≤ 4 * K * xs.prod := by
  have hw := hcut xs [] (by simp)
  simp only [List.prod_nil] at hw
  have hf : n ≤ 2 * 1 * xs.prod := by omega
  obtain ⟨pre, a, post, he, hs, hc⟩ :=
    exists_product_crossing xs K 1 n hm (by omega) hf
  simp only [one_mul] at hs hc
  have hq := hcut pre (a :: post) he
  have hb := crossing_product_barrier n K pre.prod (a :: post).prod (by omega) hc hq
  simpa only [he, List.prod_append] using hb

/-- The weighted product obstruction cannot be satisfied by r module stages
and r*e+B binary stages if 2^e<m. Even an arbitrary fixed startup B fails.
This is arithmetic; the staged architecture supplies the product inequality. -/
theorem no_uniform_small_repair (m e B : ℕ) (hm : 0 < m) (he : 2^e < m) :
    ¬ ∀ r : ℕ, (m^r)^2 ≤ 4*m*(m^r * 2^(r*e+B)) := by
  intro h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (2 : ℝ)^e := by positivity
  have hq : (1 : ℝ) < (m : ℝ) / (2 : ℝ)^e := by
    apply (lt_div_iff₀ hp).2
    simpa using (show (2 : ℝ)^e < (m : ℝ) by exact_mod_cast he)
  have ht := tendsto_pow_atTop_atTop_of_one_lt hq
  have hb : ∀ r : ℕ, ((m : ℝ) / (2 : ℝ)^e)^r ≤ 4*(m : ℝ)*(2 : ℝ)^B := by
    intro r
    have hr : ((m : ℝ)^r)^2 ≤ 4*(m : ℝ)*((m : ℝ)^r * (2 : ℝ)^(r*e+B)) := by
      exact_mod_cast h r
    have hmpos : (0 : ℝ) < (m : ℝ)^r := pow_pos hmR r
    rw [pow_add, Nat.mul_comm r e, pow_mul] at hr
    have hc : (m : ℝ)^r ≤ 4*(m : ℝ)*(2 : ℝ)^B * ((2 : ℝ)^e)^r := by
      nlinarith
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos hp r)).2 hc
  have hu := ht.eventually (Filter.eventually_gt_atTop (4*(m : ℝ)*(2 : ℝ)^B))
  obtain ⟨r, hr⟩ := hu.exists
  exact (not_lt_of_ge (hb r)) hr

end SortingRepair
