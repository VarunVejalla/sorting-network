import R1Sep
import R1Occ
import AKS.Chvatal.Bulk2Exists

/-! # Separator geometry and node networks (W2, step 3; R1-PROOF §4, §6)

Write `X = 2^(e−19)`, so `c = 524288 X`.
* `geomA`: fringe class `f = 7934`, `π/2 ∈ {63X, 64X}`, `524032 X ≤ a ≤ 525312 X`.
* `geomB`: fringe class `f = 406109`, `π/2 = 63X`, `8176 X ≤ a ≤ 8192 X`.

Both use `n = ⌊(π/2)/(f+1)⌋` and `m = ⌊(a−1)/n⌋` (so `m + 1 = ⌈a/n⌉`), and give the window
`50859009 ≤ m + 1 ≤ 2^26`, the fringe protection `(f+1) n ≤ π/2`, the support `μ c ≤ δ_F f n`, and
the `Property B` budget.

Then the node networks:
* `spec_padded`: a rectangle meeting those conditions gives the padded separator, depth `≤ 1053`;
* `spec_Bonly`: the B-only separator with `n = ⌈a/2^26⌉`, depth `≤ 1053`;
* `spec_sorter`: Batcher's sort for `a ≤ 2^45`, depth `≤ 1035`;
* `spec_root`: the package's B2 separator on `2^42` rows at `t = 0`, depth `≤ 2709`. -/

namespace R1T

open Chvatal Tapered945 Sub800

/-! ### Numeric geometry -/

theorem gamma_def : gammaRes = mu / 10 := rfl

/-- **Class `f = 7934`.** -/
theorem geomA (K a π X : ℕ) (hK : K = 63 ∨ K = 64) (hπ : π / 2 = K * X)
    (hL : 524032 * X ≤ a) (hH : a ≤ 525312 * X) (hX : 16777216 ≤ X) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ m * n ≤ a ∧ 7934 ≤ m ∧ 50859009 ≤ m + 1 ∧
      m + 1 ≤ 2 ^ 26 ∧ π / 2 ≤ a ∧ (7934 + 1) * n ≤ π / 2 ∧
      ((mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ 1 / 8 * ((7934 : ℝ) * n) ∧
      (1 / 105000 : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤
        ((((epsB * eta + gammaRes) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) := by
  have hn1 := Nat.div_add_mod (π / 2) 7935
  have hn2 := Nat.mod_lt (π / 2) (show 7935 > 0 by norm_num)
  set n := π / 2 / 7935 with hn
  have hn16 : 16 ≤ n := by rcases hK with rfl | rfl <;> omega
  have hnpos : 0 < n := by omega
  have hm1 := Nat.div_add_mod (a - 1) n
  have hm2 := Nat.mod_lt (a - 1) hnpos
  set m := (a - 1) / n with hm
  have hmn : n * m = m * n := Nat.mul_comm _ _
  have hlo : 50859008 ≤ m := by
    by_contra h
    have h' : m * n ≤ 50859007 * n := Nat.mul_le_mul_right n (by omega)
    rcases hK with rfl | rfl <;> omega
  have hhi : m < 67108864 := by
    by_contra h
    have h' : 67108864 * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
    rcases hK with rfl | rfl <;> omega
  have hsucc : (m + 1) * n = m * n + n := by ring
  have hamn : a ≤ m * n + n := by omega
  have hmna : m * n ≤ a := by omega
  have hnX : 7935 * n ≤ 64 * X ∧ 63 * X ≤ 7935 * n + 7935 := by rcases hK with rfl | rfl <;> omega
  refine ⟨m, n, hn16, by rw [hsucc]; exact hamn, hmna, by omega, by omega, by norm_num; omega,
    by rcases hK with rfl | rfl <;> omega, by omega, ?_, ?_⟩
  · have h1 : (63 : ℝ) * X ≤ 7935 * n + 7935 := by exact_mod_cast hnX.2
    have h2 : (16777216 : ℝ) ≤ X := by exact_mod_cast hX
    unfold mu; push_cast
    nlinarith
  · have h1 : (7935 : ℝ) * n ≤ 64 * X := by exact_mod_cast hnX.1
    have h3 : ((m + 1 : ℕ) : ℝ) * n ≤ 525312 * X + n := by
      have : (m + 1) * n ≤ 525312 * X + n := by rw [hsucc]; omega
      exact_mod_cast this
    rw [gamma_def]; unfold epsB eta mu; push_cast at h3 ⊢
    nlinarith

/-- **Class `f = 406109`.** -/
theorem geomB (a π X : ℕ) (hπ : π / 2 = 63 * X)
    (hL : 8176 * X ≤ a) (hH : a ≤ 8192 * X) (hX : 16777216 ≤ X) :
    ∃ m n : ℕ, 16 ≤ n ∧ a ≤ (m + 1) * n ∧ m * n ≤ a ∧ 406109 ≤ m ∧ 50859009 ≤ m + 1 ∧
      m + 1 ≤ 2 ^ 26 ∧ π / 2 ≤ a ∧ (406109 + 1) * n ≤ π / 2 ∧
      ((mu : ℚ) : ℝ) * ((524288 * X : ℕ) : ℝ) ≤ 1 / 8 * ((406109 : ℝ) * n) ∧
      (1 / 105000 : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤
        ((((epsB * eta + gammaRes) * ((524288 * X : ℕ) : ℚ) / 2 : ℚ)) : ℝ) := by
  have hn1 := Nat.div_add_mod (π / 2) 406110
  have hn2 := Nat.mod_lt (π / 2) (show 406110 > 0 by norm_num)
  set n := π / 2 / 406110 with hn
  have hn16 : 16 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hm1 := Nat.div_add_mod (a - 1) n
  have hm2 := Nat.mod_lt (a - 1) hnpos
  set m := (a - 1) / n with hm
  have hmn : n * m = m * n := Nat.mul_comm _ _
  have hlo : 50859008 ≤ m := by
    by_contra h
    have h' : m * n ≤ 50859007 * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hhi : m < 67108864 := by
    by_contra h
    have h' : 67108864 * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hsucc : (m + 1) * n = m * n + n := by ring
  have hamn : a ≤ m * n + n := by omega
  have hmna : m * n ≤ a := by omega
  have hnX : 406110 * n ≤ 63 * X ∧ 63 * X ≤ 406110 * n + 406110 := by omega
  refine ⟨m, n, hn16, by rw [hsucc]; exact hamn, hmna, by omega, by omega, by norm_num; omega,
    by omega, by omega, ?_, ?_⟩
  · have h1 : (63 : ℝ) * X ≤ 406110 * n + 406110 := by exact_mod_cast hnX.2
    have h2 : (16777216 : ℝ) ≤ X := by exact_mod_cast hX
    unfold mu; push_cast
    nlinarith
  · have h1 : (406110 : ℝ) * n ≤ 63 * X := by exact_mod_cast hnX.1
    have h3 : ((m + 1 : ℕ) : ℝ) * n ≤ 8192 * X + n := by
      have : (m + 1) * n ≤ 8192 * X + n := by rw [hsucc]; omega
      exact_mod_cast this
    rw [gamma_def]; unfold epsB eta mu; push_cast at h3 ⊢
    nlinarith

/-! ### Depths -/

theorem budget26 : bitonicDepthBudget 26 = 351 := by rw [bitonicDepthBudget_eq]
theorem budget42 : bitonicDepthBudget 42 = 903 := by rw [bitonicDepthBudget_eq]
theorem budget45 : bitonicDepthBudget 45 = 1035 := by rw [bitonicDepthBudget_eq]

theorem padded_depth {m n a : ℕ} (hn : 0 < n) (ha : a ≤ (m + 1) * n) (σ1 σ2 : Scramble (m + 1) n)
    (hm : m + 1 ≤ 2 ^ 26) : (paddedPack2Net hn ha σ1 σ2).depth ≤ 1053 := by
  refine (paddedPack2Net_depth_le hn ha σ1 σ2).trans
    ((physicalPack2Net_depth_le_budget _ _ hn σ1 σ2).trans ?_)
  have := bitonicDepthBudget_mono (Nat.clog_le_of_le_pow hm)
  rw [budget26] at this
  omega

/-! ### Node networks -/

theorem epsF_real : ((epsF : ℚ) : ℝ) = 1 / (190000 : ℝ) := by unfold epsF; push_cast; ring

open Classical in
/-- **The padded separator with fringe class `P`.** -/
theorem spec_padded (P : F2PD)
    (hF : ∀ {m n : ℕ}, 16 ≤ n →
      ((Finset.univ.filter fun σ : Scramble m n => ¬ SRd P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n) ∧
        ((Finset.univ.filter fun σ : Scramble m n => ¬ R1d P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n) ∧
        ((Finset.univ.filter fun σ : Scramble m n => ¬ R2nd P σ).card : ℝ) ≤
          (1 / 10000) * Fintype.card (Scramble m n))
    (hPJ : (P.J : ℝ) = 190000)
    {a π : ℕ} (m n : ℕ) (hn16 : 16 ≤ n) (ha : a ≤ (m + 1) * n) (hlive : m * n ≤ a)
    (hfm : P.f ≤ m) (hmlo : 50859009 ≤ m + 1) (hmhi : m + 1 ≤ 2 ^ 26) (hπa : π / 2 ≤ a)
    (hfr : (P.f + 1) * n ≤ π / 2) (Jmax : ℕ) (hJ : Jmax ≤ P.jmax n) (EB : ℝ)
    (hEB : (1 / 105000 : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤ EB) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net EB Jmax ((epsF : ℚ) : ℝ) ∧ net.depth ≤ 1053 := by
  have hn : 0 < n := by omega
  obtain ⟨σ1, σ2, hgood⟩ := sep_pair_exists_of P hF (m := m) (n := n) (by exact_mod_cast hmlo) hmhi hn16
  refine ⟨paddedPack2Net hn ha σ1 σ2, ?_, padded_depth hn ha σ1 σ2 hmhi⟩
  have := nodeSpec_padded P hn ha hlive hfm σ1 σ2 hgood π hπa hfr Jmax hJ EB hEB
  rwa [epsF_real, ← hPJ]

/-- **The B-only separator**, `n = ⌈a/2^26⌉` (no fringe). -/
theorem spec_Bonly {a : ℕ} (π : ℕ) (ha45 : 2 ^ 45 < a) (EB εF : ℝ)
    (hEB : (1 / 105000 : ℝ) / 2 * ((a : ℝ) + a / 2 ^ 26 + 1) + (a / 2 ^ 26 + 1) ≤ EB) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net EB 0 εF ∧ net.depth ≤ 1053 := by
  have hn1 := Nat.div_add_mod (a + 67108863) 67108864
  have hn2 := Nat.mod_lt (a + 67108863) (show 67108864 > 0 by norm_num)
  set n := (a + 67108863) / 67108864 with hn
  have h45 : (35184372088832 : ℕ) < a := by norm_num at ha45; exact ha45
  have hn16 : 16 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hm1 := Nat.div_add_mod (a - 1) n
  have hm2 := Nat.mod_lt (a - 1) hnpos
  set m := (a - 1) / n with hm
  have hmn : n * m = m * n := Nat.mul_comm _ _
  have hhi : m < 67108864 := by
    by_contra h
    have h' : 67108864 * n ≤ m * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hlo : 50859008 ≤ m := by
    by_contra h
    have h' : m * n ≤ 50859007 * n := Nat.mul_le_mul_right n (by omega)
    omega
  have hsucc : (m + 1) * n = m * n + n := by ring
  have ha : a ≤ (m + 1) * n := by rw [hsucc]; omega
  obtain ⟨σ1, σ2, hgood⟩ := sep_pair_exists_of Fringe7934.P Fringe7934.fringe_fail (m := m) (n := n)
    (by exact_mod_cast (show 50859009 ≤ m + 1 by omega)) (by norm_num; omega) hn16
  refine ⟨paddedPack2Net hnpos ha σ1 σ2, ?_, padded_depth hnpos ha σ1 σ2 (by norm_num; omega)⟩
  refine nodeSpec_Bonly hnpos ha σ1 σ2 (1 / 105000) (by norm_num) hgood.1.2.2.2 hgood.2.2.2.2 π EB εF
    (le_trans ?_ hEB)
  have hnR : (n : ℝ) ≤ a / 2 ^ 26 + 1 := by
    have : (67108864 : ℝ) * n ≤ a + 67108863 := by exact_mod_cast (show 67108864 * n ≤ a + 67108863 by omega)
    norm_num; linarith
  have hMR : ((m + 1 : ℕ) : ℝ) * n ≤ a + n := by
    have : (m + 1) * n ≤ a + n := by rw [hsucc]; omega
    exact_mod_cast this
  linarith

/-- **Batcher's sort** for `a ≤ 2^45`. -/
theorem spec_sorter {a : ℕ} (π : ℕ) (ha : a ≤ 2 ^ 45) {EB εF : ℝ} (hEB : 0 ≤ EB) (hε : 0 < εF)
    {Jmax : ℕ} (hJ : Jmax ≤ π / 2) :
    ∃ net : ComparatorNetwork a, NodeSpecAll a π net EB Jmax εF ∧ net.depth ≤ 1053 := by
  refine ⟨bitonicNetwork a, nodeSpec_sorter π _ (bitonicNetwork_sorts a) hEB hε hJ, ?_⟩
  refine (bitonicNetwork_depth_le_budget a).trans ?_
  have := bitonicDepthBudget_mono (Nat.clog_le_of_le_pow ha)
  rw [budget45] at this
  omega

/-- **The root at `t = 0`**: the package's B2 separator on `2^42` rows. -/
theorem spec_root {d : ℕ} (hd : 12 ≤ d) (π : ℕ) (EB εF : ℝ)
    (hEB : (1 / 59000000 : ℝ) / 2 * (16 : ℝ) ^ d + 2 ^ (4 * d - 42) ≤ EB) :
    ∃ net : ComparatorNetwork (16 ^ d), NodeSpecAll (16 ^ d) π net EB 0 εF ∧ net.depth ≤ 2709 := by
  set n := 2 ^ (4 * d - 42) with hn
  have hn16 : 16 ≤ n := by
    rw [hn, show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnpos : 0 < n := by omega
  have hmn : 16 ^ d = 2 ^ 42 * n := by
    rw [hn, ← pow_add, show 42 + (4 * d - 42) = 4 * d by omega, pow_mul]; norm_num
  have ha : 16 ^ d ≤ 2 ^ 42 * n := hmn.le
  obtain ⟨σ1, σ2, ⟨-, hB⟩, ⟨-, hB'⟩⟩ := ExistsScrambleSeparator_twoSided_B2 (m := 2 ^ 42) (n := n)
    le_rfl hn16 (fun _ => True) (by
      simp only [not_true_eq_false, Finset.filter_False, Finset.card_empty, Nat.cast_zero]
      positivity)
  refine ⟨paddedPack2Net hnpos ha σ1 σ2, ?_, ?_⟩
  · refine nodeSpec_Bonly hnpos ha σ1 σ2 (1 / 59000000) (by norm_num) hB hB' π EB εF (le_trans ?_ hEB)
    have : ((2 ^ 42 : ℕ) : ℝ) * (n : ℝ) = (16 : ℝ) ^ d := by exact_mod_cast hmn.symm
    rw [this, hn]; push_cast; exact le_refl _
  · refine (paddedPack2Net_depth_le hnpos ha σ1 σ2).trans
      ((physicalPack2Net_depth_le_budget _ _ hnpos σ1 σ2).trans ?_)
    rw [Nat.clog_pow 2 42 (by norm_num), budget42]

end R1T
