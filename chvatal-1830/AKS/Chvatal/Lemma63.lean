module

/- Chvátal Lemma 6.3 (DCS-TR-294 §6): a Hoeffding bound for scrambles via the
hypergeometric-to-binomial MGF comparison. -/

public import AKS.Chvatal.Lemma61
public import AKS.Halver.MatchingCount
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

namespace Chvatal

def rowHit {m n : Nat} (c : MonotoneColumnSums m n)
    (S : Finset (Fin n)) (r : Fin m) (π : Equiv.Perm (Fin n)) : ℕ :=
  (((monotoneRowOnes c r).image π) ∩ S).card

theorem onesInColumns_eq_sum_rowHit {m n : Nat}
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n) :
    onesInColumns c σ S = ∑ r : Fin m, rowHit c S r (σ r) := by
  simp [onesInColumns, rowHit, scrambledRowOnes]

theorem card_perm_supset_image {n : Nat} (A T : Finset (Fin n)) :
    Fintype.card {π : Equiv.Perm (Fin n) // T ⊆ A.image π} =
      A.card.descFactorial T.card * (n - T.card).factorial := by
  classical
  have e : {π : Equiv.Perm (Fin n) // T ⊆ A.image π} ≃
      {π : Equiv.Perm (Fin n) // ∀ t ∈ T, π t ∈ A} :=
    Equiv.subtypeEquiv (Equiv.inv _) fun π => by
      refine forall₂_congr fun t _ => ?_
      simp only [Finset.mem_image, Equiv.Perm.inv_def, Equiv.inv_apply]
      exact ⟨fun ⟨a, ha, h⟩ => h ▸ by simpa using ha, fun h => ⟨_, h, by simp⟩⟩
  rw [Fintype.card_congr e]
  convert Paterson.card_restricted_permutations T A using 2
  simp

theorem sum_hit_choose {n : Nat} (A S : Finset (Fin n)) (k : Nat) :
    ∑ π : Equiv.Perm (Fin n), (((A.image π) ∩ S).card.choose k) =
      S.card.choose k * A.card.descFactorial k * (n - k).factorial := by
  classical
  have h (π : Equiv.Perm (Fin n)) : ((A.image π) ∩ S).card.choose k =
      ∑ T ∈ Finset.powersetCard k S, if T ⊆ A.image π then 1 else 0 := by
    rw [← Finset.card_filter, ← Finset.card_powersetCard]
    congr 1
    ext T
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_inter_iff]
    tauto
  have h2 : ∀ T ∈ Finset.powersetCard k S,
      ∑ π : Equiv.Perm (Fin n), (if T ⊆ A.image π then 1 else 0) =
        A.card.descFactorial k * (n - k).factorial := fun T hT => by
    rw [← Finset.card_filter, ← Fintype.card_subtype, card_perm_supset_image,
      (Finset.mem_powersetCard.1 hT).2]
  simp_rw [h]
  rw [Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_powersetCard,
    smul_eq_mul, mul_assoc]

theorem avg_hit_choose {n : Nat} (hn : 0 < n) (A S : Finset (Fin n)) (k : Nat) :
    (∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k := by
  have hsum : (∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) =
      S.card.choose k * A.card.descFactorial k * (n - k).factorial := by
    exact_mod_cast sum_hit_choose A S k
  have hA : A.card ≤ n := by simpa using Finset.card_le_univ A
  rw [hsum, Fintype.card_perm, Fintype.card_fin]
  by_cases hk : k ≤ n
  · have hdf : (0 : ℝ) < n.descFactorial k := by exact_mod_cast Nat.descFactorial_pos.2 hk
    have hfac : (n.factorial : ℝ) = n.descFactorial k * (n - k).factorial := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hk).symm.trans (mul_comm _ _)
    have h' : (n : ℝ) ^ k * A.card.descFactorial k ≤ (A.card : ℝ) ^ k * n.descFactorial k := by
      exact_mod_cast Paterson.descFactorial_ratio_le_pow n A.card k hA
    have hle : (A.card.descFactorial k : ℝ) / n.descFactorial k ≤ ((A.card : ℝ) / n) ^ k := by
      have : (0 : ℝ) < (n : ℝ) ^ k := by positivity
      rw [div_pow, div_le_div_iff₀ hdf this]
      linarith
    have : ((n - k).factorial : ℝ) ≠ 0 := by positivity
    calc _ = (S.card.choose k : ℝ) * (A.card.descFactorial k / n.descFactorial k) := by
          rw [hfac]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (by omega : A.card < k)]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div]
    positivity

/-- Hoeffding bound for a Bernoulli trial: `(1-p+p e^t) ≤ exp(p t + t²/8)`. -/
theorem bernoulli_one_sub_add_mul_exp_le {prob t : ℝ} (hprob0 : 0 ≤ prob) (hprob1 : prob ≤ 1) :
    1 - prob + prob * Real.exp t ≤ Real.exp (prob * t + t ^ 2 / 8) := by
  open ProbabilityTheory MeasureTheory in
  let pnn : NNReal := ⟨prob, hprob0⟩
  have hpnn_le_one : pnn ≤ 1 := by exact_mod_cast hprob1
  let μ : Measure Bool := (PMF.bernoulli pnn hpnn_le_one).toMeasure
  haveI : IsProbabilityMeasure μ := inferInstance
  let X : Bool → ℝ := fun b => cond b 1 0
  have hb : ∀ᵐ b ∂μ, X b ∈ Set.Icc 0 1 := by
    filter_upwards with b
    cases b <;> simp [X, Set.mem_Icc]
  have hEX : ∫ x, X x ∂μ = prob := by
    simpa [X, μ, pnn, hpnn_le_one] using PMF.bernoulli_expectation hpnn_le_one
  have hcoeff : ((‖(1 : ℝ) - 0‖₊ / 2 : NNReal) ^ 2 : ℝ) * t ^ 2 / 2 = t ^ 2 / 8 := by
    have h₁ : (‖(1 : ℝ) - 0‖₊ / 2 : NNReal) = 1 / 2 := by ext; norm_num
    simp only [h₁]
    norm_num
    ring
  have hcent : mgf (fun b => X b - prob) μ t ≤ Real.exp (t ^ 2 / 8) := by
    have h := (hasSubgaussianMGF_of_mem_Icc .of_discrete hb).mgf_le t
    convert h using 1
    · congr 1
      funext b
      simp [hEX]
    · congr 1
      exact hcoeff.symm
  have hmgfX : mgf X μ t = 1 - prob + prob * Real.exp t := by
    simp only [mgf]
    rw [PMF.integral_eq_sum, Fintype.sum_bool]
    simp [X, PMF.bernoulli_apply, pnn, hpnn_le_one]
    ring
  have hshift : mgf (fun b => X b - prob) μ t = Real.exp (-prob * t) * mgf X μ t := by
    rw [show (fun b => X b - prob) = fun b => X b + (-prob) from funext fun _ => by ring,
      mgf_add_const]
    ring_nf
  rw [hshift, hmgfX] at hcent
  calc 1 - prob + prob * Real.exp t
      = Real.exp (prob * t) * (Real.exp (-prob * t) * (1 - prob + prob * Real.exp t)) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (prob * t) * Real.exp (t ^ 2 / 8) := by gcongr
    _ = _ := by rw [← Real.exp_add, add_comm]

/-- `e^{lam·H} = ∑_{k ≤ N} (e^{lam}-1)^k C(H,k)` for `H ≤ N`. -/
theorem exp_mul_nat_eq_sum_choose (lam : ℝ) {H N : ℕ} (h : H ≤ N) :
    Real.exp (lam * H) =
      ∑ k ∈ Finset.range (N + 1), (Real.exp lam - 1) ^ k * (H.choose k : ℝ) := by
  have := add_pow (Real.exp lam - 1) 1 H
  simp only [sub_add_cancel, one_pow, mul_one] at this
  rw [mul_comm, Real.exp_nat_mul, this]
  refine Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hk' => ?_
  simp only [Finset.mem_range] at hk hk'
  simp [Nat.choose_eq_zero_of_lt (by omega : H < k)]

/-- Average row-hit MGF ≤ binomial MGF `(1-p+p e^lam)^|S|`. -/
theorem avg_exp_hit_le {n : Nat} (hn : 0 < n) (A S : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∑ π : Equiv.Perm (Fin n), Real.exp (lam * (((A.image π) ∩ S).card : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (1 - ((A.card : ℝ) / n) + ((A.card : ℝ) / n) * Real.exp lam) ^ S.card := by
  classical
  have hx : 0 ≤ Real.exp lam - 1 := sub_nonneg.mpr (Real.one_le_exp hlam)
  have hexp (π : Equiv.Perm (Fin n)) :
      Real.exp (lam * (((A.image π) ∩ S).card : ℝ)) =
        ∑ k ∈ Finset.range (S.card + 1),
          (Real.exp lam - 1) ^ k * ((((A.image π) ∩ S).card.choose k : ℝ)) :=
    exp_mul_nat_eq_sum_choose lam (Finset.card_le_card Finset.inter_subset_right)
  calc _ = ∑ k ∈ Finset.range (S.card + 1), (Real.exp lam - 1) ^ k *
          ((∑ π : Equiv.Perm (Fin n), ((((A.image π) ∩ S).card.choose k : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) := by
        simp_rw [hexp]
        rw [Finset.sum_comm, Finset.sum_div]
        simp only [← Finset.mul_sum, mul_div_assoc]
    _ ≤ ∑ k ∈ Finset.range (S.card + 1), (Real.exp lam - 1) ^ k *
          ((S.card.choose k : ℝ) * ((A.card : ℝ) / n) ^ k) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_left (avg_hit_choose hn A S k) (pow_nonneg hx _)
    _ = _ := by
        have := add_pow (((A.card : ℝ) / n) * (Real.exp lam - 1)) 1 S.card
        simp only [one_pow, mul_one] at this
        rw [show 1 - (A.card : ℝ) / n + (A.card : ℝ) / n * Real.exp lam =
          ((A.card : ℝ) / n) * (Real.exp lam - 1) + 1 by ring, this]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_pow]; ring

theorem card_scramble (m n : Nat) :
    Fintype.card (Scramble m n) = Fintype.card (Equiv.Perm (Fin n)) ^ m := by
  simp [Scramble, Fintype.card_fin]

theorem avg_exp_rowHit_le {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (r : Fin m) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    (∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
        Fintype.card (Equiv.Perm (Fin n)) ≤
      (1 - ((monotoneRowOnes c r).card : ℝ) / n +
        ((monotoneRowOnes c r).card : ℝ) / n * Real.exp lam) ^ S.card := by
  simpa [rowHit] using avg_exp_hit_le hn (monotoneRowOnes c r) S lam hlam

theorem row_density_le_one {m n : Nat} (hn : 0 < n)
    (c : MonotoneColumnSums m n) (r : Fin m) :
    ((monotoneRowOnes c r).card : ℝ) / n ≤ 1 := by
  have hcard : (monotoneRowOnes c r).card ≤ n := by
    simpa [Fintype.card_fin] using (monotoneRowOnes c r).card_le_univ
  exact (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast hcard)

theorem avg_exp_onesInColumns_le {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 ≤ lam) :
    let p := (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)
    (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
        Fintype.card (Scramble m n) ≤
      Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) := by
  intro p
  classical
  have hσ (σ : Scramble m n) :
      Real.exp (lam * (onesInColumns c σ S : ℝ)) =
        ∏ r : Fin m, Real.exp (lam * (rowHit c S r (σ r) : ℝ)) := by
    have := congrArg (Nat.cast (R := ℝ)) (onesInColumns_eq_sum_rowHit c S σ)
    push_cast at this
    rw [this, Finset.mul_sum, Real.exp_sum]
  have havg_prod :
      (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
          Fintype.card (Scramble m n) =
        ∏ r : Fin m,
          ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) := by
    have hps : ∑ σ : Scramble m n, ∏ r : Fin m, Real.exp (lam * (rowHit c S r (σ r) : ℝ)) =
        ∏ r : Fin m, ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ)) :=
      (Fintype.prod_sum fun (r : Fin m) (π : Equiv.Perm (Fin n)) =>
        Real.exp (lam * (rowHit c S r π : ℝ))).symm
    simp_rw [hσ]
    rw [hps, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      card_scramble]
    push_cast
    rfl
  have hrow (r : Fin m) :
      ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
          Fintype.card (Equiv.Perm (Fin n))) ≤
        Real.exp (((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) * (S.card : ℝ)) := by
    set pr : ℝ := ((monotoneRowOnes c r).card : ℝ) / n
    have hp0 : (0 : ℝ) ≤ pr := by positivity
    have hp1 : pr ≤ 1 := row_density_le_one hn c r
    have hbase : (0 : ℝ) ≤ 1 - pr + pr * Real.exp lam := by
      have := mul_nonneg hp0 (Real.exp_nonneg lam)
      linarith
    calc _ ≤ (1 - pr + pr * Real.exp lam) ^ S.card := avg_exp_rowHit_le hn c S r lam hlam
      _ ≤ (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card :=
        pow_le_pow_left₀ hbase (bernoulli_one_sub_add_mul_exp_le hp0 hp1) _
      _ = _ := by rw [← Real.exp_nat_mul, mul_comm]
  rw [havg_prod]
  refine (Finset.prod_le_prod (fun _ _ => by positivity) fun r _ => hrow r).trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr (le_of_eq ?_)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : ∑ r : Fin m, ((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) *
        (S.card : ℝ) =
      (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / n * lam * S.card +
        m * (lam ^ 2 / 8 * S.card) := by
    simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum]
  simp only [p]
  generalize (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) = T
  field_simp <;> ring

theorem lemma63ExpBound {m n : Nat} (hm : 0 < m) (hn : 0 < n) (c : MonotoneColumnSums m n)
    (S : Finset (Fin n)) (t : ℝ) (ht : 0 < t) (bad : Finset (Scramble m n))
    (hbad : ∀ σ ∈ bad, ((∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n) + t) * m *
      S.card ≤ (onesInColumns c σ S : ℝ)) :
    (bad.card : ℝ) ≤ Real.exp (-(2 * t ^ 2 * m * S.card)) * (Fintype.card (Scramble m n) : ℝ) := by
  classical
  set p : ℝ := (∑ r : Fin m, ((monotoneRowOnes c r).card : ℝ)) / (m * n)
  set lam : ℝ := 4 * t
  have hlam : 0 ≤ lam := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht.le
  set thresh : ℝ := (p + t) * m * S.card
  have hmarkov :
      (bad.card : ℝ) ≤
        Real.exp (-lam * thresh) *
          ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
    have hone (σ : Scramble m n) (hσ : σ ∈ bad) :
        (1 : ℝ) ≤
          Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) := by
      have hX : thresh ≤ (onesInColumns c σ S : ℝ) := by
        simpa [thresh, p] using hbad σ hσ
      exact Real.one_le_exp (mul_nonneg hlam (sub_nonneg.mpr hX))
    have hsplit (σ : Scramble m n) :
        Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) =
          Real.exp (-lam * thresh) *
            Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
      have : lam * ((onesInColumns c σ S : ℝ) - thresh) =
          lam * (onesInColumns c σ S : ℝ) + (-lam * thresh) := by ring
      rw [this, Real.exp_add, mul_comm]
    calc (bad.card : ℝ)
        = ∑ σ ∈ bad, (1 : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ bad,
            Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) :=
              Finset.sum_le_sum fun σ hσ => hone σ hσ
      _ ≤ ∑ σ : Scramble m n,
            Real.exp (lam * ((onesInColumns c σ S : ℝ) - thresh)) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                fun _ _ _ => Real.exp_nonneg _
      _ = ∑ σ : Scramble m n,
            Real.exp (-lam * thresh) *
              Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
                simp_rw [hsplit]
      _ = Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) := by
                rw [← Finset.mul_sum]
  have hmgf := avg_exp_onesInColumns_le hm hn c S lam hlam
  have htotpos : (0 : ℝ) < Fintype.card (Scramble m n) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
  have hcombine :
      Real.exp (-lam * thresh) *
          ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
        Real.exp (-(2 * t ^ 2 * m * S.card)) *
          (Fintype.card (Scramble m n) : ℝ) := by
    have havg :
        (∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))) /
            Fintype.card (Scramble m n) ≤
          Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) := by
      simpa [p] using hmgf
    have hsum_le :
        ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
          Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
            (Fintype.card (Scramble m n) : ℝ) := by
      have := (div_le_iff₀ htotpos).mp havg
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (-lam * thresh) := Real.exp_nonneg _
    have hstep1 :
        Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ)) ≤
          Real.exp (-lam * thresh) *
            (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum_le hexp_nonneg
    have hstep2 :
        Real.exp (-lam * thresh) *
            (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ)) =
          Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
            (Fintype.card (Scramble m n) : ℝ) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
    have hstep3 :
        Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) =
          Real.exp (-(2 * t ^ 2 * m * S.card)) := by
      congr 1
      -- lam = 4t, thresh = (p+t) m |S|
      change -(4 * t) * ((p + t) * m * S.card) + (4 * t) * p * m * S.card +
          m * S.card * (4 * t) ^ 2 / 8 =
        -(2 * t ^ 2 * m * S.card)
      ring
    calc Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesInColumns c σ S : ℝ))
        ≤ Real.exp (-lam * thresh) *
            (Real.exp (lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ)) := hstep1
      _ = Real.exp (-lam * thresh + lam * p * m * S.card + m * S.card * lam ^ 2 / 8) *
            (Fintype.card (Scramble m n) : ℝ) := hstep2
      _ = Real.exp (-(2 * t ^ 2 * m * S.card)) *
            (Fintype.card (Scramble m n) : ℝ) := by rw [hstep3]
  exact hmarkov.trans hcombine

/-- Hypotheses for the pipeline-class Lemma 6.1 union bound. -/
structure DecodeMatrixClassObligation (m n : Nat) (epsB : ℝ) where
  hm : 0 < m
  hn : 0 < n
  heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB

def DecodeMatrixClassObligation.standard {m n : Nat} {epsB : ℝ} (hm : 0 < m) (hn : 0 < n)
    (_ : 1 ≤ m) (_ : 1 ≤ n) (heps : Real.sqrt (2 * (1 + Real.log m) / m) ≤ epsB) :
    DecodeMatrixClassObligation m n epsB := ⟨hm, hn, heps⟩

end Chvatal
