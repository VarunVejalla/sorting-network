module
/-
  # Chvátal Lemma 6.2 — fringe-row product Chernoff

  Clones the scramble MGF and exp bound from Lemma 6.3, restricted to rows in
  `aboveHalfFringeRows`. Status: kernel-checked (`avg_exp_onesAboveHalfFringe_le`,
  `lemma62FringeExpBound`, paper bad-event ⇒ Chernoff threshold under
  `FringeOnesDensityLeHalfWidth`, `lemma62_exp_bound`, `Lemma62FringeCellBound.of_hyp`).
-/

public import AKS.Chvatal.Lemma62
public import AKS.Chvatal.Theorem51
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Chvatal

/-! ## Fringe-row MGF factorization -/

private def fringeRowMGFHit {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (r : Fin m) (π : Equiv.Perm (Fin n)) : ℝ :=
  if r ∈ aboveHalfFringeRows m f hf then (rowHit c S r π : ℝ) else (0 : ℝ)

private theorem onesAboveHalfFringe_eq_sum_mgfHit {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n) :
    (onesAboveHalfFringe hf c σ S : ℝ) =
      ∑ r : Fin m, fringeRowMGFHit hf c S r (σ r) := by
  classical
  have h :
      onesAboveHalfFringe hf c σ S =
        ∑ r : Fin m, if r ∈ aboveHalfFringeRows m f hf then rowHit c S r (σ r) else 0 := by
    rw [onesAboveHalfFringe_eq_sum_rowHit, aboveHalfFringeRows, Finset.sum_filter]
    congr 1
    ext r
    simp [Finset.mem_filter, Finset.mem_univ, and_self]
  rw [h, Nat.cast_sum]
  congr 1
  ext r
  simp [fringeRowMGFHit]

private theorem fringeRowExp_prod {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (σ : Scramble m n) (lam : ℝ) :
    Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) =
      ∏ r : Fin m, Real.exp (lam * fringeRowMGFHit hf c S r (σ r)) := by
  have hsum := onesAboveHalfFringe_eq_sum_mgfHit hf c S σ
  rw [hsum, Finset.mul_sum, Real.exp_sum]

private theorem sum_scramble_exp_onesAboveHalfFringe {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (lam : ℝ) :
    let R := aboveHalfFringeRows m f hf
    ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) =
      (∏ r ∈ R,
          ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) *
        (Fintype.card (Equiv.Perm (Fin n)) ^ (m - R.card)) := by
  classical
  intro R
  set permCard : Nat := Fintype.card (Equiv.Perm (Fin n))
  have hσ (σ : Scramble m n) :
      Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) =
        ∏ r : Fin m, Real.exp (lam * fringeRowMGFHit hf c S r (σ r)) :=
    fringeRowExp_prod hf c S σ lam
  simp_rw [hσ]
  have hprod_sum :
      ∑ σ : Scramble m n,
          ∏ r : Fin m, Real.exp (lam * fringeRowMGFHit hf c S r (σ r)) =
        ∏ r : Fin m,
          ∑ π : Equiv.Perm (Fin n), Real.exp (lam * fringeRowMGFHit hf c S r π) := by
    exact (Fintype.prod_sum
        (fun (r : Fin m) (π : Equiv.Perm (Fin n)) =>
          Real.exp (lam * fringeRowMGFHit hf c S r π))).symm
  rw [hprod_sum]
  have hrow (r : Fin m) :
      ∑ π : Equiv.Perm (Fin n), Real.exp (lam * fringeRowMGFHit hf c S r π) =
        if r ∈ R then
          ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))
        else (permCard : ℝ) := by
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      simp [fringeRowMGFHit, show r ∈ aboveHalfFringeRows m f hf from hr]
    · rw [if_neg hr]
      have h1 (π : Equiv.Perm (Fin n)) :
          Real.exp (lam * fringeRowMGFHit hf c S r π) = 1 := by
        have h0 : fringeRowMGFHit hf c S r π = 0 := by
          unfold fringeRowMGFHit
          rw [if_neg (show r ∉ aboveHalfFringeRows m f hf from hr)]
        rw [h0, mul_zero, Real.exp_zero]
      rw [Finset.sum_congr rfl fun π _ => h1 π]
      simp [Finset.sum_const, permCard, nsmul_eq_mul, one_mul, Fintype.card_fin]
  have hprod :
      ∏ r : Fin m,
          ∑ π : Equiv.Perm (Fin n), Real.exp (lam * fringeRowMGFHit hf c S r π) =
        (∏ r ∈ R,
            ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) *
          permCard ^ (Finset.univ \ R).card := by
    calc ∏ r : Fin m,
            ∑ π : Equiv.Perm (Fin n), Real.exp (lam * fringeRowMGFHit hf c S r π)
        = ∏ r : Fin m, (if r ∈ R then
              ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))
            else (permCard : ℝ)) := by
            refine Finset.prod_congr rfl fun r _ => ?_
            rw [hrow r]
      _ = (∏ r ∈ R,
              ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) *
            ∏ r ∈ Finset.univ \ R, (permCard : ℝ) := by
            rw [Finset.prod_ite (s := (Finset.univ : Finset (Fin m))) (p := fun r => r ∈ R)
              (f := fun r => ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ)))
              (g := fun _ => (permCard : ℝ))]
            simp [Finset.filter_mem_eq_inter, ← Finset.sdiff_eq_filter]
      _ = (∏ r ∈ R,
              ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) *
            permCard ^ (Finset.univ \ R).card := by
            rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ R)]
  rw [hprod]
  have hcard_eq : (Finset.univ \ R).card = m - R.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin]
  rw [hcard_eq]

private theorem avg_exp_fringeRow_prod {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (lam : ℝ) :
    let R := aboveHalfFringeRows m f hf
    (∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ))) /
        Fintype.card (Scramble m n) =
      ∏ r ∈ R,
        ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
          Fintype.card (Equiv.Perm (Fin n))) := by
  classical
  intro R
  set permCard : Nat := Fintype.card (Equiv.Perm (Fin n))
  have hcard :
      (Fintype.card (Scramble m n) : ℝ) = (permCard : ℝ) ^ m := by
    exact_mod_cast card_scramble m n
  have hsum := sum_scramble_exp_onesAboveHalfFringe hf c S lam
  have hpermpos : (0 : ℝ) < permCard := by
    exact_mod_cast (Fintype.card_pos : 0 < permCard)
  have hpow_ne : (permCard : ℝ) ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hpermpos)
  have hRle : R.card ≤ m := by
    have := Finset.card_le_card (Finset.subset_univ R)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hadd : R.card + (m - R.card) = m := Nat.add_sub_of_le hRle
  rw [hsum, hcard, show (Fintype.card (Equiv.Perm (Fin n))) = permCard from rfl,
    show aboveHalfFringeRows m f hf = R from rfl, show (aboveHalfFringeRows m f hf).card = R.card from rfl]
  have hd : (permCard : ℝ) ≠ 0 := ne_of_gt hpermpos
  calc (∏ r ∈ R, ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) *
          (permCard : ℝ) ^ (m - R.card) / (permCard : ℝ) ^ m
      = (∏ r ∈ R, ∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
          (permCard : ℝ) ^ R.card := by
        field_simp [hpow_ne]
        rw [← pow_add, Nat.add_comm (m - R.card) R.card, hadd]
    _ = ∏ r ∈ R,
          ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) / permCard) := by
        rw [Finset.prod_div_distrib, Finset.prod_const]

/-! ## Fringe average MGF (clone of `avg_exp_onesInColumns_le`) -/

theorem avg_exp_onesAboveHalfFringe_le {m n f : Nat} (hf : Even f) (hn : 0 < n)
    (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (lam : ℝ) (hlam : 0 ≤ lam) :
    let mF := fringeRowCount m f hf
    let p := fringeOnesDensity hf c
    (∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ))) /
        Fintype.card (Scramble m n) ≤
      Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) := by
  classical
  intro mF p
  set R := aboveHalfFringeRows m f hf
  set totalOnes : ℝ := ∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)
  have hmF_eq : mF = R.card := rfl
  have havg_prod := avg_exp_fringeRow_prod hf c S lam
  rw [havg_prod]
  by_cases hmF0 : mF = 0
  · have hR : R = ∅ := Finset.card_eq_zero.mp (hmF_eq.trans hmF0)
    rw [show aboveHalfFringeRows m f hf = ∅ from hR]
    have hp0 : p = 0 := by
      dsimp [p, fringeOnesDensity, fringeRowCount]
      split_ifs with h
      · rfl
      · exfalso
        exact h (hmF_eq.trans hmF0)
    rw [hp0, hmF0]
    simp only [Finset.prod_empty]
    norm_num [Real.exp_zero]
  · have hmFpos : 0 < mF := Nat.pos_of_ne_zero hmF0
    have hRcard : R.card = mF := hmF_eq.symm
    have hp_def : p = totalOnes / (mF * n) := by
      dsimp [p, fringeOnesDensity, fringeRowCount]
      split_ifs with h
      · exfalso
        exact hmF0 h
      · rfl
    have hrow (r : Fin m) (hr : r ∈ R) :
        ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
            Fintype.card (Equiv.Perm (Fin n))) ≤
          Real.exp
            (((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) *
              (S.card : ℝ)) := by
      set pr : ℝ := ((monotoneRowOnes c r).card : ℝ) / n
      have hp0 : (0 : ℝ) ≤ pr := by positivity
      have hp1 : pr ≤ 1 := row_density_le_one hn c r
      have hbin := avg_exp_rowHit_le hn c S r lam hlam
      have hbern := bernoulli_one_sub_add_mul_exp_le hp0 hp1 hlam
      have hbase : (0 : ℝ) ≤ 1 - pr + pr * Real.exp lam := by
        have : (0 : ℝ) ≤ 1 - pr := sub_nonneg.mpr hp1
        linarith [mul_nonneg hp0 (Real.exp_nonneg lam)]
      have hpow :
          (1 - pr + pr * Real.exp lam) ^ S.card ≤
            (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card :=
        pow_le_pow_left₀ hbase hbern _
      have hexp_pow :
          (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card =
            Real.exp ((pr * lam + lam ^ 2 / 8) * S.card) := by
        rw [← Real.exp_nat_mul, mul_comm]
      calc ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
              Fintype.card (Equiv.Perm (Fin n)))
          ≤ (1 - pr + pr * Real.exp lam) ^ S.card := by
              convert hbin
        _ ≤ (Real.exp (pr * lam + lam ^ 2 / 8)) ^ S.card := hpow
        _ = Real.exp ((pr * lam + lam ^ 2 / 8) * S.card) := hexp_pow
    have hprod :
        ∏ r ∈ R,
            ((∑ π : Equiv.Perm (Fin n), Real.exp (lam * (rowHit c S r π : ℝ))) /
              Fintype.card (Equiv.Perm (Fin n))) ≤
          ∏ r ∈ R,
            Real.exp
              (((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) *
                (S.card : ℝ)) :=
      Finset.prod_le_prod (fun _ _ => by positivity) fun r hr => hrow r hr
    refine hprod.trans ?_
    rw [← Real.exp_sum]
    refine (Real.exp_le_exp).mpr (le_of_eq ?_)
    have hsum :
        ∑ r ∈ R,
            ((((monotoneRowOnes c r).card : ℝ) / n) * lam + lam ^ 2 / 8) * S.card =
          (totalOnes / n) * lam * S.card + (mF : ℝ) * S.card * lam ^ 2 / 8 := by
      have htot : totalOnes = ∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ) := rfl
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, hRcard,
        nsmul_eq_mul, ← Finset.sum_div (s := R) (f := fun r => ((monotoneRowOnes c r).card : ℝ)),
        htot]
      ring
    have hsum_p : totalOnes / n = p * mF := by
      have hm0 : (mF : ℝ) ≠ 0 := by exact_mod_cast hmF0
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hp_def]
      field_simp [hm0, hn0]
    rw [hsum, hsum_p]
    ring

/-! ## Fringe exp bound (clone of `lemma63ExpBound`) -/

/-- Paper fringe-row Chernoff: threshold `(p+t)·m_F·|S|` on `onesAboveHalfFringe`. -/
structure Lemma62FringeExpBound (m n f : Nat) (hf : Even f) : Prop where
  bound :
    ∀ (c : MonotoneColumnSums m n) (S : Finset (Fin n)) (t : ℝ),
      0 < t →
      ∀ (bad : Finset (Scramble m n)),
        (∀ σ ∈ bad,
          (fringeOnesDensity hf c + t) * (fringeRowCount m f hf : ℝ) * S.card ≤
            (onesAboveHalfFringe hf c σ S : ℝ)) →
          (bad.card : ℝ) ≤
            Real.exp (-(2 * t ^ 2 * (fringeRowCount m f hf : ℝ) * S.card)) *
              (Fintype.card (Scramble m n) : ℝ)

theorem lemma62FringeExpBound {m n f : Nat} (hf : Even f) (hn : 0 < n) :
    Lemma62FringeExpBound m n f hf where
  bound := by
    intro c S t ht bad hbad
    classical
    set mF : Nat := fringeRowCount m f hf
    set p : ℝ := fringeOnesDensity hf c
    set lam : ℝ := 4 * t
    have hlam : 0 ≤ lam := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht.le
    set thresh : ℝ := (p + t) * mF * S.card
    have hmarkov :
        (bad.card : ℝ) ≤
          Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) := by
      have hone (σ : Scramble m n) (hσ : σ ∈ bad) :
          (1 : ℝ) ≤
            Real.exp (lam * ((onesAboveHalfFringe hf c σ S : ℝ) - thresh)) := by
        have hX : thresh ≤ (onesAboveHalfFringe hf c σ S : ℝ) := by
          simpa [thresh, p, mF] using hbad σ hσ
        exact Real.one_le_exp (mul_nonneg hlam (sub_nonneg.mpr hX))
      have hsplit (σ : Scramble m n) :
          Real.exp (lam * ((onesAboveHalfFringe hf c σ S : ℝ) - thresh)) =
            Real.exp (-lam * thresh) *
              Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) := by
        have : lam * ((onesAboveHalfFringe hf c σ S : ℝ) - thresh) =
            lam * (onesAboveHalfFringe hf c σ S : ℝ) + (-lam * thresh) := by ring
        rw [this, Real.exp_add, mul_comm]
      calc (bad.card : ℝ)
          = ∑ σ ∈ bad, (1 : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ σ ∈ bad,
              Real.exp (lam * ((onesAboveHalfFringe hf c σ S : ℝ) - thresh)) :=
                Finset.sum_le_sum fun σ hσ => hone σ hσ
        _ ≤ ∑ σ : Scramble m n,
              Real.exp (lam * ((onesAboveHalfFringe hf c σ S : ℝ) - thresh)) :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                  fun _ _ _ => Real.exp_nonneg _
        _ = ∑ σ : Scramble m n,
              Real.exp (-lam * thresh) *
                Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) := by
                  simp_rw [hsplit]
        _ = Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) := by
                  rw [← Finset.mul_sum]
    have hmgf := avg_exp_onesAboveHalfFringe_le hf hn c S lam hlam
    have htotpos : (0 : ℝ) < Fintype.card (Scramble m n) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
    have hcombine :
        Real.exp (-lam * thresh) *
            ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) ≤
          Real.exp (-(2 * t ^ 2 * mF * S.card)) *
            (Fintype.card (Scramble m n) : ℝ) := by
      have havg :
          (∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ))) /
              Fintype.card (Scramble m n) ≤
            Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) := by
        simpa [p, mF] using hmgf
      have hsum_le :
          ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) ≤
            Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := by
        have := (div_le_iff₀ htotpos).mp havg
        linarith
      have hexp_nonneg : 0 ≤ Real.exp (-lam * thresh) := Real.exp_nonneg _
      have hstep1 :
          Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ)) ≤
            Real.exp (-lam * thresh) *
              (Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le hexp_nonneg
      have hstep2 :
          Real.exp (-lam * thresh) *
              (Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) =
            Real.exp (-lam * thresh + lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := by
        rw [← mul_assoc, ← Real.exp_add]
        ring_nf
      have hstep3 :
          Real.exp (-lam * thresh + lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) =
            Real.exp (-(2 * t ^ 2 * mF * S.card)) := by
        congr 1
        change -(4 * t) * ((p + t) * mF * S.card) + (4 * t) * p * mF * S.card +
            mF * S.card * (4 * t) ^ 2 / 8 =
          -(2 * t ^ 2 * mF * S.card)
        ring
      calc Real.exp (-lam * thresh) *
              ∑ σ : Scramble m n, Real.exp (lam * (onesAboveHalfFringe hf c σ S : ℝ))
          ≤ Real.exp (-lam * thresh) *
              (Real.exp (lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
                (Fintype.card (Scramble m n) : ℝ)) := hstep1
        _ = Real.exp (-lam * thresh + lam * p * mF * S.card + mF * S.card * lam ^ 2 / 8) *
              (Fintype.card (Scramble m n) : ℝ) := hstep2
        _ = Real.exp (-(2 * t ^ 2 * mF * S.card)) *
              (Fintype.card (Scramble m n) : ℝ) := by rw [hstep3]
    exact hmarkov.trans hcombine

/-! ## Paper bad event ⇒ fringe Chernoff threshold -/

/-- Upper cap `f/(2 m_F)` on fringe ones-density used in Lemma 6.2 (when `m_F > 0`). -/
noncomputable def fringeHalfWidthDensityCap (m f : Nat) (hf : Even f) : ℝ :=
  let mF := fringeRowCount m f hf
  if hmF : mF = 0 then (1 : ℝ) else (f / 2 : ℝ) / (mF : ℝ)

/-- Fringe average ones per column is at most half the fringe width (paper side condition). -/
def FringeOnesDensityLeHalfWidth (m n f : Nat) (hf : Even f) : Prop :=
  ∀ (c : MonotoneColumnSums m n), fringeOnesDensity hf c ≤ fringeHalfWidthDensityCap m f hf

theorem sum_fringeRowOnes_le_sum_all {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) :
    ∑ r ∈ aboveHalfFringeRows m f hf, (monotoneRowOnes c r).card ≤
      ∑ r : Fin m, (monotoneRowOnes c r).card := by
  simpa using
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (aboveHalfFringeRows m f hf))
      fun _ _ _ => Nat.zero_le _

/-- When average row ones is at most `1`, fringe ones-density is at most `f/(2 m_F)` (`f ≥ 2`). -/
theorem FringeOnesDensityLeHalfWidth_of_avgRowOnes_le_one {m n f : Nat} (hf : Even f)
    (hn : 0 < n) (hf2 : 2 ≤ f) (havg : AvgRowOnesLeOne m n) :
    FringeOnesDensityLeHalfWidth m n f hf := by
  intro c
  dsimp [FringeOnesDensityLeHalfWidth, fringeHalfWidthDensityCap, fringeOnesDensity]
  set R := aboveHalfFringeRows m f hf
  set mF := fringeRowCount m f hf
  by_cases hmF0 : mF = 0
  · simp [hmF0]
  · have hmFpos : 0 < mF := Nat.pos_of_ne_zero hmF0
    have hmF0R : (mF : ℝ) ≠ 0 := by exact_mod_cast hmF0
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hmFposR : (0 : ℝ) < mF := by exact_mod_cast hmFpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have htotal :
        (∑ r : Fin m, (monotoneRowOnes c r).card : ℝ) ≤ n := by
      have havg' := havg c
      rw [avgRowOnes_eq c, div_le_iff₀ hnR] at havg'
      linarith
    have hfringe :
        (∑ r ∈ R, (monotoneRowOnes c r).card : ℝ) ≤
          (∑ r : Fin m, (monotoneRowOnes c r).card : ℝ) := by
      exact_mod_cast sum_fringeRowOnes_le_sum_all hf c
    have hfringe_n : (∑ r ∈ R, (monotoneRowOnes c r).card : ℝ) ≤ n :=
      hfringe.trans htotal
    have hf2R : (2 : ℝ) ≤ f := by exact_mod_cast hf2
    have hfhalf : (1 : ℝ) ≤ f / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hfhalf' : (n : ℝ) ≤ (f / 2 : ℝ) * n := by nlinarith [hfhalf]
    have hle : (∑ r ∈ R, (monotoneRowOnes c r).card : ℝ) ≤ (f / 2 : ℝ) * n :=
      hfringe_n.trans hfhalf'
    have hcap :
        (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ)) / (mF * n) ≤ (f / 2 : ℝ) / mF := by
      rw [div_le_iff₀ (mul_pos hmFposR hnR)]
      calc (∑ r ∈ R, ((monotoneRowOnes c r).card : ℝ))
          ≤ (f / 2 : ℝ) * n := hle
        _ = (f / 2 : ℝ) / (mF : ℝ) * ((mF : ℝ) * n) := by
            field_simp [hmF0R, hn0]
    simpa [hmF0, R, mF] using hcap

theorem FringeOnesDensityLeHalfWidth_of_totalColumnOnesLeN {m n f : Nat} (hf : Even f)
    (hn : 0 < n) (hf2 : 2 ≤ f) (h : TotalColumnOnesLeN m n) :
    FringeOnesDensityLeHalfWidth m n f hf :=
  FringeOnesDensityLeHalfWidth_of_avgRowOnes_le_one hf hn hf2
    (AvgRowOnesLeOne.of_totalColumnOnesLeN hn h)

theorem lemma62_hepsCell_of_worst {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (hm : 1 ≤ m)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log m) * n * fringeRowCount m f hf * n / 2) ≤
        epsF) :
    ∀ (j s : Nat),
      0 < j → (j : ℝ) ≤ deltaF * (f * n) → 1 ≤ s → s ≤ n →
        Real.sqrt
            ((1 + Real.log m) * n * fringeRowCount m f hf * s / (2 * (j : ℝ) ^ 2)) ≤
          epsF := by
  intro j s hj _ hs1 hsn
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast show 0 < m from lt_of_lt_of_le (by decide : 0 < 1) hm
  have hlog : (0 : ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hmF : (0 : ℝ) ≤ fringeRowCount m f hf := by exact_mod_cast (Nat.zero_le _)
  have hn : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℕ) ≤ j := Nat.one_le_iff_ne_zero.mpr hj.ne'
  have hj2 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by
    rw [← one_pow 2]
    exact pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hj1) 2
  have hsle : (s : ℝ) ≤ n := by exact_mod_cast hsn
  have hinside :
      (1 + Real.log m) * n * fringeRowCount m f hf * s / (2 * (j : ℝ) ^ 2) ≤
        (1 + Real.log m) * n * fringeRowCount m f hf * n / 2 := by
    have hnum : (0 : ℝ) ≤ (1 + Real.log m) * n * fringeRowCount m f hf := by positivity
    have hden : (2 : ℝ) ≤ 2 * (j : ℝ) ^ 2 := by nlinarith
    have hsj : (s : ℝ) ≤ n * (j : ℝ) ^ 2 := by nlinarith [hsle, hj2]
    refine (div_le_div_iff₀ (by positivity) (by positivity)).2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hsj hnum]
  exact (Real.sqrt_le_sqrt hinside).trans hepsWorst

/-- Conservative Chernoff shift `t = ε_F · j / (m_F · |S|)` (valid when `p ≤ f/(2 m_F)`). -/
noncomputable def lemma62_fringe_t (epsF : ℝ) (mF s j : Nat) : ℝ :=
  epsF * j / ((mF : ℝ) * s)

theorem onesAboveHalfFringe_le_mF_mul_S {m n f : Nat} (hf : Even f)
    (c : MonotoneColumnSums m n) (σ : Scramble m n) (S : Finset (Fin n)) :
    (onesAboveHalfFringe hf c σ S : ℝ) ≤
      (fringeRowCount m f hf : ℝ) * S.card := by
  classical
  rw [onesAboveHalfFringe_eq_sum_rowHit, Nat.cast_sum]
  calc (∑ r ∈ aboveHalfFringeRows m f hf, (rowHit c S r (σ r) : ℝ))
      ≤ ∑ _r ∈ aboveHalfFringeRows m f hf, (S.card : ℝ) :=
        Finset.sum_le_sum fun r _ => by exact_mod_cast rowHit_le c S r (σ r)
    _ = (fringeRowCount m f hf : ℝ) * S.card := by
        simp [Finset.sum_const, fringeRowCount, nsmul_eq_mul, mul_comm]

theorem not_fringeColumnEventBad_of_thresh_gt_mF_s {m n f : Nat} (hf : Even f)
    (deltaF epsF : ℝ) (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat)
    (S : Finset (Fin n))
    (hgt :
      (f / 2 : ℝ) * S.card + epsF * j >
        (fringeRowCount m f hf : ℝ) * S.card) :
    ¬ fringeColumnEventBad hf deltaF epsF c σ j S := by
  intro hbad
  have hle := onesAboveHalfFringe_le_mF_mul_S hf c σ S
  have hle' : (f / 2 : ℝ) * S.card + epsF * j ≤ (fringeRowCount m f hf : ℝ) * S.card := by
    exact le_trans (by simpa [fringeColumnEventBad] using hbad) hle
  linarith [hgt, hle']

theorem fringeColumnEventBad_implies_chernoffBound {m n f : Nat} (hf : Even f)
    (deltaF epsF : ℝ) (c : MonotoneColumnSums m n) (σ : Scramble m n) (j : Nat)
    (S : Finset (Fin n)) (hmF : 0 < fringeRowCount m f hf) (hs : 0 < S.card) (hj : 0 < j)
    (hepsF : 0 < epsF)
    (hdensity : fringeOnesDensity hf c ≤ fringeHalfWidthDensityCap m f hf)
    (hbad : fringeColumnEventBad hf deltaF epsF c σ j S) :
    0 < lemma62_fringe_t epsF (fringeRowCount m f hf) S.card j ∧
      (fringeOnesDensity hf c + lemma62_fringe_t epsF (fringeRowCount m f hf) S.card j) *
          (fringeRowCount m f hf : ℝ) * S.card ≤
        (onesAboveHalfFringe hf c σ S : ℝ) := by
  classical
  set mF := fringeRowCount m f hf
  set p := fringeOnesDensity hf c
  set t := lemma62_fringe_t epsF mF S.card j
  have hmF0 : (mF : ℝ) ≠ 0 := by exact_mod_cast hmF.ne'
  have hs0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hmFpos : (0 : ℝ) < mF := by exact_mod_cast hmF
  have hsRpos : (0 : ℝ) < S.card := by exact_mod_cast hs
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have htpos : 0 < t := by
    dsimp [lemma62_fringe_t, t]
    exact div_pos (mul_pos hepsF hjR) (mul_pos hmFpos hsRpos)
  have hcap : p ≤ (f / 2 : ℝ) / (mF : ℝ) := by
    have := hdensity
    simp only [fringeHalfWidthDensityCap, hmF.ne', mF] at this
    exact this
  have hp_mul : p * (mF : ℝ) * S.card ≤ (f / 2 : ℝ) * S.card := by
    calc p * (mF : ℝ) * S.card = p * ((mF : ℝ) * S.card) := by ring
      _ ≤ ((f / 2 : ℝ) / (mF : ℝ)) * ((mF : ℝ) * S.card) := mul_le_mul_of_nonneg_right hcap (by positivity)
      _ = (f / 2 : ℝ) * S.card := by field_simp [hmF0]
  have hpaper :
      (p + t) * (mF : ℝ) * S.card ≤ (f / 2 : ℝ) * S.card + epsF * j := by
    dsimp [lemma62_fringe_t, t]
    have hsplit :
        (p + epsF * j / ((mF : ℝ) * S.card)) * (mF : ℝ) * S.card =
          p * (mF : ℝ) * S.card + epsF * j := by
      field_simp [hmF0, hs0]
    calc (p + epsF * j / ((mF : ℝ) * S.card)) * (mF : ℝ) * S.card
        = p * (mF : ℝ) * S.card + epsF * j := hsplit
      _ ≤ (f / 2 : ℝ) * S.card + epsF * j := by linarith
  refine ⟨htpos, ?_⟩
  exact le_trans hpaper (by simpa [fringeColumnEventBad] using hbad)

/-! ## `(e m)^{-n}` algebraic bound (clone of `lemma61_exp_bound`) -/

theorem lemma62_t_sq_identity (epsF : ℝ) (j mF s : Nat) (hs : 0 < s) (hmF : 0 < mF) :
    2 * (epsF * j / ((mF : ℝ) * s)) ^ 2 * mF * s =
      2 * epsF ^ 2 * j ^ 2 / ((mF : ℝ) * s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hm0 : (mF : ℝ) ≠ 0 := by exact_mod_cast hmF.ne'
  field_simp [hs0, hm0]

theorem lemma62_exp_bound (m n mF s j : Nat) (epsF : ℝ)
    (hm : 1 ≤ m) (hmF : 1 ≤ mF) (hs1 : 1 ≤ s) (hj1 : 1 ≤ j) (hsn : s ≤ n) (hn : 1 ≤ n)
    (heps :
      Real.sqrt ((1 + Real.log m) * n * mF * s / (2 * (j : ℝ) ^ 2)) ≤ epsF) :
    Real.exp (-(2 * (epsF * j / ((mF : ℝ) * s)) ^ 2 * mF * s)) ≤
      (Real.exp 1 * m) ^ (-(n : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hm)
  have hmFpos : (0 : ℝ) < mF := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hmF)
  have hspos : (0 : ℝ) < s := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hs1)
  have hjpos : (0 : ℝ) < j := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hj1)
  have hlog0 : (0 : ℝ) ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hinside_nn : (0 : ℝ) ≤ (1 + Real.log m) * n * mF * s / (2 * (j : ℝ) ^ 2) := by positivity
  have heps2 :
      (1 + Real.log m) * n * mF * s / (2 * (j : ℝ) ^ 2) ≤ epsF ^ 2 := by
    set harg := (1 + Real.log m) * n * mF * s / (2 * (j : ℝ) ^ 2)
    have hx' := Real.sqrt_nonneg harg
    have := mul_self_le_mul_self hx' heps
    rwa [Real.mul_self_sqrt hinside_nn, ← pow_two] at this
  have hs0nat : 0 < s := lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hs1
  have hmF0nat : 0 < mF := lt_of_lt_of_le (by norm_num : (0 : Nat) < 1) hmF
  have hid := lemma62_t_sq_identity epsF j mF s hs0nat hmF0nat
  have hj2pos : (0 : ℝ) < (j : ℝ) ^ 2 := by nlinarith
  have hmFspos : (0 : ℝ) < (mF : ℝ) * s := mul_pos hmFpos hspos
  have hcoeff :
      (1 + Real.log m) * n ≤ 2 * epsF ^ 2 * j ^ 2 / ((mF : ℝ) * s) := by
    have h1 :
        (1 + Real.log m) * n * ((mF : ℝ) * s) ≤ 2 * epsF ^ 2 * j ^ 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_right heps2 (show 0 ≤ 2 * (j : ℝ) ^ 2 from by positivity)
      field_simp at hmul ⊢
      linarith
    exact (le_div_iff₀ hmFspos).mpr h1
  have hexp_le :
      Real.exp (-(2 * (epsF * j / ((mF : ℝ) * s)) ^ 2 * mF * s)) ≤
        Real.exp (-((1 + Real.log m) * n)) := by
    rw [hid]
    exact Real.exp_le_exp.mpr (neg_le_neg hcoeff)
  have hrewrite :
      Real.exp (-((1 + Real.log m) * n)) = (Real.exp 1 * m) ^ (-(n : ℝ)) := by
    have hlogem : Real.log (Real.exp 1 * m) = 1 + Real.log m := by
      rw [Real.log_mul (Real.exp_pos _).ne' hmpos.ne', Real.log_exp]
    calc Real.exp (-((1 + Real.log m) * n))
        = Real.exp (-(n : ℝ) * Real.log (Real.exp 1 * m)) := by rw [← hlogem]; ring_nf
      _ = (Real.exp 1 * m) ^ (-(n : ℝ)) := by
            rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  exact hexp_le.trans_eq hrewrite

theorem lemma62_exp_bound_fringeRows (m n f : Nat) (hf : Even f) (s j : Nat) (epsF : ℝ)
    (hm : 1 ≤ m) (hmF : 1 ≤ fringeRowCount m f hf) (hs1 : 1 ≤ s) (hj1 : 1 ≤ j)
    (hsn : s ≤ n) (hn : 1 ≤ n)
    (heps :
      Real.sqrt
          ((1 + Real.log m) * n * fringeRowCount m f hf * s / (2 * (j : ℝ) ^ 2)) ≤
        epsF) :
    Real.exp
        (-(2 *
            (epsF * j /
                ((fringeRowCount m f hf : ℝ) * s)) ^ 2 *
              fringeRowCount m f hf * s)) ≤
      (Real.exp 1 * m) ^ (-(n : ℝ)) :=
  lemma62_exp_bound m n (fringeRowCount m f hf) s j epsF hm hmF hs1 hj1 hsn hn heps

theorem lemma62_exp_bound_of_params (g : ScrambleGeometry) (hf : Even g.f)
    (P : Theorem51Params g) {s j : Nat}
    (hmF : 1 ≤ fringeRowCount g.m g.f hf) (hs1 : 1 ≤ s) (hj1 : 1 ≤ j) (hsn : s ≤ g.n)
    (hepsCell :
      Real.sqrt
          ((1 + Real.log g.m) * g.n * fringeRowCount g.m g.f hf * s / (2 * (j : ℝ) ^ 2)) ≤
        P.epsF) :
    Real.exp
        (-(2 *
            (P.epsF * j /
                ((fringeRowCount g.m g.f hf : ℝ) * s)) ^ 2 *
              fringeRowCount g.m g.f hf * s)) ≤
      (Real.exp 1 * g.m) ^ (-(g.n : ℝ)) :=
  lemma62_exp_bound_fringeRows g.m g.n g.f hf s j P.epsF
    (le_trans (by norm_num : (1 : Nat) ≤ 100) g.hm) hmF hs1 hj1 hsn
    (le_trans (by norm_num : (1 : Nat) ≤ 16) g.hn) hepsCell

/-! ## Per-cell bound `Lemma62FringeCellBound` -/

/-- Hypotheses discharging `Lemma62FringeCellBound` from fringe Chernoff + `(e m)^{-n}`. -/
structure Lemma62FringeCellBoundHyp (m n f : Nat) (hf : Even f) (deltaF epsF : ℝ) where
  hn : 0 < n
  hepsF : 0 < epsF
  hdensity : FringeOnesDensityLeHalfWidth m n f hf
  hExp :
    ∀ (j s : Nat),
      0 < j → (j : ℝ) ≤ deltaF * (f * n) → 1 ≤ s → s ≤ n →
        Real.exp
            (-(2 *
                (epsF * j / ((fringeRowCount m f hf : ℝ) * s)) ^ 2 *
                  fringeRowCount m f hf * s)) ≤
          (Real.exp 1 * m) ^ (-(n : ℝ))

theorem Lemma62FringeCellBoundHyp.of_expSqrt {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (hn : 0 < n) (hepsF : 0 < epsF) (hdensity : FringeOnesDensityLeHalfWidth m n f hf)
    (hm : 1 ≤ m) (hn1 : 1 ≤ n)
    (hmF : 1 ≤ fringeRowCount m f hf)
    (hepsCell :
      ∀ (j s : Nat),
        0 < j → (j : ℝ) ≤ deltaF * (f * n) → 1 ≤ s → s ≤ n →
          Real.sqrt
              ((1 + Real.log m) * n * fringeRowCount m f hf * s / (2 * (j : ℝ) ^ 2)) ≤
            epsF) :
    Lemma62FringeCellBoundHyp m n f hf deltaF epsF where
  hn := hn
  hepsF := hepsF
  hdensity := hdensity
  hExp := fun j s hj hjδ hs1 hsn =>
    lemma62_exp_bound_fringeRows m n f hf s j epsF hm hmF hs1 (Nat.succ_le_iff.mp hj) hsn hn1
      (hepsCell j s hj hjδ hs1 hsn)

theorem Lemma62FringeCellBoundHyp.of_avgRowOnes {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (hn : 0 < n) (hepsF : 0 < epsF) (hf2 : 2 ≤ f) (havg : AvgRowOnesLeOne m n)
    (hm : 1 ≤ m) (hn1 : 1 ≤ n) (hmF : 1 ≤ fringeRowCount m f hf)
    (hepsCell :
      ∀ (j s : Nat),
        0 < j → (j : ℝ) ≤ deltaF * (f * n) → 1 ≤ s → s ≤ n →
          Real.sqrt
              ((1 + Real.log m) * n * fringeRowCount m f hf * s / (2 * (j : ℝ) ^ 2)) ≤
            epsF) :
    Lemma62FringeCellBoundHyp m n f hf deltaF epsF where
  hn := hn
  hepsF := hepsF
  hdensity := FringeOnesDensityLeHalfWidth_of_avgRowOnes_le_one hf hn hf2 havg
  hExp := fun j s hj hjδ hs1 hsn =>
    lemma62_exp_bound_fringeRows m n f hf s j epsF hm hmF hs1 (Nat.succ_le_iff.mp hj) hsn hn1
      (hepsCell j s hj hjδ hs1 hsn)

theorem Lemma62FringeCellBoundHyp.of_avgRowOnes_worstEps {m n f : Nat} {hf : Even f}
    {deltaF epsF : ℝ} (hn : 0 < n) (hepsF : 0 < epsF) (hf2 : 2 ≤ f)
    (havg : AvgRowOnesLeOne m n) (hm : 1 ≤ m) (hn1 : 1 ≤ n)
    (hmF : 1 ≤ fringeRowCount m f hf)
    (hepsWorst :
      Real.sqrt
          ((1 + Real.log m) * n * fringeRowCount m f hf * n / 2) ≤
        epsF) :
    Lemma62FringeCellBoundHyp m n f hf deltaF epsF :=
  of_avgRowOnes hn hepsF hf2 havg hm hn1 hmF
    (lemma62_hepsCell_of_worst hm hepsWorst)

theorem Lemma62FringeCellBound.of_hyp {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (H : Lemma62FringeCellBoundHyp m n f hf deltaF epsF) :
    Lemma62FringeCellBound m n f hf deltaF epsF where
  bound := by
    intro c j S hj hjδ bad hbad
    classical
    set mF := fringeRowCount m f hf
    set s := S.card
    set N : ℝ := (Fintype.card (Scramble m n) : ℝ)
    have hNpos : 0 < N := by
      dsimp [N]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Scramble m n))
    by_cases hmF0 : mF = 0
    · have hempty : bad = ∅ := by
        ext σ
        simp only [Finset.notMem_empty, iff_false]
        intro hσ
        have hbadσ := hbad σ hσ
        have hzero : onesAboveHalfFringe hf c σ S = 0 := by
          have hR : aboveHalfFringeRows m f hf = ∅ := Finset.card_eq_zero.mp hmF0
          rw [onesAboveHalfFringe_eq_sum_rowHit, hR, Finset.sum_empty]
        have hbadσ' := by simpa [fringeColumnEventBad, hzero] using hbadσ
        have hpos : 0 < epsF * j := mul_pos H.hepsF (by exact_mod_cast hj)
        have hfS_nn : 0 ≤ (f / 2 : ℝ) * S.card := by positivity
        linarith [hbadσ', hpos, hfS_nn]
      rw [show (bad.card : ℝ) = 0 from by simp [hempty]]
      positivity
    · by_cases hs0 : s = 0
      · have hempty : bad = ∅ := by
          ext σ
          simp only [Finset.notMem_empty, iff_false]
          intro hσ
          have hbadσ := hbad σ hσ
          have hS : S = ∅ := Finset.card_eq_zero.mp hs0
          have hzero : onesAboveHalfFringe hf c σ S = 0 := by
            rw [hS, onesAboveHalfFringe_eq_sum_rowHit]
            refine Finset.sum_eq_zero fun r _ => ?_
            simp [rowHit, Finset.inter_empty]
          have hScard : (S.card : ℝ) = 0 := by exact_mod_cast hs0
          have hbadσ' := by simpa [fringeColumnEventBad, hzero, hScard, mul_zero, add_zero] using hbadσ
          have hpos : 0 < epsF * (j : ℝ) := mul_pos H.hepsF (by exact_mod_cast hj)
          linarith [hbadσ', hpos]
        rw [show (bad.card : ℝ) = 0 from by simp [hempty]]
        positivity
      · have hmFpos : 0 < mF := Nat.pos_of_ne_zero hmF0
        have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
        have hsn : s ≤ n := by
          simpa [Fintype.card_fin] using (S.card_le_univ : s ≤ Finset.univ.card)
        set t := lemma62_fringe_t epsF mF s j
        have ht : 0 < t := by
          dsimp [lemma62_fringe_t, t]
          exact div_pos (mul_pos H.hepsF (by exact_mod_cast hj))
            (mul_pos (by exact_mod_cast hmFpos) (by exact_mod_cast (Nat.pos_of_ne_zero hs0)))
        have ht_eq : t = epsF * j / ((fringeRowCount m f hf : ℝ) * s) := by
          rfl
        have hcher (σ : Scramble m n) (hσ : σ ∈ bad) :
            (fringeOnesDensity hf c + t) * (mF : ℝ) * s ≤
              (onesAboveHalfFringe hf c σ S : ℝ) := by
          have ⟨_, hbound⟩ :=
            fringeColumnEventBad_implies_chernoffBound hf deltaF epsF c σ j S hmFpos
              (Nat.pos_of_ne_zero hs0) hj H.hepsF (H.hdensity c) (hbad σ hσ)
          simpa [lemma62_fringe_t, mF] using hbound
        have hF := (lemma62FringeExpBound hf H.hn).bound c S t ht bad hcher
        have hexp := H.hExp j s hj hjδ hs1 hsn
        have hexp' :=
          show Real.exp (-(2 * t ^ 2 * mF * s)) ≤ (Real.exp 1 * m) ^ (-(n : ℝ)) from by
            rw [show t = epsF * j / ((fringeRowCount m f hf : ℝ) * s) from ht_eq,
              show mF = fringeRowCount m f hf from rfl]
            exact H.hExp j s hj hjδ hs1 hsn
        calc (bad.card : ℝ)
            ≤ Real.exp (-(2 * t ^ 2 * mF * s)) * N := hF
          _ ≤ (Real.exp 1 * m) ^ (-(n : ℝ)) * N :=
              mul_le_mul_of_nonneg_right hexp' (le_of_lt hNpos)

theorem Lemma62FringeCellBound.of_fringeExpBound {m n f : Nat} {hf : Even f} {deltaF epsF : ℝ}
    (H : Lemma62FringeCellBoundHyp m n f hf deltaF epsF) :
    Lemma62FringeCellBound m n f hf deltaF epsF :=
  Lemma62FringeCellBound.of_hyp H

end Chvatal
