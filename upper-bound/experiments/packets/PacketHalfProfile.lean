import PacketProfile
import AKS.Chvatal.ExecPlacement

/-! The actual repair atoms are 32-wire rank intervals. This file carries the
sorted-profile scale transfer down to that fragment size. -/

namespace Chvatal.PacketAlignment

open Finset BigOperators

def profileHalf (K X i : Nat) : Nat :=
  profileTail (32 * K) X (32 * (i + 1)) - profileTail (32 * K) X (32 * i)

private theorem profileTail_interval_count32 (m X a b : Nat)
    (hab : a ≤ b) (hb : b ≤ m) :
    profileTail m X b - profileTail m X a = min (b - a) (X - (m - b)) := by
  by_cases h0 : X ≤ m - b
  · simp [profileTail, h0]
  · by_cases h1 : X ≤ m - a
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega
    · simp only [profileTail, Nat.min_def]
      split_ifs <;> omega

/-- Ideal count in any fixed rank interval of a sorted packet. -/
def profileInterval (m X a b : Nat) : Nat :=
  profileTail m X b - profileTail m X a

theorem profileInterval_formula (m X a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    profileInterval m X a b = min (b - a) (X - (m - b)) := by
  unfold profileInterval
  exact profileTail_interval_count32 m X a b hab hb

/-- A fixed rank interval's ideal count changes by at most the change in
the packet's total count. This is the local estimate needed when ports select
different fixed rank intervals from a cohort. -/
theorem profileInterval_change_le (m X Y a b : Nat) (hab : a ≤ b) (hb : b ≤ m)
    (hYX : Y ≤ X) : profileInterval m X a b - profileInterval m Y a b ≤ X - Y := by
  rw [profileInterval_formula m X a b hab hb,
    profileInterval_formula m Y a b hab hb]
  by_cases hy : b - a ≤ Y - (m - b)
  · have hx : b - a ≤ X - (m - b) := by omega
    rw [Nat.min_eq_left hy, Nat.min_eq_left hx]
    omega
  · by_cases hx : b - a ≤ X - (m - b)
    · have hy' : Y - (m - b) < b - a := by omega
      rw [Nat.min_eq_left hx, Nat.min_eq_right (Nat.le_of_lt hy')]
      omega
    · have hx' : X - (m - b) < b - a := by omega
      have hy' : Y - (m - b) < b - a := by omega
      rw [Nat.min_eq_right (Nat.le_of_lt hx'), Nat.min_eq_right (Nat.le_of_lt hy')]
      omega

private def blockRankEmbedding {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ s.card) : Fin (hi - lo) ↪ Fin N where
  toFun j := s.orderEmbOfFin rfl ⟨lo + j.val, by
    have hsum := Nat.add_sub_of_le hlo
    have hlt : lo + j.val < hi := by
      calc
        lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
        _ = hi := hsum
    exact lt_of_lt_of_le hlt hhi⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := (s.orderEmbOfFin rfl).injective h
    have hv := congrArg Fin.val he
    simp only [Fin.val_mk] at hv
    omega

private theorem blockRankEmbedding_range {N : Nat} (s : Finset (Fin N))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ s.card) :
    Set.range (blockRankEmbedding s lo hi hlo hhi) = {w | w ∈ blockOf s lo hi} := by
  ext w
  constructor
  · rintro ⟨j, rfl⟩
    change blockRankEmbedding s lo hi hlo hhi j ∈ blockOf s lo hi
    rw [mem_blockOf_iff]
    refine ⟨⟨lo + j.val, by
      have hsum := Nat.add_sub_of_le hlo
      have hlt : lo + j.val < hi := by
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
      exact lt_of_lt_of_le hlt hhi⟩, ?_, ?_, rfl⟩
    · change lo ≤ lo + j.val
      exact Nat.le_add_right _ _
    · change lo + j.val < hi
      have hsum := Nat.add_sub_of_le hlo
      calc
        lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
        _ = hi := hsum
  · intro hw
    change w ∈ blockOf s lo hi at hw
    rw [mem_blockOf_iff] at hw
    rcases hw with ⟨r, hrlo, hrhi, rfl⟩
    let j : Fin (hi - lo) := ⟨r.val - lo, by omega⟩
    refine ⟨j, ?_⟩
    change s.orderEmbOfFin rfl ⟨lo + j.val, by
      have hsum := Nat.add_sub_of_le hlo
      have hlt : lo + j.val < hi := by
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
      exact lt_of_lt_of_le hlt hhi⟩ = s.orderEmbOfFin rfl r
    apply congrArg (s.orderEmbOfFin rfl)
    apply Fin.ext
    dsimp [j]
    omega

def profileIntervalMean (m q : Nat) (frac : Real) (a b : Nat) : Real :=
  (1 - frac) * profileInterval m q a b +
    frac * profileInterval m (q + 1) a b

/-- A fractional ideal profile assigns each rank interval a mean between zero
and that interval's capacity. This lets selected interval means define a
valid next receiver threshold target without a separate common-mean ansatz. -/
theorem profileIntervalMean_bounds (m q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    0 ≤ profileIntervalMean m q frac a b ∧
      profileIntervalMean m q frac a b ≤ (b - a : Nat) := by
  have hx0 : 0 ≤ (profileInterval m q a b : Real) := by
    rw [profileInterval_formula m q a b hab hb]
    exact_mod_cast Nat.zero_le (min (b - a) (q - (m - b)))
  have hy0 : 0 ≤ (profileInterval m (q + 1) a b : Real) := by
    rw [profileInterval_formula m (q + 1) a b hab hb]
    exact_mod_cast Nat.zero_le (min (b - a) (q + 1 - (m - b)))
  have hxle : (profileInterval m q a b : Real) ≤ (b - a : Nat) := by
    rw [profileInterval_formula m q a b hab hb]
    exact_mod_cast Nat.min_le_left _ _
  have hyle : (profileInterval m (q + 1) a b : Real) ≤ (b - a : Nat) := by
    rw [profileInterval_formula m (q + 1) a b hab hb]
    exact_mod_cast Nat.min_le_left _ _
  unfold profileIntervalMean
  constructor <;> nlinarith

private theorem profileTail_mono_r (m X : Nat) : Monotone (profileTail m X) := by
  intro a b hab
  simp only [profileTail]
  omega

private theorem sum_profileIntervals_partition (m p X : Nat) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hmono : Monotone cuts) (hend : cuts p = m) :
    (∑ i ∈ range p, profileInterval m X (cuts i) (cuts (i + 1))) =
      profileTail m X m - profileTail m X 0 := by
  unfold profileInterval
  have htail : Monotone (fun i => profileTail m X (cuts i)) :=
    (profileTail_mono_r m X).comp hmono
  rw [Finset.sum_range_tsub htail p]
  rw [hend, hstart]

private theorem profileInterval_mono_X (m X Y a b : Nat) (hab : a ≤ b) (hb : b ≤ m)
    (hXY : Y ≤ X) : profileInterval m Y a b ≤ profileInterval m X a b := by
  rw [profileInterval_formula m Y a b hab hb, profileInterval_formula m X a b hab hb]
  exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)

/-- Interpolation between adjacent integer profiles stays between those
profiles on every rank interval. -/
theorem profileIntervalMean_between (m q a b : Nat) (frac : Real)
    (hab : a ≤ b) (hb : b ≤ m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (profileInterval m q a b : Real) ≤ profileIntervalMean m q frac a b ∧
      profileIntervalMean m q frac a b ≤
        (profileInterval m (q + 1) a b : Real) := by
  have hmono := profileInterval_mono_X m (q + 1) q a b hab hb (by omega)
  have hdelta : 0 ≤ (profileInterval m (q + 1) a b : Real) -
      profileInterval m q a b := by exact_mod_cast Nat.zero_le (profileInterval m (q + 1) a b - profileInterval m q a b)
  have hdelta' : (profileInterval m q a b : Real) ≤
      profileInterval m (q + 1) a b := by exact_mod_cast hmono
  unfold profileIntervalMean
  constructor
  · have hprod := mul_nonneg hfrac0 hdelta
    nlinarith
  · have hprod := mul_nonneg (sub_nonneg.mpr hfrac1) hdelta
    nlinarith

/-- The interpolated interval target is monotone in its underlying real
threshold count `q + frac`. The integer boundary case is exact, so changing
the floor does not introduce a discontinuity. -/
theorem profileIntervalMean_mono_mean (m q₁ q₂ a b : Nat)
    (frac₁ frac₂ : Real) (hab : a ≤ b) (hb : b ≤ m)
    (hfrac₁0 : 0 ≤ frac₁) (hfrac₁1 : frac₁ ≤ 1)
    (hfrac₂0 : 0 ≤ frac₂) (hfrac₂1 : frac₂ ≤ 1)
    (hmean : (q₁ : Real) + frac₁ ≤ (q₂ : Real) + frac₂) :
    profileIntervalMean m q₁ frac₁ a b ≤ profileIntervalMean m q₂ frac₂ a b := by
  by_cases h₁₂ : q₁ ≤ q₂
  · by_cases heq : q₁ = q₂
    · subst q₂
      have hfrac : frac₁ ≤ frac₂ := by nlinarith
      have hmono := profileInterval_mono_X m (q₁ + 1) q₁ a b hab hb (by omega)
      have hdelta : 0 ≤ (profileInterval m (q₁ + 1) a b : Real) -
          profileInterval m q₁ a b := by exact_mod_cast Nat.zero_le _
      unfold profileIntervalMean
      have hprod := mul_nonneg (sub_nonneg.mpr hfrac) hdelta
      nlinarith [show (profileInterval m q₁ a b : Real) ≤
        profileInterval m (q₁ + 1) a b by exact_mod_cast hmono]
    · have hlt : q₁ < q₂ := by omega
      have hleft := (profileIntervalMean_between m q₁ a b frac₁ hab hb
        hfrac₁0 hfrac₁1).2
      have hright := (profileIntervalMean_between m q₂ a b frac₂ hab hb
        hfrac₂0 hfrac₂1).1
      have hmidNat := profileInterval_mono_X m q₂ (q₁ + 1) a b hab hb (by omega)
      have hmid : (profileInterval m (q₁ + 1) a b : Real) ≤
          (profileInterval m q₂ a b : Real) := by exact_mod_cast hmidNat
      exact le_trans hleft (le_trans hmid hright)
  · have hlt : q₂ < q₁ := by omega
    by_cases hsucc : q₂ + 1 = q₁
    · have hqreal : (q₁ : Real) = (q₂ : Real) + 1 := by exact_mod_cast hsucc.symm
      have hf₁ : frac₁ = 0 := by rw [hqreal] at hmean; nlinarith
      have hf₂ : frac₂ = 1 := by rw [hqreal] at hmean; nlinarith
      rw [← hsucc, hf₁, hf₂]
      simp [profileIntervalMean]
    · have hgap : q₂ + 1 < q₁ := by omega
      have hqle : q₁ ≤ q₂ + 1 := by
        have hqleReal : (q₁ : Real) ≤ (q₂ : Real) + 1 := by nlinarith
        exact_mod_cast hqleReal
      omega

/-- Any real threshold target in a positive-capacity register can be encoded
as `q + frac` with `q` strictly below capacity and `frac ∈ [0,1]`. The full
capacity endpoint uses the equivalent representation `(m-1)+1`. -/
theorem realTarget_has_integer_fraction (m : Nat) (μ : Real)
    (hm : 0 < m) (hμ0 : 0 ≤ μ) (hμm : μ ≤ (m : Real)) :
    ∃ q : Nat, q < m ∧ ∃ frac : Real,
      0 ≤ frac ∧ frac ≤ 1 ∧ (q : Real) + frac = μ := by
  by_cases htop : μ = (m : Real)
  · refine ⟨m - 1, by omega, 1, by norm_num, by norm_num, ?_⟩
    have hcast : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
      have hn : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      exact_mod_cast hn
    rw [htop]
    exact hcast
  · have hμlt : μ < (m : Real) := by
      by_contra h
      have hmμ : (m : Real) ≤ μ := le_of_not_gt h
      exact htop (le_antisymm hμm hmμ)
    have hfloorle : (Nat.floor μ : Real) ≤ μ := Nat.floor_le hμ0
    have hfloorlt : μ < (Nat.floor μ : Real) + 1 := Nat.lt_floor_add_one μ
    have hq_lt_real : (Nat.floor μ : Real) < (m : Real) := lt_of_le_of_lt hfloorle hμlt
    have hq_lt : Nat.floor μ < m := by exact_mod_cast hq_lt_real
    refine ⟨Nat.floor μ, hq_lt, μ - (Nat.floor μ : Real), ?_, ?_, ?_⟩
    · dsimp
      linarith
    · dsimp
      linarith
    · dsimp
      ring

private theorem cuts_le_end (p : Nat) (cuts : Nat → Nat) (hcuts : Monotone cuts)
    (i : Nat) (hi : i ≤ p) : cuts i ≤ cuts p := hcuts hi

private theorem profileInterval_partition_total (m p X : Nat) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hcuts : Monotone cuts) (hend : cuts p = m)
    (hX : X ≤ m) : (∑ i ∈ range p, profileInterval m X (cuts i) (cuts (i + 1))) = X := by
  rw [sum_profileIntervals_partition m p X cuts hstart hcuts hend]
  simp only [profileTail]
  omega

/-- The interpolated ideal means of a partition sum to the chosen fractional
target, including both the full-capacity and zero-capacity endpoint cases. -/
theorem profileIntervalMean_partition_sum (m p q : Nat) (frac : Real)
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hend : cuts p = m) (hq : q ≤ m) (hfrac0 : 0 ≤ frac)
    (hfrac1 : frac ≤ 1) (hendpoint : q = m → frac = 0) :
    (∑ i ∈ range p,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) = q + frac := by
  by_cases hq' : q < m
  · have hqsum : (∑ i ∈ range p,
        (profileInterval m q (cuts i) (cuts (i + 1)) : Real)) = q := by
      exact_mod_cast profileInterval_partition_total m p q cuts hstart hcuts hend (by omega)
    have hq1sum : (∑ i ∈ range p,
        (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real)) = q + 1 := by
      exact_mod_cast profileInterval_partition_total m p (q + 1) cuts hstart hcuts hend (by omega)
    unfold profileIntervalMean
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hqsum, hq1sum]
    ring
  · have hqeq : q = m := by omega
    have hf : frac = 0 := hendpoint hqeq
    subst q
    rw [hf]
    unfold profileIntervalMean
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    exact_mod_cast profileInterval_partition_total m p m cuts hstart hcuts hend (by omega)

theorem profileInterval_partition_L1_exact (m p X q : Nat) (frac : Real)
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hend : cuts p = m) (hX : X ≤ m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range p,
      |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      |(X : Real) - (q + frac)| := by
  have hmean : (∑ i ∈ range p,
      profileIntervalMean m q frac (cuts i) (cuts (i + 1))) = q + frac := by
    have hqsum : (∑ i ∈ range p,
        (profileInterval m q (cuts i) (cuts (i + 1)) : Real)) = q := by
      exact_mod_cast profileInterval_partition_total m p q cuts hstart hcuts hend (by omega)
    have hq1sum : (∑ i ∈ range p,
        (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real)) = q + 1 := by
      exact_mod_cast profileInterval_partition_total m p (q + 1) cuts hstart hcuts hend (by omega)
    unfold profileIntervalMean
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hqsum, hq1sum]
    ring
  have hxsum := profileInterval_partition_total m p X cuts hstart hcuts hend hX
  have hxsumR : (∑ i ∈ range p,
      (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) = X := by exact_mod_cast hxsum
  by_cases hXq : X ≤ q
  · have hpoint : ∀ i ∈ range p,
        (profileInterval m X (cuts i) (cuts (i + 1)) : Real) ≤
          profileIntervalMean m q frac (cuts i) (cuts (i + 1)) := by
      intro i hi
      have hi' : i < p := mem_range.mp hi
      have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
      have hb : cuts (i + 1) ≤ m := by
        rw [← hend]
        exact hcuts (by omega)
      have hbase := profileInterval_mono_X m q X (cuts i) (cuts (i + 1)) hab hb (by omega)
      have hnext := profileInterval_mono_X m (q + 1) q (cuts i) (cuts (i + 1)) hab hb (by omega)
      unfold profileIntervalMean
      have hn : (profileInterval m q (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m (q + 1) (cuts i) (cuts (i + 1)) := by exact_mod_cast hnext
      have hb' : (profileInterval m X (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m q (cuts i) (cuts (i + 1)) := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range p,
          |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
          ∑ i ∈ range p,
            (profileIntervalMean m q frac (cuts i) (cuts (i + 1)) -
              (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range p,
          profileIntervalMean m q frac (cuts i) (cuts (i + 1))) -
          (∑ i ∈ range p,
            (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        calc
          _ = (q + frac) - X := by rw [hmean, hxsumR]
          _ = |(X : Real) - (q + frac)| := by
            have hXR : (X : Real) ≤ q := by exact_mod_cast hXq
            rw [abs_of_nonpos (by linarith [hXR, hfrac0])]
            ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range p,
        profileIntervalMean m q frac (cuts i) (cuts (i + 1)) ≤
          (profileInterval m X (cuts i) (cuts (i + 1)) : Real) := by
      intro i hi
      have hi' : i < p := mem_range.mp hi
      have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
      have hb : cuts (i + 1) ≤ m := by
        rw [← hend]
        exact hcuts (by omega)
      have hbase := profileInterval_mono_X m X (q + 1) (cuts i) (cuts (i + 1)) hab hb (by omega)
      have hnext := profileInterval_mono_X m (q + 1) q (cuts i) (cuts (i + 1)) hab hb (by omega)
      unfold profileIntervalMean
      have hn : (profileInterval m q (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m (q + 1) (cuts i) (cuts (i + 1)) := by exact_mod_cast hnext
      have hb' : (profileInterval m (q + 1) (cuts i) (cuts (i + 1)) : Real) ≤
          profileInterval m X (cuts i) (cuts (i + 1)) := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range p,
          |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
          ∑ i ∈ range p,
            ((profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
              profileIntervalMean m q frac (cuts i) (cuts (i + 1))) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range p,
          (profileInterval m X (cuts i) (cuts (i + 1)) : Real)) -
          (∑ i ∈ range p,
            profileIntervalMean m q frac (cuts i) (cuts (i + 1))) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        calc
          _ = X - (q + frac) := by rw [hxsumR, hmean]
          _ = |(X : Real) - (q + frac)| := by
            have hXR : (q : Real) + 1 ≤ X := by exact_mod_cast hX'
            rw [abs_of_nonneg (by linarith [hXR, hfrac1])]

/-- The exact interval-partition error identity also covers the full and empty
profile endpoints. At positive capacity, `q=m` is represented by the equivalent
strict form `(m-1)+1`; at zero capacity all terms vanish. -/
theorem profileInterval_partition_L1_exact_allow_endpoint
    (m p X q : Nat) (frac : Real) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hcuts : Monotone cuts) (hend : cuts p = m)
    (hX : X ≤ m) (hq : q ≤ m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (hendpoint : q = m → frac = 0) :
    (∑ i ∈ range p,
      |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      |(X : Real) - (q + frac)| := by
  by_cases hm : 0 < m
  · by_cases hq' : q < m
    · exact profileInterval_partition_L1_exact m p X q frac cuts
        hstart hcuts hend hX hq' hfrac0 hfrac1
    · have hqeq : q = m := by omega
      have hf : frac = 0 := hendpoint hqeq
      have hcast : ((m - 1 : Nat) : Real) + 1 = (m : Real) := by
        have hn : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        exact_mod_cast hn
      have hmeanEq (a b : Nat) :
          profileIntervalMean m q frac a b =
            profileIntervalMean m (m - 1) 1 a b := by
        rw [hqeq, hf]
        simp only [profileIntervalMean]
        rw [show m - 1 + 1 = m by omega]
        ring
      calc
        _ = ∑ i ∈ range p,
            |(profileInterval m X (cuts i) (cuts (i + 1)) : Real) -
              profileIntervalMean m (m - 1) 1 (cuts i) (cuts (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hmeanEq]
        _ = |(X : Real) - ((m - 1 : Nat) + 1)| :=
          profileInterval_partition_L1_exact m p X (m - 1) 1 cuts
            hstart hcuts hend hX (by omega) (by norm_num) (by norm_num)
        _ = |(X : Real) - (q + frac)| := by
          rw [hqeq, hf, hcast]
          simp
  · have hm0 : m = 0 := by omega
    have hq0 : q = 0 := by omega
    have hX0 : X = 0 := by omega
    have hqeq : q = m := by omega
    have hf : frac = 0 := hendpoint hqeq
    have hcut0 (i : Nat) (hi : i ≤ p) : cuts i = 0 := by
      have hle := hcuts hi
      rw [hend, hm0] at hle
      omega
    calc
      _ = ∑ i ∈ range p, (0 : Real) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < p := Finset.mem_range.mp hi
        simp [profileInterval, profileTail, profileIntervalMean, hm0, hX0, hq0, hf,
          hcut0 i (by omega), hcut0 (i + 1) (by omega)]
      _ = |(X : Real) - (q + frac)| := by simp [hX0, hq0, hf]

/-- The actual count in a half-open rank interval of an increasing Boolean
packet is its ideal profile count. -/
theorem sortedBool_rankInterval_trueCount {m : Nat} (v : Fin m → Bool)
    (hv : Monotone v) (a b : Nat) (hab : a ≤ b) (hb : b ≤ m) :
    boolTrueCount (fun j : Fin (b - a) => v ⟨a + j.val, by have hj := j.isLt; omega⟩) =
      profileInterval m (boolTrueCount v) a b := by
  let hsumB : b + (m - b) = m := Nat.add_sub_of_le hb
  let hsumA : a + (m - a) = m := Nat.add_sub_of_le (le_trans hab hb)
  let hsum : a + (b - a) = b := Nat.add_sub_of_le hab
  let A : Fin a → Bool := fun i => v (Fin.cast hsumA (Fin.castAdd (m - a) i))
  let B : Fin b → Bool := fun i => v (Fin.cast hsumB (Fin.castAdd (m - b) i))
  let C : Fin (b - a) → Bool := fun j => v ⟨a + j.val, by have hj := j.isLt; omega⟩
  have he : Fin.append A C = B ∘ Fin.cast hsum := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [A, B, Fin.val_cast, Fin.val_castAdd, Fin.val_mk]
    · simp only [Fin.append_right, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [B, C, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_mk]
  have hcounts : boolTrueCount B = boolTrueCount A + boolTrueCount C := by
    calc
      boolTrueCount B = boolTrueCount (B ∘ Fin.cast hsum) := (boolTrueCount_finCast hsum B).symm
      _ = boolTrueCount (Fin.append A C) := congrArg boolTrueCount he.symm
      _ = boolTrueCount A + boolTrueCount C := boolTrueCount_append_general A C
  have hA := sortedBool_prefix_trueCount v hv (le_trans hab hb)
  have hB := sortedBool_prefix_trueCount v hv hb
  change boolTrueCount A = _ at hA
  change boolTrueCount B = _ at hB
  have hC : boolTrueCount C =
      (boolTrueCount v - (m - b)) - (boolTrueCount v - (m - a)) := by omega
  change boolTrueCount C = profileInterval m (boolTrueCount v) a b
  unfold profileInterval profileTail
  rw [hC]

/-- Actual values on a `WireFlow` rank block have exactly the ideal sorted
profile count. This connects the abstract profile lemma to concrete `blockOf`
ports without choosing or reordering their physical wire labels. -/
theorem trueCountOn_blockOf_profile {N : Nat} (s : Finset (Fin N))
    (v : Fin N → Bool) (hv : Monotone (v ∘ s.orderEmbOfFin rfl)) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ s.card) :
    trueCountOn (blockOf s lo hi) v = profileInterval s.card (trueCountOn s v) lo hi := by
  let e := blockRankEmbedding s lo hi hlo hhi
  have hcount := boolTrueCount_embedding (blockOf s lo hi) e
    (blockRankEmbedding_range s lo hi hlo hhi) v
  have hinterval := sortedBool_rankInterval_trueCount (v ∘ s.orderEmbOfFin rfl) hv lo hi hlo hhi
  have htotal := boolTrueCount_orderEmb s rfl v
  have heq : v ∘ e = fun j : Fin (hi - lo) =>
      (v ∘ s.orderEmbOfFin rfl) ⟨lo + j.val, by
        have hsum := Nat.add_sub_of_le hlo
        calc
          lo + j.val < lo + (hi - lo) := Nat.add_lt_add_left j.isLt _
          _ = hi := hsum
          _ ≤ s.card := hhi⟩ := by
    funext j
    rfl
  rw [← hcount, heq, hinterval, ← htotal]

theorem trueCountOn_eq_card_filter {N : Nat} (s : Finset (Fin N)) (v : Fin N → Bool) :
    trueCountOn s v = (s.filter (fun w => v w = true)).card := by
  classical
  let e : {w : s // v w.val = true} ≃
      {w // w ∈ s.filter (fun x => v x = true)} :=
    { toFun := fun w => ⟨w.val.val, by simp [w.val.property, w.property]⟩
      invFun := fun w => ⟨⟨w.val, (Finset.mem_filter.mp w.property).1⟩,
        (Finset.mem_filter.mp w.property).2⟩
      left_inv := by intro w; cases w; rfl
      right_inv := by intro w; cases w; rfl }
  unfold trueCountOn
  rw [Fintype.card_congr e]
  exact Fintype.card_coe (s.filter (fun x => v x = true))

/-- Injective relabeling preserves the Boolean count. -/
theorem trueCountOn_image {m N : Nat} (s : Finset (Fin m)) (f : Fin m → Fin N)
    (hf : Function.Injective f) (v : Fin N → Bool) :
    trueCountOn (s.image f) v = trueCountOn s (v ∘ f) := by
  let e : Fin s.card ↪ Fin N :=
    ⟨fun i => f (s.orderEmbOfFin rfl i), fun i j hij => by
      apply (s.orderEmbOfFin rfl).injective
      exact hf hij⟩
  have hrange : Set.range e = {w | w ∈ s.image f} := by
    ext w
    simp only [Set.mem_range, Set.mem_setOf_eq, Finset.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem _ rfl _, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, rfl⟩ := exists_orderEmb_eq hx
      exact ⟨i, rfl⟩
  calc
    trueCountOn (s.image f) v = boolTrueCount (v ∘ e) :=
      (boolTrueCount_embedding (s.image f) e hrange v).symm
    _ = boolTrueCount ((v ∘ f) ∘ s.orderEmbOfFin rfl) := by rfl
    _ = trueCountOn s (v ∘ f) := boolTrueCount_orderEmb s rfl (v ∘ f)

/-- Threshold counts add across disjoint finite supports. -/
theorem trueCountOn_union_disjoint {N : Nat} (A B : Finset (Fin N))
    (hdis : Disjoint A B) (v : Fin N → Bool) :
    trueCountOn (A ∪ B) v = trueCountOn A v + trueCountOn B v := by
  let p : Fin N → Prop := fun w => v w = true
  have hfilter : (A ∪ B).filter p = A.filter p ∪ B.filter p := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hdis' : Disjoint (A.filter p) (B.filter p) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    trueCountOn (A ∪ B) v = ((A ∪ B).filter p).card := trueCountOn_eq_card_filter _ _
    _ = (A.filter p).card + (B.filter p).card := by
      rw [hfilter, Finset.card_union_of_disjoint hdis']
    _ = trueCountOn A v + trueCountOn B v := by
      rw [← trueCountOn_eq_card_filter A v, ← trueCountOn_eq_card_filter B v]

theorem trueCountOn_biUnion {ι : Type*} {N : Nat} [DecidableEq ι] (I : Finset ι)
    (A : ι → Finset (Fin N))
    (hdis : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j))
    (v : Fin N → Bool) :
    trueCountOn (I.biUnion A) v = ∑ i ∈ I, trueCountOn (A i) v := by
  have hdis' : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint ((A i).filter (fun w => v w = true))
        ((A j).filter (fun w => v w = true)) := by
    intro i hi j hj hij
    exact (hdis i hi j hj hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [trueCountOn_eq_card_filter, Finset.filter_biUnion, Finset.card_biUnion hdis']
  simp_rw [← trueCountOn_eq_card_filter]

theorem sortedWireBags_intervalPartition_L1_exact {c N m p q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (hcard : ∀ packet, (S packet).card = m)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(trueCountOn (blockOf (S packet) (cuts packet i) (cuts packet (i + 1)))
          (v packet) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|) =
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  let V : Fin c → Fin m → Bool := fun packet i =>
    v packet ((S packet).orderEmbOfFin rfl (Fin.cast (hcard packet).symm i))
  have hV : ∀ packet, Monotone (V packet) := by
    intro packet i j hij
    apply hsorted packet
    apply Fin.le_iff_val_le_val.mpr
    exact Fin.le_iff_val_le_val.mp hij
  have htotal (packet : Fin c) : boolTrueCount (V packet) = trueCountOn (S packet) (v packet) := by
    calc
      boolTrueCount (V packet) = boolTrueCount (v packet ∘ (S packet).orderEmbOfFin rfl) := by
        dsimp [V]
        exact boolTrueCount_finCast (hcard packet).symm (v packet ∘ (S packet).orderEmbOfFin rfl)
      _ = trueCountOn (S packet) (v packet) := boolTrueCount_orderEmb (S packet) rfl (v packet)
  calc
    _ = ∑ packet : Fin c, ∑ i ∈ range p,
        |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
            V packet ⟨cuts packet i + j.val, by
              have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
              have hsum := Nat.add_sub_of_le hab
              calc
                cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                  Nat.add_lt_add_left j.isLt _
                _ = cuts packet (i + 1) := hsum
                _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply Finset.sum_congr rfl
      intro packet _
      apply Finset.sum_congr rfl
      intro i hi
      have hcutCard : cuts packet (i + 1) ≤ (S packet).card := by
        rw [hcard packet]
        exact hcutBound packet (i + 1)
      have hblock := trueCountOn_blockOf_profile (S packet) (v packet)
        (hsorted packet) (cuts packet i) (cuts packet (i + 1))
        (hcuts packet (Nat.le_succ i)) hcutCard
      have hinterval := sortedBool_rankInterval_trueCount (V packet) (hV packet)
        (cuts packet i) (cuts packet (i + 1)) (hcuts packet (Nat.le_succ i))
        (hcutBound packet (i + 1))
      rw [hcard packet] at hblock
      rw [hblock, ← htotal packet, ← hinterval]
    _ = ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro packet _
      have hVbound : boolTrueCount (V packet) ≤ m := by
        simpa [boolTrueCount] using
          (Fintype.card_subtype_le (fun i : Fin m => V packet i = true))
      have hprofile := profileInterval_partition_L1_exact m p
        (boolTrueCount (V packet)) q frac (cuts packet) (hstart packet) (hcuts packet)
        (hend packet) hVbound hq hfrac0 hfrac1
      have hinterval' (i : Nat) (hi : i < p) :
          boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
            V packet ⟨cuts packet i + j.val, by
              have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
              have hsum := Nat.add_sub_of_le hab
              calc
                cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                  Nat.add_lt_add_left j.isLt _
                _ = cuts packet (i + 1) := hsum
                _ ≤ m := hcutBound packet (i + 1)⟩) =
            profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) :=
        sortedBool_rankInterval_trueCount (V packet) (hV packet)
          (cuts packet i) (cuts packet (i + 1)) (hcuts packet (Nat.le_succ i))
          (hcutBound packet (i + 1))
      calc
        _ = ∑ i ∈ range p,
            |(profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) : Real) -
              profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hinterval' i (mem_range.mp hi)]
        _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile
        _ = |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
          rw [htotal packet]

/-- The 66 consecutive rank pieces that a sender routes: two separate
halves of its parent fringe and one middle block for each child. -/
def senderRankCut (up down i : Nat) : Nat :=
  if i = 0 then 0 else if i ≤ 65 then up / 2 + (i - 1) * down else up + 64 * down

theorem senderRankCut_le (up down i : Nat) : senderRankCut up down i ≤ up + 64 * down := by
  unfold senderRankCut
  split_ifs with hi0 hi65
  · omega
  · have hmul : (i - 1) * down ≤ 64 * down := Nat.mul_le_mul_right down (by omega)
    omega
  · rfl

theorem senderRankCut_mono (up down : Nat) : Monotone (senderRankCut up down) := by
  intro i j hij
  by_cases hi0 : i = 0
  · simp [senderRankCut, hi0]
  · by_cases hj65 : j ≤ 65
    · have hi65 : i ≤ 65 := le_trans hij hj65
      have hj0 : j ≠ 0 := by
        intro hj
        subst j
        exact hi0 (by omega)
      have hsub : i - 1 ≤ j - 1 := by omega
      have hmul := Nat.mul_le_mul_right down hsub
      simp [senderRankCut, hi0, hi65, hj65, hj0]
      exact hmul
    · have hle := senderRankCut_le up down i
      have hj0 : j ≠ 0 := by
        intro hj
        subst j
        exact hi0 (by omega)
      have hcutj : senderRankCut up down j = up + 64 * down := by
        simp [senderRankCut, hj0, hj65]
      rw [hcutj]
      exact hle

theorem senderRankCut_start (up down : Nat) : senderRankCut up down 0 = 0 := by
  simp [senderRankCut]

theorem senderRankCut_end (up down : Nat) : senderRankCut up down 66 = up + 64 * down := by
  simp [senderRankCut]

/-- The two omitted frontier fringe targets have total mass at most the
sender's up-flow capacity. -/
theorem senderRankCut_fringe_mean_sum_le (up down q : Nat) (frac : Real)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1))) ≤ up := by
  have hmean (i : Nat) (hi : i ∈ ({0, 65} : Finset Nat)) :
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
    have hi_lt : i < 66 := by simp at hi; omega
    have hmono := senderRankCut_mono up down (Nat.le_succ i)
    have hbound := senderRankCut_le up down (i + 1)
    exact (profileIntervalMean_bounds (up + 64 * down) q
      (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
      hmono hbound hfrac0 hfrac1).2
  calc
    _ ≤ ∑ i ∈ ({0, 65} : Finset Nat),
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmean i hi
    _ = up := by
      have hwidth : ∑ i ∈ ({0, 65} : Finset Nat),
          (senderRankCut up down (i + 1) - senderRankCut up down i) = up := by
        norm_num [senderRankCut]
        omega
      exact_mod_cast hwidth

/-- The 64 omitted upper-frontier middle targets have total mass at most
the sender's aggregate down-flow capacity. -/
theorem senderRankCut_middle_mean_sum_le (up down q : Nat) (frac : Real)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1))) ≤ 64 * down := by
  let middle := (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)
  have hwidth (i : Nat) (hi : i ∈ middle) :
      senderRankCut up down (i + 1) - senderRankCut up down i = down := by
    have hx := (Finset.mem_filter.mp hi).1
    have hb := (Finset.mem_filter.mp hi).2
    have hi0 : i ≠ 0 := by omega
    have hi64 : i ≤ 64 := hb.2
    have hnext : i + 1 ≤ 65 := by omega
    have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
      simp [senderRankCut, hi0, show i ≤ 65 by omega]
    have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
      simp [senderRankCut, hnext]
    rw [hcut, hcutNext]
    have hmul : i * down = (i - 1) * down + down := by
      calc
        i * down = ((i - 1) + 1) * down := by rw [Nat.sub_add_cancel hb.1]
        _ = (i - 1) * down + down := by rw [Nat.add_mul]; simp
    rw [hmul]
    omega
  have hmean (i : Nat) (hi : i ∈ middle) :
      profileIntervalMean (up + 64 * down) q frac
        (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤ down := by
    have hmono := senderRankCut_mono up down (Nat.le_succ i)
    have hbound := senderRankCut_le up down (i + 1)
    have hbounds := profileIntervalMean_bounds (up + 64 * down) q
      (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
      hmono hbound hfrac0 hfrac1
    calc
      profileIntervalMean (up + 64 * down) q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1)) ≤
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) :=
          hbounds.2
      _ = down := by exact_mod_cast hwidth i hi
  have hcard : middle.card = 64 := by
    have hset : middle = Finset.Icc 1 64 := by
      ext i
      simp [middle, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  calc
    _ ≤ ∑ i ∈ middle, (down : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmean i hi
    _ = (64 : Real) * down := by simp [hcard]

def senderOutgoingPiece {N : Nat} (s : Finset (Fin N)) (up down i : Nat) :
    Finset (Fin N) :=
  if i = 0 then blockOf s 0 (up / 2)
  else if i ≤ 64 then downSet s up down (i - 1)
  else blockOf s (s.card - up / 2) s.card

theorem senderOutgoingPiece_eq_blockOf {N : Nat} (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i : Nat) (hi : i < 66) :
    senderOutgoingPiece s up down i =
      blockOf s (senderRankCut up down i) (senderRankCut up down (i + 1)) := by
  by_cases hi0 : i = 0
  · subst i
    simp [senderOutgoingPiece, senderRankCut]
  · by_cases hi64 : i ≤ 64
    · have hnext : i + 1 ≤ 65 := by omega
      have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
        simp [senderRankCut, hi0, Nat.not_lt.mpr (by omega : i ≤ 65)]
      have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
        simp [senderRankCut, hnext]
      unfold senderOutgoingPiece
      rw [if_neg hi0, if_pos hi64]
      unfold downSet
      rw [hcut, hcutNext]
      have hiPos : 1 ≤ i := by omega
      rw [Nat.sub_add_cancel hiPos]
    · have hi65 : i = 65 := by omega
      subst i
      have hlast : s.card - up / 2 = up / 2 + 64 * down := by omega
      have hc65 : senderRankCut up down 65 = up / 2 + 64 * down := by
        simp [senderRankCut]
      have hc66 : senderRankCut up down 66 = s.card := by
        rw [senderRankCut_end, hs]
      unfold senderOutgoingPiece
      rw [if_neg (by omega : ¬65 = 0), if_neg (by omega : ¬65 ≤ 64), hlast, hc65, hc66]

theorem senderOutgoingPiece_card_eq_interval {N : Nat}
    (s : Finset (Fin N)) (up down : Nat)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up) (i : Nat) (hi : i < 66) :
    (senderOutgoingPiece s up down i).card =
      senderRankCut up down (i + 1) - senderRankCut up down i := by
  rw [senderOutgoingPiece_eq_blockOf s up down hs hu i hi]
  exact blockOf_card (by rw [hs]; exact senderRankCut_le up down (i + 1))

/-- A routed piece's actual Boolean count and its ideal mean both lie in the
piece capacity, so their absolute discrepancy is at most that capacity. -/
theorem senderOutgoingPiece_profile_error_le_capacity {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) (i : Nat) (hi : i < 66) :
    |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
      profileIntervalMean s.card q frac (senderRankCut up down i)
        (senderRankCut up down (i + 1))| ≤
      (senderRankCut up down (i + 1) - senderRankCut up down i : Nat) := by
  have hcard := senderOutgoingPiece_card_eq_interval s up down hs hu i hi
  have hcount : trueCountOn (senderOutgoingPiece s up down i) v ≤
      (senderOutgoingPiece s up down i).card := by
    rw [trueCountOn_eq_card_filter]
    exact Finset.card_filter_le _ _
  have hcountR : (trueCountOn (senderOutgoingPiece s up down i) v : Real) ≤
      (senderRankCut up down (i + 1) - senderRankCut up down i : Nat) := by
    exact_mod_cast (hcard ▸ hcount)
  have hmono := senderRankCut_mono up down (Nat.le_succ i)
  have hbound : senderRankCut up down (i + 1) ≤ s.card := by
    rw [hs]
    exact senderRankCut_le up down (i + 1)
  have hmean := profileIntervalMean_bounds s.card q
    (senderRankCut up down i) (senderRankCut up down (i + 1)) frac
    hmono hbound hfrac0 hfrac1
  apply abs_le.mpr
  constructor <;> linarith

/-- The combined omitted root/first-level fringe discrepancy of one sender is
bounded by its total up-flow capacity. -/
theorem senderOutgoing_fringe_profile_error_sum_le_up {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
        profileIntervalMean s.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))|) ≤ up := by
  calc
    _ ≤ ∑ i ∈ ({0, 65} : Finset Nat),
        ((senderRankCut up down (i + 1) - senderRankCut up down i : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < 66 := by simp at hi; omega
      exact senderOutgoingPiece_profile_error_le_capacity s v up down q frac
        hs hu hfrac0 hfrac1 i hi_lt
    _ = up := by
      have hwidth : ∑ i ∈ ({0, 65} : Finset Nat),
          (senderRankCut up down (i + 1) - senderRankCut up down i) = up := by
        norm_num [senderRankCut]
        omega
      exact_mod_cast hwidth

/-- The omitted top-frontier middle discrepancy of one sender is bounded by
the combined capacity of its 64 child ports. -/
theorem senderOutgoing_middle_profile_error_sum_le_down {N : Nat}
    (s : Finset (Fin N)) (v : Fin N → Bool) (up down q : Nat) (frac : Real)
    (hs : s.card = up + 64 * down) (hu : 2 ∣ up)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |(trueCountOn (senderOutgoingPiece s up down i) v : Real) -
        profileIntervalMean s.card q frac
          (senderRankCut up down i) (senderRankCut up down (i + 1))|) ≤ 64 * down := by
  let middle := (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)
  have hwidth (i : Nat) (hi : i ∈ middle) :
      senderRankCut up down (i + 1) - senderRankCut up down i = down := by
    have hb := (Finset.mem_filter.mp hi).2
    have hi0 : i ≠ 0 := by omega
    have hnext : i + 1 ≤ 65 := by omega
    have hcut : senderRankCut up down i = up / 2 + (i - 1) * down := by
      simp [senderRankCut, hi0, show i ≤ 65 by omega]
    have hcutNext : senderRankCut up down (i + 1) = up / 2 + i * down := by
      simp [senderRankCut, hnext]
    rw [hcut, hcutNext]
    have hmul : i * down = (i - 1) * down + down := by
      calc
        i * down = ((i - 1) + 1) * down := by rw [Nat.sub_add_cancel hb.1]
        _ = (i - 1) * down + down := by rw [Nat.add_mul]; simp
    rw [hmul]
    omega
  have hcard : middle.card = 64 := by
    have hset : middle = Finset.Icc 1 64 := by
      ext i
      simp [middle, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    simp
  calc
    _ ≤ ∑ i ∈ middle, (down : Real) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi_lt : i < 66 := by
        have := (Finset.mem_filter.mp hi).1
        simp at this
        omega
      have hpiece := senderOutgoingPiece_profile_error_le_capacity s v up down q frac
        hs hu hfrac0 hfrac1 i hi_lt
      rw [hwidth i hi] at hpiece
      exact hpiece
    _ = (64 : Real) * down := by simp [hcard]

theorem senderOutgoingPieces_are_WireFlow_ports {N : Nat} (s : Finset (Fin N))
    (up down : Nat) :
    senderOutgoingPiece s up down 0 ∪ senderOutgoingPiece s up down 65 = upSet s up ∧
      ∀ j < 64, senderOutgoingPiece s up down (j + 1) = downSet s up down j := by
  constructor
  · simp [senderOutgoingPiece, upSet]
  · intro j hj
    have hj1 : j + 1 ≤ 64 := by omega
    simp [senderOutgoingPiece, show j + 1 ≠ 0 by omega, hj1, Nat.succ_sub_one]

theorem sortedSenderOutgoing_profile_error_exact {c N m q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down : Fin c → Nat)
    (hcard : ∀ packet, (S packet).card = m)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range 66,
      |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real) -
        profileIntervalMean m q frac
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))|) =
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  let cuts : Fin c → Nat → Nat := fun packet i => senderRankCut (up packet) (down packet) i
  have hstart : ∀ packet, cuts packet 0 = 0 := by intro packet; exact senderRankCut_start _ _
  have hcuts : ∀ packet, Monotone (cuts packet) := by intro packet; exact senderRankCut_mono _ _
  have hcutBound : ∀ packet i, cuts packet i ≤ m := by
    intro packet i
    calc
      cuts packet i ≤ up packet + 64 * down packet := senderRankCut_le _ _ _
      _ = m := by rw [← hsize packet, hcard packet]
  have hend : ∀ packet, cuts packet 66 = m := by
    intro packet
    change senderRankCut (up packet) (down packet) 66 = m
    rw [senderRankCut_end, ← hsize packet, hcard packet]
  have hgeneric := sortedWireBags_intervalPartition_L1_exact frac S v hcard hsorted
    cuts hstart hcuts hcutBound hend hq hfrac0 hfrac1
  calc
    _ = ∑ packet : Fin c, ∑ i ∈ range 66,
        |(trueCountOn (blockOf (S packet) (cuts packet i) (cuts packet (i + 1)))
            (v packet) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply Finset.sum_congr rfl
      intro packet _
      apply Finset.sum_congr rfl
      intro i hi
      rw [senderOutgoingPiece_eq_blockOf (S packet) (up packet) (down packet)
        (hsize packet) (hu packet) i (mem_range.mp hi)]
    _ = ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := hgeneric

noncomputable def senderOutgoingProfileError {c N : Nat} (S : Fin c → Finset (Fin N))
    (v : Fin c → Fin N → Bool) (up down : Fin c → Nat)
    (q : Nat) (frac : Real) (packet : Fin c) (i : Nat) : Real :=
  |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
    profileIntervalMean (S packet).card q frac
      (senderRankCut (up packet) (down packet) i)
      (senderRankCut (up packet) (down packet) (i + 1))|

/-- Selecting any subset of the routed pieces for a receiver cannot amplify
the aggregate profile error: it is bounded by the sender cohort's original
coarse count error, independently of how many pieces are selected. -/
theorem selectedSenderOutgoing_profile_error_le {c N m q : Nat} (frac : Real)
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down : Fin c → Nat)
    (hcard : ∀ packet, (S packet).card = m)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    (∑ packet : Fin c, ∑ i ∈ selected packet,
      senderOutgoingProfileError S v up down q frac packet i) ≤
      ∑ packet : Fin c, |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
  have hfull := sortedSenderOutgoing_profile_error_exact frac S v up down
    hcard hsize hu hsorted hq hfrac0 hfrac1
  calc
    _ ≤ ∑ packet : Fin c, ∑ i ∈ range 66,
        senderOutgoingProfileError S v up down q frac packet i := by
      apply Finset.sum_le_sum
      intro packet _
      exact Finset.sum_le_sum_of_subset_of_nonneg (hselected packet) (by
        intro i hi hnot
        exact abs_nonneg _)
    _ = ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q + frac)| := by
      simpa [senderOutgoingProfileError, hcard] using hfull

noncomputable def senderOutgoingProfileErrorVar {Source : Type} {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (packet : Source) (i : Nat) : Real :=
  |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
    profileIntervalMean (S packet).card (q packet) (frac packet)
      (senderRankCut (up packet) (down packet) i)
      (senderRankCut (up packet) (down packet) (i + 1))|

/-- The no-loss sender partition identity also holds for unequal source bag
sizes and a separate fractional ideal count for each sender. This is the
shape needed when a receiver combines its larger parent bag with smaller child
bags. -/
theorem sortedSenderOutgoing_profile_error_exact_var
    {Source : Type} [Fintype Source] [DecidableEq Source] {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0) :
    (∑ packet : Source, ∑ i ∈ range 66,
      senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Source,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hlocal (packet : Source) :
      (∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i) =
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
    let cuts : Nat → Nat := senderRankCut (up packet) (down packet)
    have hstart : cuts 0 = 0 := senderRankCut_start _ _
    have hcuts : Monotone cuts := senderRankCut_mono _ _
    have hbound : ∀ i, cuts i ≤ (S packet).card := by
      intro i
      calc
        cuts i ≤ up packet + 64 * down packet := senderRankCut_le _ _ _
        _ = (S packet).card := (hsize packet).symm
    have hend : cuts 66 = (S packet).card := by
      change senderRankCut (up packet) (down packet) 66 = _
      rw [senderRankCut_end, hsize packet]
    have hcount (i : Nat) (hi : i < 66) :
        trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
            (v packet) =
          profileInterval (S packet).card (trueCountOn (S packet) (v packet))
            (cuts i) (cuts (i + 1)) := by
      rw [senderOutgoingPiece_eq_blockOf (S packet) (up packet) (down packet)
        (hsize packet) (hu packet) i hi]
      exact trueCountOn_blockOf_profile (S packet) (v packet) (hsorted packet)
        (cuts i) (cuts (i + 1)) (hcuts (Nat.le_succ i)) (hbound (i + 1))
    have hX : trueCountOn (S packet) (v packet) ≤ (S packet).card := by
      unfold trueCountOn
      simpa using (Fintype.card_subtype_le
        (fun w : S packet => v packet w.val = true))
    have hprofile := profileInterval_partition_L1_exact_allow_endpoint
      (S packet).card 66 (trueCountOn (S packet) (v packet)) (q packet)
      (frac packet) cuts hstart hcuts hend hX
      (hq packet) (hfrac0 packet) (hfrac1 packet) (hendpoint packet)
    calc
      (∑ i ∈ range 66,
          senderOutgoingProfileErrorVar S v up down q frac packet i) =
        ∑ i ∈ range 66,
          |(profileInterval (S packet).card (trueCountOn (S packet) (v packet))
              (cuts i) (cuts (i + 1)) : Real) -
            profileIntervalMean (S packet).card (q packet) (frac packet)
              (cuts i) (cuts (i + 1))| := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [senderOutgoingProfileErrorVar, hcount i (mem_range.mp hi)]
      _ = |(trueCountOn (S packet) (v packet) : Real) -
            (q packet + frac packet)| := hprofile
  calc
    (∑ packet : Source, ∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Source,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
      apply Finset.sum_congr rfl
      intro packet _
      exact hlocal packet

/-- Selecting any actual sender pieces still cannot amplify error when the
source bags have different sizes and ideal means. -/
theorem selectedSenderOutgoing_profile_error_le_var {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    (∑ packet : Fin c, ∑ i ∈ selected packet,
      senderOutgoingProfileErrorVar S v up down q frac packet i) ≤
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hfull := sortedSenderOutgoing_profile_error_exact_var S v up
    down q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  calc
    _ ≤ ∑ packet : Fin c, ∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i := by
      apply Finset.sum_le_sum
      intro packet _
      exact Finset.sum_le_sum_of_subset_of_nonneg (hselected packet) (by
        intro i hi hnot
        exact abs_nonneg _)
    _ = ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := hfull

/-- The combined threshold count entering a receiver differs from the sum of
its selected source-ideal interval counts by at most the senders' total coarse
count error. This is the aggregate form consumed by a later merge/deal bound. -/
theorem selectedSenderOutgoing_count_error_le_var {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet ≤ (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (hendpoint : ∀ packet, q packet = (S packet).card → frac packet = 0)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    |(∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
      ∑ packet : Fin c, ∑ i ∈ selected packet,
        profileIntervalMean (S packet).card (q packet) (frac packet)
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))| ≤
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  let err : Fin c → Nat → Real := fun packet i =>
    (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
      profileIntervalMean (S packet).card (q packet) (frac packet)
        (senderRankCut (up packet) (down packet) i)
        (senderRankCut (up packet) (down packet) (i + 1))
  have hdiff :
      (∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
        ∑ packet : Fin c, ∑ i ∈ selected packet,
          profileIntervalMean (S packet).card (q packet) (frac packet)
            (senderRankCut (up packet) (down packet) i)
            (senderRankCut (up packet) (down packet) (i + 1)) =
      ∑ packet : Fin c, ∑ i ∈ selected packet, err packet i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro packet _
    rw [← Finset.sum_sub_distrib]
  have hinner (packet : Fin c) :
      |∑ i ∈ selected packet, err packet i| ≤
        ∑ i ∈ selected packet, |err packet i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hselectedError := selectedSenderOutgoing_profile_error_le_var
    S v up down q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint selected hselected
  calc
    |(∑ packet : Fin c, ∑ i ∈ selected packet,
        (trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
          (v packet) : Real)) -
      ∑ packet : Fin c, ∑ i ∈ selected packet,
        profileIntervalMean (S packet).card (q packet) (frac packet)
          (senderRankCut (up packet) (down packet) i)
          (senderRankCut (up packet) (down packet) (i + 1))| =
      |∑ packet : Fin c, ∑ i ∈ selected packet, err packet i| := by rw [hdiff]
    _ ≤ ∑ packet : Fin c, |∑ i ∈ selected packet, err packet i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ packet : Fin c, ∑ i ∈ selected packet, |err packet i| := by
      apply Finset.sum_le_sum
      intro packet _
      exact hinner packet
    _ ≤ ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
      simpa [err, senderOutgoingProfileErrorVar] using hselectedError

/-- Selection pattern matching one `WireFlow` receiver when its sources are
indexed by the parent followed by its 64 children: take the receiver's one
down block from the parent, and both up-fringe halves from each child. -/
def receiverOutgoingSelection (parentPort : Nat) : Fin 65 → Finset Nat :=
  fun source => if source.val = 0 then {parentPort + 1} else {0, 65}

theorem receiverOutgoingSelection_subset (parentPort : Nat) (hport : parentPort < 64)
    (source : Fin 65) : receiverOutgoingSelection parentPort source ⊆ range 66 := by
  by_cases hsource : source.val = 0
  · simp [receiverOutgoingSelection, hsource]
    omega
  · rw [Finset.subset_iff]
    intro i hi
    simp [receiverOutgoingSelection, hsource] at hi
    rcases hi with rfl | rfl <;> simp
/-- The parent-plus-children-shaped selection has the same no-amplification
count bound. Instantiating its source data with actual `execPlacement` sets is
still a separate adapter obligation. -/
theorem wireFlowReceiver_count_error_le {N : Nat}
    (S : Fin 65 → Finset (Fin N)) (v : Fin 65 → Fin N → Bool)
    (up down q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source, Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0)
    (parentPort : Nat) (hport : parentPort < 64) :
    |(∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection parentPort source,
        (trueCountOn (senderOutgoingPiece (S source) (up source) (down source) i)
          (v source) : Real)) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection parentPort source,
        profileIntervalMean (S source).card (q source) (frac source)
          (senderRankCut (up source) (down source) i)
          (senderRankCut (up source) (down source) (i + 1))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  exact selectedSenderOutgoing_count_error_le_var S v up down q frac hsize hu hsorted
    hq hfrac0 hfrac1 hendpoint (receiverOutgoingSelection parentPort)
    (fun source => receiverOutgoingSelection_subset parentPort hport source)

/-- Layerwise sum of receiver discrepancies charges each source rank piece at
most once when routed selections are pairwise disjoint. -/
theorem sum_receiver_selected_errors_le_source_pieces
    {Receiver Source : Type} [Fintype Receiver] [Fintype Source]
    [DecidableEq Receiver] [DecidableEq Source]
    (err : Source → Nat → Real) (selected : Receiver → Source → Finset Nat)
    (hselected : ∀ receiver source, selected receiver source ⊆ range 66)
    (hdisjoint : ∀ source receiver₁ receiver₂, receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁ source) (selected receiver₂ source)) :
    (∑ receiver : Receiver,
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i|) ≤
      ∑ source : Source, ∑ i ∈ range 66, |err source i| := by
  classical
  have htriangle (receiver : Receiver) :
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i| ≤
        ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
    calc
      |∑ source : Source, ∑ i ∈ selected receiver source, err source i| ≤
          ∑ source : Source, |∑ i ∈ selected receiver source, err source i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
        apply Finset.sum_le_sum
        intro source _
        exact Finset.abs_sum_le_sum_abs _ _
  calc
    _ ≤ ∑ receiver : Receiver,
        ∑ source : Source, ∑ i ∈ selected receiver source, |err source i| := by
      apply Finset.sum_le_sum
      intro receiver _
      exact htriangle receiver
    _ = ∑ source : Source,
        ∑ receiver : Receiver, ∑ i ∈ selected receiver source, |err source i| := by
      rw [Finset.sum_comm]
    _ ≤ ∑ source : Source, ∑ i ∈ range 66, |err source i| := by
      apply Finset.sum_le_sum
      intro source _
      let pieces := Finset.univ.biUnion (fun receiver : Receiver => selected receiver source)
      have hpair : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Receiver)))
          (fun receiver => selected receiver source) := by
        intro receiver _ receiver' _ hne
        exact hdisjoint source receiver receiver' hne
      have hpieces :
          (∑ receiver : Receiver, ∑ i ∈ selected receiver source, |err source i|) =
            ∑ i ∈ pieces, |err source i| := by
        dsimp [pieces]
        rw [← Finset.sum_biUnion hpair]
      have hsub : pieces ⊆ range 66 := by
        intro i hi
        obtain ⟨receiver, _, hi⟩ := Finset.mem_biUnion.mp hi
        exact hselected receiver source hi
      rw [hpieces]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        exact abs_nonneg _)

/-- If receivers partition each sender's 66 outgoing rank pieces, the sum of
their absolute profile discrepancies is bounded by one coarse count error per
sender, regardless of how the pieces are grouped into receivers. -/
theorem sum_receiver_profile_errors_le_source_count_errors
    {Receiver Source : Type} [Fintype Receiver] [Fintype Source]
    [DecidableEq Receiver] [DecidableEq Source] {N : Nat}
    (S : Source → Finset (Fin N)) (v : Source → Fin N → Bool)
    (up down q : Source → Nat) (frac : Source → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source, Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0)
    (selected : Receiver → Source → Finset Nat)
    (hselected : ∀ receiver source, selected receiver source ⊆ range 66)
    (hdisjoint : ∀ source receiver₁ receiver₂, receiver₁ ≠ receiver₂ →
      Disjoint (selected receiver₁ source) (selected receiver₂ source)) :
    (∑ receiver : Receiver,
      |∑ source : Source,
        ∑ i ∈ selected receiver source,
          ((trueCountOn
            (senderOutgoingPiece (S source) (up source) (down source) i)
            (v source) : Real) -
          profileIntervalMean (S source).card (q source) (frac source)
            (senderRankCut (up source) (down source) i)
            (senderRankCut (up source) (down source) (i + 1)))|) ≤
      ∑ source : Source,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  let err : Source → Nat → Real := fun source i =>
    (trueCountOn (senderOutgoingPiece (S source) (up source) (down source) i)
      (v source) : Real) -
      profileIntervalMean (S source).card (q source) (frac source)
        (senderRankCut (up source) (down source) i)
        (senderRankCut (up source) (down source) (i + 1))
  calc
    _ ≤ ∑ source : Source, ∑ i ∈ range 66, |err source i| :=
      sum_receiver_selected_errors_le_source_pieces err selected hselected hdisjoint
    _ = ∑ source : Source,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
      simpa [err, senderOutgoingProfileErrorVar] using
        (sortedSenderOutgoing_profile_error_exact_var S v up down q frac
          hsize hu hsorted hq hfrac0 hfrac1 hendpoint)

/-- Rank pieces sent from `source` to `receiver`: child receivers get the
middle piece indexed by their child digit, and the parent gets both fringes. -/
def wireFlowLayerSelection {d : Nat} (receiver source : KBag 64 d) : Finset Nat :=
  (range 66).filter (fun i =>
    (1 ≤ receiver.l ∧ source = receiver.parent ∧ i = receiver.x % 64 + 1) ∨
    (1 ≤ source.l ∧ receiver = source.parent ∧ (i = 0 ∨ i = 65)))

theorem wireFlowLayerSelection_mem {d : Nat} (receiver source : KBag 64 d)
    (i : Nat) :
    i ∈ wireFlowLayerSelection receiver source ↔
      i ∈ range 66 ∧
        ((1 ≤ receiver.l ∧ source = receiver.parent ∧ i = receiver.x % 64 + 1) ∨
          (1 ≤ source.l ∧ receiver = source.parent ∧ (i = 0 ∨ i = 65))) := by
  simp only [wireFlowLayerSelection, Finset.mem_filter]

theorem wireFlowLayerSelection_subset {d : Nat} (receiver source : KBag 64 d) :
    wireFlowLayerSelection receiver source ⊆ range 66 := by
  intro i hi
  rw [wireFlowLayerSelection_mem] at hi
  exact hi.1

/-- Distinct receivers select disjoint rank-piece indices from a fixed
source bag. Child digits are unique; the parent's fringe indices are outside
the child-index range. -/
theorem wireFlowLayerSelection_pairwise_disjoint {d : Nat}
    (source receiver₁ receiver₂ : KBag 64 d) (hne : receiver₁ ≠ receiver₂) :
    Disjoint (wireFlowLayerSelection receiver₁ source)
      (wireFlowLayerSelection receiver₂ source) := by
  classical
  apply Finset.disjoint_left.2
  intro i hi₁ hi₂
  rw [wireFlowLayerSelection_mem] at hi₁ hi₂
  rcases hi₁.2 with hp₁ | hc₁ <;> rcases hi₂.2 with hp₂ | hc₂
  · have hparent : receiver₁.parent = receiver₂.parent :=
      hp₁.2.1.symm.trans hp₂.2.1
    have hport : receiver₁.x % 64 = receiver₂.x % 64 := by omega
    have hpX₁ : source.x = receiver₁.x / 64 := by
      have h := congrArg KBag.x hp₁.2.1
      simpa [KBag.parent] using h
    have hpX₂ : source.x = receiver₂.x / 64 := by
      have h := congrArg KBag.x hp₂.2.1
      simpa [KBag.parent] using h
    have hx₁ : receiver₁.x = 64 * source.x + receiver₁.x % 64 := by
      have h := Nat.mod_add_div receiver₁.x 64
      omega
    have hx₂ : receiver₂.x = 64 * source.x + receiver₂.x % 64 := by
      have h := Nat.mod_add_div receiver₂.x 64
      omega
    have hl : receiver₁.l = receiver₂.l := by
      have h := congrArg KBag.l hparent
      rw [KBag.parent_l, KBag.parent_l] at h
      omega
    apply hne
    exact KBag.ext hl (by rw [hx₁, hx₂, hport])
  · have hport : 0 < receiver₁.x % 64 + 1 ∧ receiver₁.x % 64 + 1 ≤ 64 := by
      have hmod := Nat.mod_lt receiver₁.x (by norm_num : 0 < 64)
      omega
    rcases hc₂.2.2 with hiZero | hiLast <;> omega
  · have hport : 0 < receiver₂.x % 64 + 1 ∧ receiver₂.x % 64 + 1 ≤ 64 := by
      have hmod := Nat.mod_lt receiver₂.x (by norm_num : 0 < 64)
      omega
    rcases hc₁.2.2 with hiZero | hiLast <;> omega
  · exact hne (hc₁.2.1.trans hc₂.2.1.symm)

/-- Every piece of an interior source bag is routed to exactly one active
receiver: pieces 1 through 64 go to its children, and the two fringe pieces
go to its parent. The two level restrictions exclude the root and top frontier. -/
theorem wireFlowLayerSelection_active_cover {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhi : source.l + 2 ≤ d) (i : Nat) (hi : i ∈ range 66) :
    ∃ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      i ∈ wireFlowLayerSelection receiver source := by
  rw [mem_range] at hi
  rcases eq_or_lt_of_le (show i ≤ 65 by omega) with hlast | hlt
  · subst i
    refine ⟨source.parent, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp [KBag.parent_l]
      omega
    · rw [wireFlowLayerSelection_mem]
      refine ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inr rfl⟩⟩
  · by_cases hzero : i = 0
    · subst i
      refine ⟨source.parent, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [KBag.parent_l]
        omega
      · rw [wireFlowLayerSelection_mem]
        refine ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inl rfl⟩⟩
    · have hidx : 1 ≤ i ∧ i ≤ 64 := by omega
      let receiver := source.child (i - 1) (by omega) (by omega)
      refine ⟨receiver, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · change 1 ≤ source.l + 1 ∧ source.l + 1 < d
        omega
      · rw [wireFlowLayerSelection_mem]
        have hlevel : 1 ≤ receiver.l := by
          simp [receiver, KBag.child_l]
        have hparent : source = receiver.parent := by
          dsimp [receiver]
          exact (KBag.child_parent source (i - 1) (by omega) (by omega)
            (by norm_num)).symm
        have hmod : receiver.x % 64 = i - 1 := by
          change (64 * source.x + (i - 1)) % 64 = i - 1
          omega
        have hindex : i = receiver.x % 64 + 1 := by omega
        refine ⟨mem_range.mpr (by omega), Or.inl ⟨hlevel, hparent, hindex⟩⟩

/-- On interior source levels, the active receiver selectors partition the
whole 66-piece sender profile, not merely a subset of it. -/
theorem wireFlowLayerSelection_active_union_eq_range {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) = range 66 := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    exact wireFlowLayerSelection_subset receiver source hpiece
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ :=
      wireFlowLayerSelection_active_cover source hlo hhi i hi
    exact Finset.mem_biUnion.mpr ⟨receiver, hreceiver, hpiece⟩

/-- A low-frontier source (root or first level) sends exactly its middle 64
pieces to active children; its parent fringe receiver is inactive. -/
theorem wireFlowLayerSelection_active_union_low {d : Nat}
    (source : KBag 64 d) (hlow : source.l ≤ 1)
    (hchild : source.l + 1 < d) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) =
      (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64) := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    rw [wireFlowLayerSelection_mem] at hpiece
    rcases hpiece.2 with hfromChild | hfromParent
    · exact Finset.mem_filter.mpr ⟨hpiece.1, by
        have hmod := Nat.mod_lt receiver.x (by norm_num : 0 < 64)
        omega⟩
    · have hreceiverParent := congrArg KBag.l hfromParent.2.1
      rw [KBag.parent_l] at hreceiverParent
      have : receiver.l = 0 := by omega
      have hactive := (Finset.mem_filter.mp hreceiver).2.1
      omega
  · intro hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hindex := (Finset.mem_filter.mp hi).1
    let receiver := source.child (i - 1) (by omega) (by omega)
    have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
      change 1 ≤ source.l + 1 ∧ source.l + 1 < d
      omega
    have hparent : source = receiver.parent := by
      dsimp [receiver]
      exact (KBag.child_parent source (i - 1) (by omega) (by omega)
        (by norm_num)).symm
    have hmod : receiver.x % 64 = i - 1 := by
      change (64 * source.x + (i - 1)) % 64 = i - 1
      omega
    have hpiece : i ∈ wireFlowLayerSelection receiver source := by
      rw [wireFlowLayerSelection_mem]
      refine ⟨hindex, Or.inl ⟨hreceiverLevel.1, hparent, ?_⟩⟩
      omega
    exact Finset.mem_biUnion.mpr ⟨receiver,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩

/-- At the upper frontier, an active source reaches only its two parent-fringe
pieces; no active receiver exists below those pieces. -/
theorem wireFlowLayerSelection_active_union_high {d : Nat}
    (source : KBag 64 d) (hlo : 2 ≤ source.l)
    (hhigh : d ≤ source.l + 1) :
    (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
      (fun receiver => wireFlowLayerSelection receiver source) = {0, 65} := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨receiver, hreceiver, hpiece⟩ := Finset.mem_biUnion.mp hi
    rw [wireFlowLayerSelection_mem] at hpiece
    rcases hpiece.2 with hfromChild | hfromParent
    · have hlevel := congrArg KBag.l hfromChild.2.1
      rw [KBag.parent_l] at hlevel
      have hactive := (Finset.mem_filter.mp hreceiver).2.2
      have hsourced : source.l ≤ d := source.hl
      omega
    · rcases hfromParent.2.2 with hzero | hlast
      · simp [hzero]
      · simp [hlast]
  · intro hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hzero | hlast
    · subst i
      let receiver := source.parent
      have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
        change 1 ≤ source.l - 1 ∧ source.l - 1 < d
        have hsourced : source.l ≤ d := source.hl
        omega
      have hpiece : 0 ∈ wireFlowLayerSelection receiver source := by
        rw [wireFlowLayerSelection_mem]
        exact ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inl rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨receiver,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩
    · subst i
      let receiver := source.parent
      have hreceiverLevel : 1 ≤ receiver.l ∧ receiver.l < d := by
        change 1 ≤ source.l - 1 ∧ source.l - 1 < d
        have hsourced : source.l ≤ d := source.hl
        omega
      have hpiece : 65 ∈ wireFlowLayerSelection receiver source := by
        rw [wireFlowLayerSelection_mem]
        exact ⟨mem_range.mpr (by omega), Or.inr ⟨by omega, rfl, Or.inr rfl⟩⟩
      exact Finset.mem_biUnion.mpr ⟨receiver,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreceiverLevel⟩, hpiece⟩

/-- Complete selector geometry for every source bag once the tree has height
at least three: low sources send the 64 middle pieces, interior sources send
all 66, and top-frontier sources send only the two fringes. -/
theorem wireFlowLayerSelection_active_union_complete {d : Nat}
    (hd : 3 ≤ d) (source : KBag 64 d) :
    (source.l ≤ 1 ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) =
          (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64)) ∨
    (2 ≤ source.l ∧ source.l + 2 ≤ d ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = range 66) ∨
    (2 ≤ source.l ∧ d ≤ source.l + 1 ∧
      (Finset.univ.filter (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = {0, 65}) := by
  by_cases hlow : source.l ≤ 1
  · exact Or.inl ⟨hlow,
      wireFlowLayerSelection_active_union_low source hlow (by omega)⟩
  · have hsource : 2 ≤ source.l := by omega
    by_cases hmid : source.l + 2 ≤ d
    · exact Or.inr (Or.inl ⟨hsource, hmid,
        wireFlowLayerSelection_active_union_eq_range source hsource hmid⟩)
    · exact Or.inr (Or.inr ⟨hsource, by omega,
        wireFlowLayerSelection_active_union_high source hsource (by omega)⟩)

/-- Any exact active-selector union identity immediately gives the matching
additive conservation identity, since selectors for distinct receivers are
pairwise disjoint. -/
theorem wireFlowLayerSelection_active_sum_eq_union {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d) (pieces : Finset Nat)
    (hunion : (Finset.univ.filter
      (fun b : KBag 64 d => 1 ≤ b.l ∧ b.l < d)).biUnion
        (fun receiver => wireFlowLayerSelection receiver source) = pieces)
    (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ pieces, f i := by
  classical
  let active := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  have hdis : Set.PairwiseDisjoint (↑active : Set (KBag 64 d))
      (fun receiver => wireFlowLayerSelection receiver source) := by
    intro receiver hreceiver other hother hne
    exact wireFlowLayerSelection_pairwise_disjoint source receiver other hne
  calc
    (∑ receiver ∈ active,
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
        ∑ i ∈ active.biUnion (fun receiver => wireFlowLayerSelection receiver source),
          f i := (Finset.sum_biUnion hdis).symm
    _ = ∑ i ∈ pieces, f i := by rw [hunion]

theorem wireFlowLayerSelection_active_sum_eq_low {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlow : source.l ≤ 1) (hchild : source.l + 1 < d) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64), f i :=
  wireFlowLayerSelection_active_sum_eq_union source _
    (wireFlowLayerSelection_active_union_low source hlow hchild) f

theorem wireFlowLayerSelection_active_sum_eq_high {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhigh : d ≤ source.l + 1) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      f 0 + f 65 := by
  rw [wireFlowLayerSelection_active_sum_eq_union source {0, 65}
    (wireFlowLayerSelection_active_union_high source hlo hhigh) f]
  simp

/-- Consequently, summing any additive piece quantity over the active
receivers preserves the exact full source total on interior bag levels. -/
theorem wireFlowLayerSelection_active_sum_eq_range {d : Nat}
    {M : Type*} [AddCommMonoid M] (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) (f : Nat → M) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
      ∑ i ∈ range 66, f i := by
  classical
  let active := (Finset.univ : Finset (KBag 64 d)).filter
    (fun b => 1 ≤ b.l ∧ b.l < d)
  have hdis : Set.PairwiseDisjoint (↑active : Set (KBag 64 d))
      (fun receiver => wireFlowLayerSelection receiver source) := by
    intro receiver hreceiver other hother hne
    exact wireFlowLayerSelection_pairwise_disjoint source receiver other hne
  calc
    (∑ receiver ∈ active,
      ∑ i ∈ wireFlowLayerSelection receiver source, f i) =
        ∑ i ∈ active.biUnion (fun receiver => wireFlowLayerSelection receiver source),
          f i := (Finset.sum_biUnion hdis).symm
    _ = ∑ i ∈ range 66, f i := by
      rw [wireFlowLayerSelection_active_union_eq_range source hlo hhi]

/-- Actual bag-indexed incidence bound: summing the absolute routed-profile
errors over every receiver in the 64-ary tree charges each sender's coarse
count error only once. The hypotheses carry the source sorting and ideal-count
invariants; the routing disjointness itself is proved above. -/
theorem wireFlowLayer_profile_error_sum_le {d N : Nat}
    (S : KBag 64 d → Finset (Fin N)) (v : KBag 64 d → Fin N → Bool)
    (up down q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsize : ∀ source, (S source).card = up source + 64 * down source)
    (hu : ∀ source, 2 ∣ up source)
    (hsorted : ∀ source,
      Monotone (v source ∘ (S source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (S source).card → frac source = 0) :
    (∑ receiver : KBag 64 d,
      |∑ source : KBag 64 d,
        ∑ i ∈ wireFlowLayerSelection receiver source,
          ((trueCountOn
            (senderOutgoingPiece (S source) (up source) (down source) i)
            (v source) : Real) -
          profileIntervalMean (S source).card (q source) (frac source)
            (senderRankCut (up source) (down source) i)
            (senderRankCut (up source) (down source) (i + 1)))|) ≤
      ∑ source : KBag 64 d,
        |(trueCountOn (S source) (v source) : Real) - (q source + frac source)| := by
  classical
  exact sum_receiver_profile_errors_le_source_count_errors
    S v up down q frac hsize hu hsorted hq hfrac0 hfrac1
    hendpoint
    wireFlowLayerSelection
    (fun receiver source => wireFlowLayerSelection_subset receiver source)
    (fun source receiver₁ receiver₂ hne =>
      wireFlowLayerSelection_pairwise_disjoint source receiver₁ receiver₂ hne)

def wireFlowReceiverSource {d : Nat} (b : KBag 64 d) (hchild : b.l < d)
    (source : Fin 65) : KBag 64 d :=
  if h : source.val = 0 then b.parent
  else b.child (source.val - 1) (by have hs := source.isLt; omega) hchild

def wireFlowReceiverChildSource (j : Fin 64) : Fin 65 :=
  ⟨j.val + 1, by have hj := j.isLt; omega⟩

theorem wireFlowReceiverSource_parent {d : Nat} (b : KBag 64 d) (hchild : b.l < d) :
    wireFlowReceiverSource b hchild ⟨0, by omega⟩ = b.parent := by
  simp [wireFlowReceiverSource]

theorem wireFlowReceiverSource_child {d : Nat} (b : KBag 64 d) (hchild : b.l < d)
    (j : Fin 64) :
    wireFlowReceiverSource b hchild (wireFlowReceiverChildSource j) =
      b.child j.val j.isLt hchild := by
  simp [wireFlowReceiverSource, wireFlowReceiverChildSource]

/-- For each receiver, the global bag selector agrees on its 65 actual
neighbors with the local parent-plus-children selector used by the register
identity. -/
theorem wireFlowLayerSelection_receiverSource {d : Nat}
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d) (source : Fin 65) :
    wireFlowLayerSelection b (wireFlowReceiverSource b hchild source) =
      receiverOutgoingSelection (b.x % 64) source := by
  classical
  rcases source with ⟨s, hslt⟩
  by_cases hs : s = 0
  · subst s
    have hnotParentParent : b ≠ b.parent.parent := by
      intro h
      have hl := congrArg KBag.l h
      rw [KBag.parent_l, KBag.parent_l] at hl
      omega
    ext i
    rw [wireFlowLayerSelection_mem, wireFlowReceiverSource_parent]
    simp [receiverOutgoingSelection, Fin.val_mk]
    constructor
    · intro h
      rcases h.2 with hp | hc
      · exact hp.2
      · exact False.elim (hnotParentParent hc.2.1)
    · intro h
      refine ⟨?_, Or.inl ⟨hb, h⟩⟩
      have hmod := Nat.mod_lt b.x (by norm_num : 0 < 64)
      change i < 66
      omega
  · have hj : s - 1 < 64 := by omega
    let j : Fin 64 := ⟨s - 1, hj⟩
    have hsource : (⟨s, hslt⟩ : Fin 65) = wireFlowReceiverChildSource j := by
      apply Fin.ext
      simp [j, wireFlowReceiverChildSource]
      omega
    rw [hsource]
    have hbag := wireFlowReceiverSource_child b hchild j
    have hchildParent : (b.child j.val j.isLt hchild).parent = b :=
      KBag.child_parent b j.val j.isLt hchild (by omega)
    ext i
    rw [wireFlowLayerSelection_mem, hbag]
    simp only [receiverOutgoingSelection, wireFlowReceiverChildSource,
      Fin.val_mk]
    have hjnz : ¬(j.val + 1 = 0) := by omega
    rw [if_neg hjnz]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases h.2 with hp | hc
      · have hl := congrArg KBag.l hp.2.1
        rw [KBag.child_l, KBag.parent_l] at hl
        omega
      · exact hc.2.2
    · intro h
      have hmod := Nat.mod_lt b.x (by norm_num : 0 < 64)
      rcases h with h | h
      · refine ⟨?_, Or.inr ⟨by simp [KBag.child_l], hchildParent.symm, Or.inl h⟩⟩
        exact mem_range.mpr (by omega)
      · refine ⟨?_, Or.inr ⟨by simp [KBag.child_l], hchildParent.symm, Or.inr h⟩⟩
        exact mem_range.mpr (by omega)

/-- The source bags incident to an active receiver: its parent followed by its
64 children (when present). -/
def wireFlowReceiverNeighborBags {d : Nat} (b : KBag 64 d) (hchild : b.l < d) :
    Finset (KBag 64 d) :=
  insert (b.parent (by omega))
    (Finset.univ.image (fun j : Fin 64 => b.child j.val j.isLt hchild))

theorem wireFlowReceiverNeighborBags_mem {d : Nat}
    (b : KBag 64 d) (hchild : b.l < d) (source : KBag 64 d) :
    source ∈ wireFlowReceiverNeighborBags b hchild ↔
      source = b.parent ∨ ∃ j : Fin 64, source = b.child j.val j.isLt hchild := by
  simp [wireFlowReceiverNeighborBags, eq_comm]

/-- The global selector vanishes outside the actual parent/children source
bags of an active receiver. -/
theorem wireFlowLayerSelection_eq_empty_of_not_neighbor {d : Nat}
    (b source : KBag 64 d) (hchild : b.l < d)
    (hnot : source ∉ wireFlowReceiverNeighborBags b hchild) :
    wireFlowLayerSelection b source = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [wireFlowLayerSelection_mem] at hi
  rcases hi.2 with hp | hc
  · exact hnot ((wireFlowReceiverNeighborBags_mem b hchild source).2 (Or.inl hp.2.1))
  · have hparent_lt : (source.parent).l < d := by simpa [hc.2.1] using hchild
    have hpc := KBag.parent_child source hc.1 (by omega) hparent_lt
    have hsrc : source = b.child (source.x % 64)
        (Nat.mod_lt _ (by omega)) hchild := by
      simpa [← hc.2.1] using hpc.symm
    exact hnot ((wireFlowReceiverNeighborBags_mem b hchild source).2
      (Or.inr ⟨⟨source.x % 64, Nat.mod_lt _ (by omega)⟩, hsrc⟩))

theorem fin65_sum_parent_children {α : Type*} [AddCommMonoid α]
    (f : Fin 65 → α) :
    (∑ source : Fin 65, f source) =
      f ⟨0, by omega⟩ + ∑ j : Fin 64, f (wireFlowReceiverChildSource j) := by
  rw [Fin.sum_univ_succ]
  congr 1

/-- Reindex the global source sum for one active receiver onto its actual
parent-plus-children `Fin 65` source map. -/
theorem wireFlowLayerSelection_receiverSum_eq {d : Nat}
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (f : KBag 64 d → Nat → Real) :
    (∑ source : KBag 64 d,
      ∑ i ∈ wireFlowLayerSelection b source, f source i) =
    (∑ source : Fin 65,
      ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        f (wireFlowReceiverSource b hchild source) i) := by
  classical
  let g : KBag 64 d → Real := fun source =>
    ∑ i ∈ wireFlowLayerSelection b source, f source i
  let neighbors := wireFlowReceiverNeighborBags b hchild
  have hzero (source : KBag 64 d) (hnot : source ∉ neighbors) : g source = 0 := by
    simp [g, wireFlowLayerSelection_eq_empty_of_not_neighbor b source hchild hnot]
  have hparentNotChild :
      b.parent ∉ Finset.univ.image (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro h
    obtain ⟨j, _, hEq⟩ := Finset.mem_image.mp h
    have hl := congrArg KBag.l hEq
    rw [KBag.parent_l, KBag.child_l] at hl
    omega
  have hchildInj : Function.Injective (fun j : Fin 64 => b.child j.val j.isLt hchild) := by
    intro j k hEq
    apply Fin.ext
    exact KBag.child_inj b j.val k.val j.isLt k.isLt hchild hEq
  calc
    (∑ source : KBag 64 d, g source) =
        ∑ source ∈ Finset.univ, g source := by simp
    _ = ∑ source ∈ neighbors, g source := by
      symm
      exact Finset.sum_subset (Finset.subset_univ neighbors) (by
        intro source _ hnot
        exact hzero source hnot)
    _ = g b.parent + ∑ j : Fin 64, g (b.child j.val j.isLt hchild) := by
      simp only [neighbors, wireFlowReceiverNeighborBags]
      rw [Finset.sum_insert hparentNotChild]
      rw [Finset.sum_image]
      exact hchildInj.injOn
    _ = ∑ source : Fin 65, g (wireFlowReceiverSource b hchild source) := by
      rw [fin65_sum_parent_children]
      rw [wireFlowReceiverSource_parent]
      simp_rw [wireFlowReceiverSource_child]
    _ = ∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
          f (wireFlowReceiverSource b hchild source) i := by
      apply Finset.sum_congr rfl
      intro source _
      simp only [g]
      rw [wireFlowLayerSelection_receiverSource b hb hchild source]



theorem receiverOutgoingSelection_sum (parentPort : Nat)
    (source : Fin 65) (f : Nat → Nat) :
    (∑ i ∈ receiverOutgoingSelection parentPort source, f i) =
      if source.val = 0 then f (parentPort + 1) else f 0 + f 65 := by
  by_cases hs : source.val = 0
  · simp [receiverOutgoingSelection, hs]
  · simp [receiverOutgoingSelection, hs]

/-- Instantiate the parent/children profile estimate on the actual source
wire sets and flow sizes from `WireFlow`. The sortedness premise says each
sender's post-stage Boolean values are in rank order. The theorem bounds the
sum of selected incoming-piece counts; identifying that sum with a count on
`execPlacement.regs` still requires the disjoint-image adapter. -/
theorem wireFlowReceiver_count_error_actual {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source,
      q source = (wireSets F t (wireFlowReceiverSource b hchild source)).card →
        frac source = 0) :
    |(∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        ((trueCountOn
          (senderOutgoingPiece (wireSets F t (wireFlowReceiverSource b hchild source))
            (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (fun w => predicate (X F nets input (t + 1) w))) : Real) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q source) (frac source)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1)))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  let S : Fin 65 → Finset (Fin (64 ^ d)) :=
    fun source => wireSets F t (wireFlowReceiverSource b hchild source)
  let val : Fin 65 → Fin (64 ^ d) → Bool :=
    fun _ w => predicate (X F nets input (t + 1) w)
  let up : Fin 65 → Nat := fun source =>
    F.up (wireFlowReceiverSource b hchild source).l t
  let down : Fin 65 → Nat := fun source =>
    F.down (wireFlowReceiverSource b hchild source).l t
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize : ∀ source, (S source).card = up source + 64 * down source := by
    intro source
    change (wireSets F t (wireFlowReceiverSource b hchild source)).card = _
    rw [hinv.1 (wireFlowReceiverSource b hchild source)]
    exact F.hsplit _ _ (wireFlowReceiverSource b hchild source).hl ht
  have hu : ∀ source, 2 ∣ up source := by
    intro source
    exact F.hup_even _ _ ht
  have hsorted' : ∀ source, Monotone (val source ∘ (S source).orderEmbOfFin rfl) := by
    intro source
    exact hsorted source
  have hq' : ∀ source, q source ≤ (S source).card := hq
  have hendpoint' : ∀ source, q source = (S source).card → frac source = 0 := hendpoint
  have hfrac0' : ∀ source, 0 ≤ frac source := hfrac0
  have hfrac1' : ∀ source, frac source ≤ 1 := hfrac1
  have hparentPort : b.x % 64 < 64 := Nat.mod_lt _ (by omega)
  simpa [S, val, up, down] using
    (wireFlowReceiver_count_error_le S val up down q frac hsize hu hsorted'
      hq' hfrac0' hfrac1' hendpoint' (b.x % 64) hparentPort)

/-- The selected interval counts in the previous theorem are exactly the
threshold count on the receiver's actual `execPlacement` register. This uses
the parent/child port decomposition, injectivity of execution, and disjoint
source bags; it removes the selected-sum versus receiver-count gap. -/
theorem wireFlowReceiver_selected_count_eq_register {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool) :
    (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
      trueCountOn
        (senderOutgoingPiece (wireSets F t (wireFlowReceiverSource b hchild source))
          (F.up (wireFlowReceiverSource b hchild source).l t)
          (F.down (wireFlowReceiverSource b hchild source).l t) i)
        (fun w => predicate (X F nets input (t + 1) w))) =
       trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate := by
  let Xout := X F nets input (t + 1)
  let sourceBag := wireFlowReceiverSource b hchild
  let senderSet (source : Fin 65) := wireSets F t (sourceBag source)
  let senderUp (source : Fin 65) := F.up (sourceBag source).l t
  let senderDown (source : Fin 65) := F.down (sourceBag source).l t
  let value (w : Fin (64 ^ d)) := predicate (Xout w)
  let source0 : Fin 65 := ⟨0, by omega⟩
  have hsource0 : sourceBag source0 = b.parent := by
    exact wireFlowReceiverSource_parent b hchild
  have hXinj : Function.Injective Xout := X_injective F nets input (t + 1)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hparentPort : b.x % 64 < 64 := Nat.mod_lt _ (by omega)
  have hparentPiece :
      senderOutgoingPiece (wireSets F t b.parent) (F.up b.parent.l t)
          (F.down b.parent.l t) (b.x % 64 + 1) =
        downSet (wireSets F t b.parent) (F.up b.parent.l t)
          (F.down b.parent.l t) (b.x % 64) :=
    (senderOutgoingPieces_are_WireFlow_ports (wireSets F t b.parent)
      (F.up b.parent.l t) (F.down b.parent.l t)).2 _ hparentPort
  have hparentSelected :
      (∑ i ∈ receiverOutgoingSelection (b.x % 64) source0,
        trueCountOn (senderOutgoingPiece (senderSet source0) (senderUp source0)
          (senderDown source0) i) value) =
        trueCountOn (fromParentK F nets input t b) predicate := by
    have hsourceZero : wireFlowReceiverSource b hchild 0 = b.parent := by
      simpa [source0] using hsource0
    simp only [receiverOutgoingSelection, source0, Fin.val_mk, if_pos rfl,
      Finset.sum_singleton]
    dsimp [senderSet, senderUp, senderDown, sourceBag]
    simp only [Finset.sum_singleton]
    rw [hsourceZero, hparentPiece]
    symm
    simp [fromParentK, hb, KBag.parent_l, Xout]
    rw [trueCountOn_image _ Xout hXinj predicate]
    rfl
  have hsourceSize (source : Fin 65) :
      (senderSet source).card = senderUp source + 64 * senderDown source := by
    calc
      (senderSet source).card = F.a (sourceBag source).l t := hinv.1 (sourceBag source)
      _ = senderUp source + 64 * senderDown source :=
        F.hsplit _ _ (sourceBag source).hl ht
  have hchildPieceDisjoint (j : Fin 64) :
      Disjoint
        (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0)
        (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65) := by
    let s := wireSets F t (b.child j.val j.isLt hchild)
    let up := F.up (b.l + 1) t
    let down := F.down (b.l + 1) t
    have hsize : s.card = up + 64 * down := by
      simpa [s, up, down, KBag.child_l] using
        (hinv.1 (b.child j.val j.isLt hchild)).trans
          (F.hsplit (b.l + 1) t (by omega) ht)
    have heven : 2 ∣ up := F.hup_even _ _ ht
    rw [senderOutgoingPiece_eq_blockOf s up down hsize heven 0 (by omega),
      senderOutgoingPiece_eq_blockOf s up down hsize heven 65 (by omega)]
    have hcut : senderRankCut up down 1 ≤ senderRankCut up down 65 := by
      simp [senderRankCut]
    exact disjoint_blockOf hcut
  have hchildCount (j : Fin 64) :
      (∑ i ∈ receiverOutgoingSelection (b.x % 64)
          (wireFlowReceiverChildSource j),
        trueCountOn
          (senderOutgoingPiece (senderSet (wireFlowReceiverChildSource j))
            (senderUp (wireFlowReceiverChildSource j))
            (senderDown (wireFlowReceiverChildSource j)) i) value) =
        trueCountOn
          ((upSet (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t)).image Xout) predicate := by
    let childSource := wireFlowReceiverChildSource j
    have hchildSourceNe : childSource ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [childSource, wireFlowReceiverChildSource] at hv
    have hbag : sourceBag childSource = b.child j.val j.isLt hchild :=
      wireFlowReceiverSource_child b hchild j
    have hports := senderOutgoingPieces_are_WireFlow_ports
      (wireSets F t (b.child j.val j.isLt hchild)) (F.up (b.l + 1) t)
      (F.down (b.l + 1) t)
    have hdisImage : Disjoint
        ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0).image Xout)
        ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65).image Xout) := by
      rw [Finset.disjoint_image hXinj]
      exact hchildPieceDisjoint j
    calc
      _ = trueCountOn
          (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0) value +
          trueCountOn
          (senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65) value := by
        simp [receiverOutgoingSelection, childSource, hchildSourceNe,
          wireFlowReceiverSource_child, sourceBag, senderSet, senderUp, senderDown,
          value, KBag.child_l]
      _ = trueCountOn
          ((senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t) (F.down (b.l + 1) t) 0 ∪
            senderOutgoingPiece (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t) (F.down (b.l + 1) t) 65).image Xout) predicate := by
        rw [Finset.image_union,
          trueCountOn_union_disjoint _ _ hdisImage predicate]
        rw [trueCountOn_image _ Xout hXinj, trueCountOn_image _ Xout hXinj]
        rfl
      _ = trueCountOn
          ((upSet (wireSets F t (b.child j.val j.isLt hchild))
              (F.up (b.l + 1) t)).image Xout) predicate := by
        rw [hports.1]
  have hchildPairDisjoint (j k : Fin 64) (hjk : j ≠ k) :
      Disjoint
        ((upSet (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t)).image Xout)
        ((upSet (wireSets F t (b.child k.val k.isLt hchild))
          (F.up (b.l + 1) t)).image Xout) := by
    rw [Finset.disjoint_image hXinj]
    apply Disjoint.mono upSet_subset upSet_subset
    apply hinv.2.1
    intro he
    apply hjk
    exact Fin.ext (KBag.child_inj b j.val k.val j.isLt k.isLt hchild he)
  have hchildrenCount :
      trueCountOn (fromChildrenK F nets input t b) predicate =
        ∑ j : Fin 64,
          trueCountOn
            ((upSet (wireSets F t (b.child j.val j.isLt hchild))
                (F.up (b.l + 1) t)).image Xout) predicate := by
    unfold fromChildrenK
    rw [dif_pos hchild]
    rw [trueCountOn_biUnion Finset.univ
      (fun j : Fin 64 =>
        (upSet (wireSets F t (b.child j.val j.isLt hchild))
          (F.up (b.l + 1) t)).image Xout)
      (by
        intro j _ k _ hjk
        exact hchildPairDisjoint j k hjk) predicate]
  have hparentChildDisjoint :
      Disjoint (fromParentK F nets input t b) (fromChildrenK F nets input t b) := by
    unfold fromParentK fromChildrenK
    rw [dif_pos hchild, Finset.disjoint_biUnion_right]
    intro j hj
    rw [Finset.disjoint_image hXinj]
    apply Disjoint.mono downSet_subset upSet_subset
    apply hinv.2.1
    intro he
    have hl := congrArg KBag.l he
    rw [KBag.parent_l, KBag.child_l] at hl
    omega
  have hregisterCount :
      trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate =
        trueCountOn (fromParentK F nets input t b) predicate +
          trueCountOn (fromChildrenK F nets input t b) predicate := by
    rw [execPlacement_succ_regs F nets input t ht b hb]
    exact trueCountOn_union_disjoint _ _ hparentChildDisjoint predicate
  let pieceCount (source : Fin 65) :=
    ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
      trueCountOn (senderOutgoingPiece (senderSet source) (senderUp source)
        (senderDown source) i) value
  have hsum := fin65_sum_parent_children pieceCount
  calc
    (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        trueCountOn
          (senderOutgoingPiece (senderSet source) (senderUp source) (senderDown source) i)
          value) =
      trueCountOn (fromParentK F nets input t b) predicate +
        trueCountOn (fromChildrenK F nets input t b) predicate := by
      rw [hsum]
      change pieceCount source0 + ∑ j : Fin 64, pieceCount (wireFlowReceiverChildSource j) = _
      rw [show pieceCount source0 =
        trueCountOn (fromParentK F nets input t b) predicate from hparentSelected]
      simp_rw [show ∀ j : Fin 64,
        pieceCount (wireFlowReceiverChildSource j) =
          trueCountOn ((upSet (wireSets F t (b.child j.val j.isLt hchild))
            (F.up (b.l + 1) t)).image Xout) predicate from hchildCount]
      rw [← hchildrenCount]
    _ = trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b) predicate :=
      hregisterCount.symm

/-- Actual threshold count in one sender's outgoing rank piece. -/
noncomputable def wireFlowLayerSenderPieceCount {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (predicate : Fin (64 ^ d) → Bool) (source : KBag 64 d) (i : Nat) : Nat :=
  trueCountOn
    (senderOutgoingPiece (wireSets F t source)
      (F.up source.l t) (F.down source.l t) i)
    (fun w => predicate (X F nets input (t + 1) w))

/-- Ideal profile mean assigned to one sender rank piece. -/
def wireFlowLayerSenderPieceMean {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d) (i : Nat) : Real :=
  profileIntervalMean (wireSets F t source).card (q source) (frac source)
    (senderRankCut (F.up source.l t) (F.down source.l t) i)
    (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))

/-- For every interior source bag, summing its ideal rank-piece means over
the active destinations recovers the entire source mean profile. This exact
conservation law is stronger than the one-sided no-amplification estimate. -/
theorem wireFlowLayerSenderPieceMean_active_sum_eq {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceMean F t q frac source i) =
      ∑ i ∈ range 66, wireFlowLayerSenderPieceMean F t q frac source i := by
  exact wireFlowLayerSelection_active_sum_eq_range source hlo hhi
    (wireFlowLayerSenderPieceMean F t q frac source)

/-- The active destinations receive exactly the source's fractional target
mass, once all source rank pieces are accounted for. -/
theorem wireFlowLayerSenderPieceMean_active_sum_eq_target {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d)
    (hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t)
    (hq : q source ≤ (wireSets F t source).card)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1)
    (hendpoint : q source = (wireSets F t source).card → frac source = 0)
    (hlo : 2 ≤ source.l) (hhi : source.l + 2 ≤ d) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceMean F t q frac source i) =
      (q source : Real) + frac source := by
  rw [wireFlowLayerSenderPieceMean_active_sum_eq F t q frac source hlo hhi]
  have hstart := senderRankCut_start (F.up source.l t) (F.down source.l t)
  have hcuts := senderRankCut_mono (F.up source.l t) (F.down source.l t)
  have hend : senderRankCut (F.up source.l t) (F.down source.l t) 66 =
      (wireSets F t source).card := by
    rw [senderRankCut_end, hsize]
  simpa [wireFlowLayerSenderPieceMean] using
    (profileIntervalMean_partition_sum (wireSets F t source).card 66
      (q source) (frac source)
      (senderRankCut (F.up source.l t) (F.down source.l t))
      hstart hcuts hend hq hfrac0 hfrac1 hendpoint)

/-- Signed discrepancy contributed by one routed sender piece. -/
noncomputable def wireFlowLayerSenderPieceError {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (source : KBag 64 d) (i : Nat) : Real :=
  (wireFlowLayerSenderPieceCount F nets input t predicate source i : Real) -
    wireFlowLayerSenderPieceMean F t q frac source i

/-- Across all root/first-level source bags, the profile error in the omitted
fringes is bounded by their total up-flow capacity. -/
theorem wireFlowLayer_low_frontier_error_sum_le_up {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => b.l ≤ 1 ∧ b.l + 1 < d),
      ∑ i ∈ ({0, 65} : Finset Nat),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) ≤
      ∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => b.l ≤ 1 ∧ b.l + 1 < d),
        (F.up source.l t : Real) := by
  classical
  apply Finset.sum_le_sum
  intro source hsource
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  simpa [wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using
    (senderOutgoing_fringe_profile_error_sum_le_up
      (wireSets F t source)
      (fun w => predicate (X F nets input (t + 1) w))
      (F.up source.l t) (F.down source.l t) (q source) (frac source)
      hsize (F.hup_even source.l t ht) (hfrac0 source) (hfrac1 source))

/-- Across all top-frontier source bags, the profile error in the omitted
middle pieces is bounded by their aggregate down-flow capacity. -/
theorem wireFlowLayer_high_frontier_error_sum_le_down {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) ≤
      ∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
        (64 * F.down source.l t : Real) := by
  classical
  apply Finset.sum_le_sum
  intro source hsource
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  simpa [wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using
    (senderOutgoing_middle_profile_error_sum_le_down
      (wireSets F t source)
      (fun w => predicate (X F nets input (t + 1) w))
      (F.up source.l t) (F.down source.l t) (q source) (frac source)
      hsize (F.hup_even source.l t ht) (hfrac0 source) (hfrac1 source))

/-- The root's omitted fringe error vanishes: its up-flow is identically zero. -/
theorem wireFlowLayer_root_fringe_error_eq_zero {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hroot : source.l = 0)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1) :
    (∑ i ∈ ({0, 65} : Finset Nat),
      |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) = 0 := by
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  have hup : F.up source.l t = 0 := by
    rw [hroot]
    exact F.hup_root t ht
  have hle := senderOutgoing_fringe_profile_error_sum_le_up
    (wireSets F t source) (fun w => predicate (X F nets input (t + 1) w))
    (F.up source.l t) (F.down source.l t) (q source) (frac source)
    hsize (F.hup_even source.l t ht) hfrac0 hfrac1
  have hnonneg : 0 ≤ ∑ i ∈ ({0, 65} : Finset Nat),
      |(trueCountOn (senderOutgoingPiece (wireSets F t source)
          (F.up source.l t) (F.down source.l t) i)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
        profileIntervalMean (wireSets F t source).card (q source) (frac source)
          (senderRankCut (F.up source.l t) (F.down source.l t) i)
          (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hle0 := by simpa [hup] using hle
  have hnonneg0 := by simpa [hup] using hnonneg
  have hsum := le_antisymm hle0 hnonneg0
  simpa [hup, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using hsum

/-- The bottom leaf's omitted middle error vanishes: it sends no down-flow. -/
theorem wireFlowLayer_leaf_middle_error_eq_zero {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (source : KBag 64 d) (hleaf : source.l = d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : 0 ≤ frac source) (hfrac1 : frac source ≤ 1) :
    (∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) = 0 := by
  have hsize : (wireSets F t source).card =
      F.up source.l t + 64 * F.down source.l t := by
    rw [wireSets_card _ (Nat.le_of_lt ht)]
    exact F.hsplit source.l t source.hl ht
  have hdown : F.down source.l t = 0 := by
    rw [hleaf]
    exact F.hdown_leaf t ht
  have hle := senderOutgoing_middle_profile_error_sum_le_down
    (wireSets F t source) (fun w => predicate (X F nets input (t + 1) w))
    (F.up source.l t) (F.down source.l t) (q source) (frac source)
    hsize (F.hup_even source.l t ht) hfrac0 hfrac1
  have hnonneg : 0 ≤ ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
      |(trueCountOn (senderOutgoingPiece (wireSets F t source)
          (F.up source.l t) (F.down source.l t) i)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
        profileIntervalMean (wireSets F t source).card (q source) (frac source)
          (senderRankCut (F.up source.l t) (F.down source.l t) i)
          (senderRankCut (F.up source.l t) (F.down source.l t) (i + 1))| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hle0 := by simpa [hdown] using hle
  have hnonneg0 := by simpa [hdown] using hnonneg
  have hsum := le_antisymm hle0 hnonneg0
  simpa [hdown, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
    wireFlowLayerSenderPieceMean] using hsum

private theorem omega7_lt_d_sub_one (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht : t < tf7 d) : omega7 d t < d - 1 := by
  by_cases ht0 : t = 0
  · simp [omega7, ht0]
    omega
  · by_cases ht1 : t = 1
    · simp [omega7, ht0, ht1]
      omega
    · have ht2 : 2 ≤ t := by omega
      have hbound := omega7_bounds d t ht2
      unfold tf7 at ht
      omega

/-- In the §7 schedule, level d−1 is already outside the active band at all
ordinary stages, so it sends no down-flow to the leaves. -/
theorem flowDown7_d_sub_one_eq_zero (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht : t < tf7 d) : flowDown7 d hd (d - 1) t = 0 := by
  by_cases ht0 : t = 0
  · simp [flowDown7, ht0]
    omega
  · by_cases ht1 : t = 1
    · simp [flowDown7, ht0, ht1]
      omega
    · have ht2 : 2 ≤ t := by omega
      have hnot : ¬Active d (d - 1) t := by
        intro ha
        have hle := ha.2.2.1
        have hstrict := omega7_lt_d_sub_one d hd t ht
        omega
      have hrat := flowDown_inactive d hnot
      have hcast := cast_flowDown7 d hd (d - 1) t ht2 ht
      have hzero : ((flowDown7 d hd (d - 1) t : Nat) : Rat) = 0 := by
        rw [hcast, hrat]
      exact_mod_cast hzero

/-- The level-1 parent send at an ordinary stage is at most its capacity
divided by `4096^2`; this is the geometric envelope for the low-frontier tail. -/
theorem flowUp7_level_one_le_capacity_scale (d : Nat) (hd : 7 ≤ d)
    (t : Nat) (ht2 : 2 ≤ t) (ht : t < tf7 d) :
    ((flowUp7 d hd 1 t : Nat) : Rat) ≤ capacity d 1 t / (4096 : Rat) ^ 2 := by
  have hcast := cast_flowUp7 d hd 1 t ht2 ht
  by_cases ha : Active d 1 t
  · have hω := omega7_bounds d t ht2
    have hneω : 1 ≠ omega7 d t := by omega
    by_cases hα : 1 = alpha7 d t
    · by_cases hstep : alpha7 d t < alpha7 d (t + 1)
      · have hup := flowUp_top_desc d ha hα hstep
        rw [hcast.1, hup]
        exact div_nonneg (capacity_nonneg d 1 t) (by positivity)
      · have hup := flowUp_top_rise d ha hα hstep
        rw [hcast.1, hup]
        have hratio : (1 / 64 : Rat) * capacity d 1 t / (4096 * 64) =
            capacity d 1 t / (4096 : Rat) ^ 2 := by
          field_simp
          ring
        rw [hratio]
    · have hup := flowUp_mid d ha hα (fun heq => (hneω heq).elim)
      rw [hcast.1, hup]
      have hcoeff : (4095 : Rat) / capacityRatio ≤
          1 / (4096 : Rat) ^ 2 := by
        rw [capacityRatio_eq]
        norm_num
      have hcap := capacity_nonneg d 1 t
      calc
        (4095 : Rat) * capacity d 1 t / capacityRatio =
            ((4095 : Rat) / capacityRatio) * capacity d 1 t := by ring
        _ ≤ (1 / (4096 : Rat) ^ 2) * capacity d 1 t :=
          mul_le_mul_of_nonneg_right hcoeff hcap
        _ = capacity d 1 t / (4096 : Rat) ^ 2 := by ring
  · have hup := flowUp_inactive d ha
    rw [hcast.1, hup]
    exact div_nonneg (capacity_nonneg d 1 t) (by positivity)

private theorem capacity_level_one_geometric_sum (d n : Nat) :
    (∑ k ∈ range n, capacity d 1 (k + 1)) =
      (64 / 63 : Rat) * (capacity d 1 1 - capacity d 1 (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := capacity_succ_stage d 1 (n + 1)
      rw [hstep]
      ring

theorem wireFlowLayer_level_one_bags_card_le_64 (d : Nat) :
    ((Finset.univ : Finset (KBag 64 d)).filter (fun b => b.l = 1)).card ≤ 64 := by
  calc
    _ ≤ (Finset.range 64).card := by
      apply Finset.card_le_card_of_injOn
        (fun b : KBag 64 d => b.x)
      · intro b hb
        have hl := (Finset.mem_filter.mp hb).2
        simp only [Finset.mem_range]
        simpa [hl] using b.hx
      · intro a ha b hb hab
        apply KBag.ext
        · have ha' := (Finset.mem_filter.mp ha).2
          have hb' := (Finset.mem_filter.mp hb).2
          omega
        · exact hab
    _ = 64 := by simp

/-- Summed over every ordinary stage starting at t=1, the level-1 up-flow is
bounded by a geometric tail with ratio 1/64. -/
theorem flowUp7_level_one_time_sum_le (d : Nat) (hd : 7 ≤ d) :
    (∑ k ∈ range (tf7 d - 1),
      (flowUp7 d hd 1 (k + 1) : Rat)) ≤
      (64 / 63 : Rat) * (capacity d 1 1 / (4096 : Rat) ^ 2) := by
  have hterm (k : Nat) (hk : k ∈ range (tf7 d - 1)) :
      (flowUp7 d hd 1 (k + 1) : Rat) ≤
        capacity d 1 (k + 1) / (4096 : Rat) ^ 2 := by
    have ht : k + 1 < tf7 d := by
      have hk' := mem_range.mp hk
      unfold tf7 at *
      omega
    by_cases ht1 : k + 1 = 1
    · have hspecial : flowUp7 d hd 1 1 = 64 ^ (d - 5) := by
        simp [flowUp7]
      have hcap := capacity_eq_pow d 1 1 (d - 1) (by omega)
      rw [ht1, hspecial, hcap]
      have hratio : ((64 ^ (d - 5) : Nat) : Rat) =
          (64 : Rat) ^ (d - 1) / (4096 : Rat) ^ 2 := by
        have hexp : d - 1 = (d - 5) + 4 := by omega
        rw [hexp, pow_add]
        norm_num
      rw [hratio, Nat.cast_pow]
      norm_num
    · have ht2 : 2 ≤ k + 1 := by omega
      exact flowUp7_level_one_le_capacity_scale d hd (k + 1) ht2 ht
  calc
    _ ≤ ∑ k ∈ range (tf7 d - 1),
        capacity d 1 (k + 1) / (4096 : Rat) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact hterm k hk
    _ = (∑ k ∈ range (tf7 d - 1), capacity d 1 (k + 1)) /
          (4096 : Rat) ^ 2 := by
      calc
        _ = ∑ k ∈ range (tf7 d - 1),
            capacity d 1 (k + 1) * ((4096 : Rat) ^ 2)⁻¹ := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = (∑ k ∈ range (tf7 d - 1), capacity d 1 (k + 1)) *
            ((4096 : Rat) ^ 2)⁻¹ := by rw [Finset.sum_mul]
        _ = _ := by ring
    _ ≤ (64 / 63 : Rat) * capacity d 1 1 / (4096 : Rat) ^ 2 := by
      have hgeom := capacity_level_one_geometric_sum d (tf7 d - 1)
      rw [hgeom]
      have htfpos : 1 ≤ tf7 d := by unfold tf7; omega
      rw [Nat.sub_add_cancel htfpos]
      have hcap := capacity_nonneg d 1 (tf7 d)
      have hbound : (64 / 63 : Rat) *
          (capacity d 1 1 - capacity d 1 (tf7 d)) ≤
          (64 / 63 : Rat) * capacity d 1 1 := by
        nlinarith [hcap]
      have hden : 0 < (4096 : Rat) ^ 2 := by positivity
      rw [div_le_div_iff_of_pos_right hden]
      field_simp
      nlinarith [hbound]
    _ = (64 / 63 : Rat) *
        (capacity d 1 1 / (4096 : Rat) ^ 2) := by ring

/-- The level-1 up-flow capacity, summed over all its bags and ordinary
stages, is at most 64 copies of the per-bag geometric tail. -/
theorem flowUp7_level_one_aggregate_time_sum_le (d : Nat) (hd : 7 ≤ d) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => b.l = 1),
      ∑ k ∈ range (tf7 d - 1),
        (flowUp7 d hd source.l (k + 1) : Rat)) ≤
      64 * ((64 / 63 : Rat) *
        (capacity d 1 1 / (4096 : Rat) ^ 2)) := by
  let sources := (Finset.univ : Finset (KBag 64 d)).filter (fun b => b.l = 1)
  have hlevel (source : KBag 64 d) (hs : source ∈ sources) : source.l = 1 := by
    exact (Finset.mem_filter.mp hs).2
  have hrewrite :
      (∑ source ∈ sources,
        ∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd source.l (k + 1) : Rat)) =
      (sources.card : Rat) *
        (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) := by
    calc
      _ = ∑ source ∈ sources,
          (∑ k ∈ range (tf7 d - 1),
            (flowUp7 d hd 1 (k + 1) : Rat)) := by
        apply Finset.sum_congr rfl
        intro source hs
        apply Finset.sum_congr rfl
        intro k hk
        rw [hlevel source hs]
      _ = (sources.card : Rat) *
          (∑ k ∈ range (tf7 d - 1),
            (flowUp7 d hd 1 (k + 1) : Rat)) := by
        simp [Finset.sum_const]
  have hcard : (sources.card : Rat) ≤ 64 := by
    have h := wireFlowLayer_level_one_bags_card_le_64 d
    exact_mod_cast h
  have htime := flowUp7_level_one_time_sum_le d hd
  have htime_nonneg : 0 ≤
      (∑ k ∈ range (tf7 d - 1),
        (flowUp7 d hd 1 (k + 1) : Rat)) := by
    apply Finset.sum_nonneg
    intro k hk
    positivity
  rw [hrewrite]
  calc
    (sources.card : Rat) *
        (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) ≤
        64 * (∑ k ∈ range (tf7 d - 1),
          (flowUp7 d hd 1 (k + 1) : Rat)) :=
      mul_le_mul_of_nonneg_right hcard htime_nonneg
    _ ≤ 64 * ((64 / 63 : Rat) *
          (capacity d 1 1 / (4096 : Rat) ^ 2)) :=
      mul_le_mul_of_nonneg_left htime (by norm_num)

/-- All high-frontier omitted-middle error vanishes in the actual §7 flow:
level d−1 is inactive, and level d has zero down-flow by construction. -/
theorem wireFlowLayer_high_frontier_error_sum_eq_zero {d : Nat}
    (hd : 7 ≤ d) (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf7 d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1) :
    (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError (flowSizes7 d hd) nets input t
          predicate q frac source i|) = 0 := by
  let F := flowSizes7 d hd
  have hle := wireFlowLayer_high_frontier_error_sum_le_down
    F nets input t ht predicate q frac hfrac0 hfrac1
  have hdown (source : KBag 64 d)
      (hsource : source ∈ (Finset.univ : Finset (KBag 64 d)).filter
        (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1)) : F.down source.l t = 0 := by
    have hmem := (Finset.mem_filter.mp hsource).2
    have hlevel : source.l = d - 1 ∨ source.l = d := by
      have hsourced : source.l ≤ d := source.hl
      omega
    change flowDown7 d hd source.l t = 0
    rcases hlevel with hlevel | hlevel
    · rw [hlevel]
      exact flowDown7_d_sub_one_eq_zero d hd t ht
    · rw [hlevel]
      exact flowSizes7_down_leaf d hd t ht
  have hrhs : (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 2 ≤ b.l ∧ d ≤ b.l + 1),
      (64 * F.down source.l t : Real)) = 0 := by
    apply Finset.sum_eq_zero
    intro source hsource
    rw [hdown source hsource]
    simp
  have hnonneg : 0 ≤ (∑ source ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b : KBag 64 d => 2 ≤ b.l ∧ d ≤ b.l + 1),
      ∑ i ∈ (range 66).filter (fun i => 1 ≤ i ∧ i ≤ 64),
        |wireFlowLayerSenderPieceError F nets input t predicate q frac source i|) := by
    apply Finset.sum_nonneg
    intro source hsource
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hsum := le_antisymm (by simpa [hrhs] using hle) hnonneg
  simpa [F] using hsum

/-- Sum of the selected ideal means for an active receiver. -/
noncomputable def wireFlowReceiverSelectedIdealMean {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) (receiver : KBag 64 d) : Real :=
  if hchild : receiver.l < d then
    ∑ source : Fin 65,
      ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
        wireFlowLayerSenderPieceMean F t q frac
          (wireFlowReceiverSource receiver hchild source) i
  else 0

set_option maxHeartbeats 1000000
/-- The signed all-bag routed discrepancy at an active receiver equals its
actual register threshold count minus the selected ideal means. -/
theorem wireFlowLayer_receiver_signed_error_eq_register {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real) :
    (∑ source : KBag 64 d,
      ∑ i ∈ wireFlowLayerSelection receiver source,
        wireFlowLayerSenderPieceError F nets input t predicate q frac source i) =
      (trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) -
        (wireFlowReceiverSelectedIdealMean F t q frac receiver) := by
  let pieceCount (source : KBag 64 d) (i : Nat) : Real :=
    wireFlowLayerSenderPieceCount F nets input t predicate source i
  let pieceMean (source : KBag 64 d) (i : Nat) : Real :=
    wireFlowLayerSenderPieceMean F t q frac source i
  have hcountsNat := wireFlowReceiver_selected_count_eq_register
    F nets input t ht receiver hb hchild predicate
  have hcounts :
      (∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
          pieceCount (wireFlowReceiverSource receiver hchild source) i) =
        (trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) := by
    simpa only [pieceCount, Nat.cast_sum] using
      congrArg (fun n : Nat => (n : Real)) hcountsNat
  have hpieceSum := wireFlowLayerSelection_receiverSum_eq receiver hb hchild
    (fun source i => pieceCount source i - pieceMean source i)
  calc
    _ = ∑ source : Fin 65,
        ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
          (pieceCount (wireFlowReceiverSource receiver hchild source) i -
            pieceMean (wireFlowReceiverSource receiver hchild source) i) := by
      simpa [wireFlowLayerSenderPieceError, pieceCount, pieceMean] using hpieceSum
    _ = (∑ source : Fin 65,
          ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            pieceCount (wireFlowReceiverSource receiver hchild source) i) -
        ∑ source : Fin 65,
          ∑ i ∈ receiverOutgoingSelection (receiver.x % 64) source,
            pieceMean (wireFlowReceiverSource receiver hchild source) i := by
      simp_rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [hcounts]
      simp only [pieceMean, wireFlowReceiverSelectedIdealMean, dif_pos hchild]
set_option maxHeartbeats 200000

/-- The selected ideal means form a valid Boolean threshold target for the
receiver: they lie between zero and the receiver register capacity. -/
theorem wireFlowReceiverSelectedIdealMean_bounds {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource receiver hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource receiver hchild source) ≤ 1) :
    0 ≤ wireFlowReceiverSelectedIdealMean F t q frac receiver ∧
      wireFlowReceiverSelectedIdealMean F t q frac receiver ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
  classical
  let sourceBag := wireFlowReceiverSource receiver hchild
  let selection := receiverOutgoingSelection (receiver.x % 64)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize (source : Fin 65) :
      (wireSets F t (sourceBag source)).card =
        F.up (sourceBag source).l t + 64 * F.down (sourceBag source).l t := by
    rw [hinv.1]
    exact F.hsplit (sourceBag source).l t (sourceBag source).hl ht
  have hpieceCard (source : Fin 65) (i : Nat) (hi : i < 66) :
      (senderOutgoingPiece (wireSets F t (sourceBag source))
        (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card =
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i := by
    rw [senderOutgoingPiece_eq_blockOf _ _ _ (hsize source)
      (F.hup_even _ _ ht) i hi]
    apply blockOf_card
    rw [hsize source]
    exact senderRankCut_le _ _ _
  have hcountNat := wireFlowReceiver_selected_count_eq_register
    F nets input t ht receiver hb hchild (fun _ => true)
  have hcountCard :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        (senderOutgoingPiece (wireSets F t (sourceBag source))
          (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card) =
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
    simpa [trueCountOn_eq_card_filter] using hcountNat
  have hwidthNat :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i)) =
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card := by
    calc
      _ = ∑ source : Fin 65, ∑ i ∈ selection source,
          (senderOutgoingPiece (wireSets F t (sourceBag source))
            (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i).card := by
        apply Finset.sum_congr rfl
        intro source _
        apply Finset.sum_congr rfl
        intro i hi
        symm
        exact hpieceCard source i (by
          have hlt := receiverOutgoingSelection_subset (receiver.x % 64)
            (Nat.mod_lt _ (by omega)) source hi
          exact Finset.mem_range.mp hlt)
      _ = _ := hcountCard
  have hwidthReal :
      (∑ source : Fin 65, ∑ i ∈ selection source,
        ((senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1) -
        senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i : Nat) : Real)) =
        (((execPlacement F nets input (t + 1) (by omega)).regs receiver).card : Real) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun n : Nat => (n : Real)) hwidthNat
  have hpieceBounds (source : Fin 65) (i : Nat) (hi : i ∈ selection source) :
      0 ≤ wireFlowLayerSenderPieceMean F t q frac (sourceBag source) i ∧
        wireFlowLayerSenderPieceMean F t q frac (sourceBag source) i ≤
          ((senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) (i + 1) -
          senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) i : Nat) : Real) := by
    have hmono := senderRankCut_mono
      (F.up (sourceBag source).l t) (F.down (sourceBag source).l t)
    have hcut := hmono (Nat.le_succ i)
    have hcutEnd := senderRankCut_le (F.up (sourceBag source).l t)
      (F.down (sourceBag source).l t) (i + 1)
    rw [← hsize source] at hcutEnd
    simpa [sourceBag, wireFlowLayerSenderPieceMean] using profileIntervalMean_bounds _ (q (sourceBag source))
      (senderRankCut (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) i)
      (senderRankCut (F.up (sourceBag source).l t) (F.down (sourceBag source).l t) (i + 1))
      (frac (sourceBag source)) hcut hcutEnd (hfrac0 source) (hfrac1 source)
  constructor
  · unfold wireFlowReceiverSelectedIdealMean
    rw [dif_pos hchild]
    apply Finset.sum_nonneg
    intro source _
    apply Finset.sum_nonneg
    intro i hi
    exact (hpieceBounds source i hi).1
  · unfold wireFlowReceiverSelectedIdealMean
    rw [dif_pos hchild]
    calc
      _ ≤ ∑ source : Fin 65, ∑ i ∈ selection source,
          ((senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) (i + 1) -
          senderRankCut (F.up (sourceBag source).l t)
            (F.down (sourceBag source).l t) i : Nat) : Real) := by
        apply Finset.sum_le_sum
        intro source _
        apply Finset.sum_le_sum
        intro i hi
        exact (hpieceBounds source i hi).2
      _ = _ := hwidthReal

/-- The receiver's selected ideal mean can be installed as a legal next-stage
`q + frac` target, including the zero-capacity endpoint case. -/
theorem wireFlowReceiverSelectedIdealMean_has_code {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hb : 1 ≤ receiver.l) (hchild : receiver.l < d)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource receiver hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource receiver hchild source) ≤ 1) :
    ∃ nextQ : Nat, nextQ ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card ∧
      ∃ nextFrac : Real, 0 ≤ nextFrac ∧ nextFrac ≤ 1 ∧
        (nextQ : Real) + nextFrac =
          wireFlowReceiverSelectedIdealMean F t q frac receiver ∧
        (nextQ = ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card →
          nextFrac = 0) := by
  let m := ((execPlacement F nets input (t + 1) (by omega)).regs receiver).card
  let μ := wireFlowReceiverSelectedIdealMean F t q frac receiver
  have hbnds := wireFlowReceiverSelectedIdealMean_bounds F nets input t ht
    receiver hb hchild q frac hfrac0 hfrac1
  by_cases hm : m = 0
  · have hμ : μ = 0 := by
      have hμm : μ ≤ 0 := by simpa [μ, m, hm] using hbnds.2
      exact le_antisymm hμm (by simpa [μ] using hbnds.1)
    refine ⟨0, by simp [m, hm], 0, by norm_num, by norm_num, ?_, ?_⟩
    · simpa [μ] using hμ.symm
    · intro _
      rfl
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    obtain ⟨nextQ, hq, nextFrac, hf0, hf1, hmean⟩ :=
      realTarget_has_integer_fraction m μ hmpos (by simpa [μ] using hbnds.1)
        (by simpa [m, μ] using hbnds.2)
    refine ⟨nextQ, by omega, nextFrac, hf0, hf1, ?_, ?_⟩
    · simpa [μ] using hmean
    · intro htop
      omega

/-- If every source bag's real threshold target is monotone between two value
thresholds, then the receiver's selected ideal target is monotone as well.
Thus the port rule preserves coherence of the target profile. -/
theorem wireFlowReceiverSelectedIdealMean_mono {d tf : Nat}
    (F : FlowSizes d tf) (t : Nat) (ht : t < tf)
    (receiver : KBag 64 d) (hchild : receiver.l < d)
    (q : Nat → KBag 64 d → Nat) (frac : Nat → KBag 64 d → Real)
    (θ₁ θ₂ : Nat)
    (hfrac₁0 : ∀ source : Fin 65,
      0 ≤ frac θ₁ (wireFlowReceiverSource receiver hchild source))
    (hfrac₁1 : ∀ source : Fin 65,
      frac θ₁ (wireFlowReceiverSource receiver hchild source) ≤ 1)
    (hfrac₂0 : ∀ source : Fin 65,
      0 ≤ frac θ₂ (wireFlowReceiverSource receiver hchild source))
    (hfrac₂1 : ∀ source : Fin 65,
      frac θ₂ (wireFlowReceiverSource receiver hchild source) ≤ 1)
    (hmean : ∀ source : Fin 65,
      (q θ₁ (wireFlowReceiverSource receiver hchild source) : Real) +
          frac θ₁ (wireFlowReceiverSource receiver hchild source) ≤
        (q θ₂ (wireFlowReceiverSource receiver hchild source) : Real) +
          frac θ₂ (wireFlowReceiverSource receiver hchild source)) :
    wireFlowReceiverSelectedIdealMean F t (q θ₁) (frac θ₁) receiver ≤
      wireFlowReceiverSelectedIdealMean F t (q θ₂) (frac θ₂) receiver := by
  classical
  let sourceBag := wireFlowReceiverSource receiver hchild
  let selection := receiverOutgoingSelection (receiver.x % 64)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize (source : Fin 65) :
      (wireSets F t (sourceBag source)).card =
        F.up (sourceBag source).l t + 64 * F.down (sourceBag source).l t := by
    rw [hinv.1]
    exact F.hsplit (sourceBag source).l t (sourceBag source).hl ht
  have hpiece (source : Fin 65) (i : Nat) :
      wireFlowLayerSenderPieceMean F t (q θ₁) (frac θ₁) (sourceBag source) i ≤
        wireFlowLayerSenderPieceMean F t (q θ₂) (frac θ₂) (sourceBag source) i := by
    have hcuts := senderRankCut_mono
      (F.up (sourceBag source).l t) (F.down (sourceBag source).l t)
    have hcut := hcuts (Nat.le_succ i)
    have hcutEnd := senderRankCut_le (F.up (sourceBag source).l t)
      (F.down (sourceBag source).l t) (i + 1)
    rw [← hsize source] at hcutEnd
    simpa [sourceBag, wireFlowLayerSenderPieceMean] using
      (profileIntervalMean_mono_mean (wireSets F t (sourceBag source)).card
        (q θ₁ (sourceBag source)) (q θ₂ (sourceBag source))
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) i)
        (senderRankCut (F.up (sourceBag source).l t)
          (F.down (sourceBag source).l t) (i + 1))
        (frac θ₁ (sourceBag source)) (frac θ₂ (sourceBag source))
        hcut hcutEnd (hfrac₁0 source) (hfrac₁1 source)
        (hfrac₂0 source) (hfrac₂1 source) (hmean source))
  unfold wireFlowReceiverSelectedIdealMean
  simp only [dif_pos hchild]
  apply Finset.sum_le_sum
  intro source _
  apply Finset.sum_le_sum
  intro i _
  exact hpiece source i

/-- Summed over every interior receiver of a WireFlow layer, the actual
register discrepancy from its selected ideal port mean is bounded by the
coarse count error of each sender, once. This is the concrete layerwise
incidence estimate needed by the bag-mean recurrence. The selected means form
valid monotone receiver targets under the corresponding source-profile
hypotheses; contraction of the resulting profile under merge/deal is still
separate. -/
theorem wireFlowLayer_register_error_sum_le_source_count_error {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Fin (64 ^ d) → Bool) (q : KBag 64 d → Nat)
    (frac : KBag 64 d → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source, q source = (wireSets F t source).card → frac source = 0) :
    (∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      |(trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          predicate : Real) -
        wireFlowReceiverSelectedIdealMean F t q frac receiver|) ≤
      ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  classical
  let active : Finset (KBag 64 d) :=
    (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d)
  let v : KBag 64 d → Fin (64 ^ d) → Bool :=
    fun _ w => predicate (X F nets input (t + 1) w)
  have hinv := wireSets_inv F t (Nat.le_of_lt ht)
  have hsize : ∀ source,
      (wireSets F t source).card = F.up source.l t + 64 * F.down source.l t := by
    intro source
    rw [hinv.1 source]
    exact F.hsplit source.l t source.hl ht
  have hu : ∀ source : KBag 64 d, 2 ∣ F.up source.l t := by
    intro source
    exact F.hup_even source.l t ht
  have hbound := wireFlowLayer_profile_error_sum_le
    (fun source => wireSets F t source) v (fun source => F.up source.l t)
    (fun source => F.down source.l t) q frac hsize hu hsorted hq hfrac0 hfrac1 hendpoint
  have hsubset : active ⊆ Finset.univ := Finset.filter_subset _ _
  calc
    (∑ receiver ∈ active,
        |(trueCountOn
            ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
            predicate : Real) -
          wireFlowReceiverSelectedIdealMean F t q frac receiver|) =
      ∑ receiver ∈ active,
        |∑ source : KBag 64 d,
          ∑ i ∈ wireFlowLayerSelection receiver source,
            wireFlowLayerSenderPieceError F nets input t predicate q frac source i| := by
      apply Finset.sum_congr rfl
      intro receiver hreceiver
      have hactive := (Finset.mem_filter.mp hreceiver).2
      rw [← wireFlowLayer_receiver_signed_error_eq_register F nets input t ht
        receiver hactive.1 hactive.2 predicate q frac]
    _ ≤ ∑ receiver : KBag 64 d,
        |∑ source : KBag 64 d,
          ∑ i ∈ wireFlowLayerSelection receiver source,
            wireFlowLayerSenderPieceError F nets input t predicate q frac source i| :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro receiver _ _
        exact abs_nonneg _)
    _ ≤ ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
      simpa [v, wireFlowLayerSenderPieceError, wireFlowLayerSenderPieceCount,
        wireFlowLayerSenderPieceMean, profileIntervalMean] using hbound

/-- The no-amplification estimate holds simultaneously for any finite family
of value thresholds. Summing over all active receivers and thresholds charges
each source bag's coarse error once per threshold, with no factor for the
number of receiver levels or routed ports. -/
theorem wireFlowLayer_register_error_sum_le_source_count_error_multi
    {d tf : Nat} {Θ : Type} [Fintype Θ] [DecidableEq Θ]
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (predicate : Θ → Fin (64 ^ d) → Bool)
    (q : Θ → KBag 64 d → Nat) (frac : Θ → KBag 64 d → Real)
    (hsorted : ∀ θ source, Monotone
      ((fun w => predicate θ (X F nets input (t + 1) w)) ∘
        (wireSets F t source).orderEmbOfFin rfl))
    (hq : ∀ θ source, q θ source ≤ (wireSets F t source).card)
    (hfrac0 : ∀ θ source, 0 ≤ frac θ source)
    (hfrac1 : ∀ θ source, frac θ source ≤ 1)
    (hendpoint : ∀ θ source,
      q θ source = (wireSets F t source).card → frac θ source = 0) :
    (∑ θ : Θ, ∑ receiver ∈ (Finset.univ : Finset (KBag 64 d)).filter
      (fun b => 1 ≤ b.l ∧ b.l < d),
      |(trueCountOn
          ((execPlacement F nets input (t + 1) (by omega)).regs receiver)
          (predicate θ) : Real) -
        wireFlowReceiverSelectedIdealMean F t (q θ) (frac θ) receiver|) ≤
      ∑ θ : Θ, ∑ source : KBag 64 d,
        |(trueCountOn (wireSets F t source)
          (fun w => predicate θ (X F nets input (t + 1) w)) : Real) -
          (q θ source + frac θ source)| := by
  classical
  apply Finset.sum_le_sum
  intro θ _
  exact wireFlowLayer_register_error_sum_le_source_count_error
    F nets input t ht (predicate θ) (q θ) (frac θ)
    (hsorted θ) (hq θ) (hfrac0 θ) (hfrac1 θ) (hendpoint θ)

/-- The source-profile error bound applies directly to the actual receiver
register: the selected parent/child piece counts are exactly its Boolean
threshold count. This packages the source-side discrepancy at the receiver
boundary; matching the selected profile means to a common downstream target
is still a separate recurrence obligation. -/
theorem wireFlowReceiver_register_count_error_actual {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : Fin 65 → Nat) (frac : Fin 65 → Real)
    (hsorted : ∀ source, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source, q source ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
    (hendpoint : ∀ source,
      q source = (wireSets F t (wireFlowReceiverSource b hchild source)).card →
        frac source = 0) :
    |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
        predicate : Real) -
      ∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q source) (frac source)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1))| ≤
      ∑ source : Fin 65,
        |(trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
          (fun w => predicate (X F nets input (t + 1) w)) : Real) -
          (q source + frac source)| := by
  have hcount := (wireFlowReceiver_selected_count_eq_register
    F nets input t ht b hb hchild predicate).symm
  calc
    |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
        predicate : Real) - _| =
      |((∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
          trueCountOn
            (senderOutgoingPiece
              (wireSets F t (wireFlowReceiverSource b hchild source))
              (F.up (wireFlowReceiverSource b hchild source).l t)
              (F.down (wireFlowReceiverSource b hchild source).l t) i)
            (fun w => predicate (X F nets input (t + 1) w)) : Nat) : Real) - _| := by
        rw [hcount]
    _ ≤ _ := by
      simpa only [Nat.cast_sum] using
        (wireFlowReceiver_count_error_actual F nets input t ht b hb hchild predicate
          q frac hsorted hq hfrac0 hfrac1 hendpoint)

/-- The receiver discrepancy is directly against a valid re-encoded next-stage
target, with the same source-error charge as the selected-mean interface. -/
theorem wireFlowReceiver_register_count_error_reencoded {d tf : Nat}
    (F : FlowSizes d tf)
    (nets : Nat → (b : KBag 64 d) → (n : Nat) → ComparatorNetwork n)
    (input : Equiv.Perm (Fin (64 ^ d))) (t : Nat) (ht : t < tf)
    (b : KBag 64 d) (hb : 1 ≤ b.l) (hchild : b.l < d)
    (predicate : Fin (64 ^ d) → Bool)
    (q : KBag 64 d → Nat) (frac : KBag 64 d → Real)
    (hsorted : ∀ source : Fin 65, Monotone
      ((fun w => predicate (X F nets input (t + 1) w)) ∘
        (wireSets F t (wireFlowReceiverSource b hchild source)).orderEmbOfFin rfl))
    (hq : ∀ source : Fin 65, q (wireFlowReceiverSource b hchild source) ≤
      (wireSets F t (wireFlowReceiverSource b hchild source)).card)
    (hfrac0 : ∀ source : Fin 65,
      0 ≤ frac (wireFlowReceiverSource b hchild source))
    (hfrac1 : ∀ source : Fin 65,
      frac (wireFlowReceiverSource b hchild source) ≤ 1)
    (hendpoint : ∀ source : Fin 65,
      q (wireFlowReceiverSource b hchild source) =
        (wireSets F t (wireFlowReceiverSource b hchild source)).card →
      frac (wireFlowReceiverSource b hchild source) = 0) :
    ∃ nextQ : Nat, nextQ ≤
        ((execPlacement F nets input (t + 1) (by omega)).regs b).card ∧
      ∃ nextFrac : Real, 0 ≤ nextFrac ∧ nextFrac ≤ 1 ∧
        (nextQ : Real) + nextFrac =
          wireFlowReceiverSelectedIdealMean F t q frac b ∧
        (nextQ = ((execPlacement F nets input (t + 1) (by omega)).regs b).card →
          nextFrac = 0) ∧
        |(trueCountOn ((execPlacement F nets input (t + 1) (by omega)).regs b)
            predicate : Real) - ((nextQ : Real) + nextFrac)| ≤
          ∑ source : Fin 65,
            |((trueCountOn (wireSets F t (wireFlowReceiverSource b hchild source))
                (fun w => predicate (X F nets input (t + 1) w)) : Nat) : Real) -
              ((q (wireFlowReceiverSource b hchild source) : Real) +
                frac (wireFlowReceiverSource b hchild source))| := by
  rcases wireFlowReceiverSelectedIdealMean_has_code F nets input t ht b hb hchild
      q frac hfrac0 hfrac1 with ⟨nextQ, hnextQ, nextFrac, hnextFrac0,
        hnextFrac1, hcode, hendpointNext⟩
  have hmean :
      (∑ source : Fin 65, ∑ i ∈ receiverOutgoingSelection (b.x % 64) source,
        profileIntervalMean
          (wireSets F t (wireFlowReceiverSource b hchild source)).card
          (q (wireFlowReceiverSource b hchild source))
          (frac (wireFlowReceiverSource b hchild source))
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) i)
          (senderRankCut (F.up (wireFlowReceiverSource b hchild source).l t)
            (F.down (wireFlowReceiverSource b hchild source).l t) (i + 1))) =
        wireFlowReceiverSelectedIdealMean F t q frac b := by
    simp [wireFlowReceiverSelectedIdealMean, wireFlowLayerSenderPieceMean, hchild]
  have herror := wireFlowReceiver_register_count_error_actual F nets input t ht b hb hchild
    predicate (fun source => q (wireFlowReceiverSource b hchild source))
    (fun source => frac (wireFlowReceiverSource b hchild source)) hsorted hq hfrac0 hfrac1
    hendpoint
  rw [hmean] at herror
  refine ⟨nextQ, hnextQ, nextFrac, hnextFrac0, hnextFrac1, hcode, hendpointNext, ?_⟩
  rw [hcode]
  simpa using herror

theorem sortedPackets_intervalPartition_L1_exact {c m p q : Nat} (frac : Real)
    (V : Fin c → Fin m → Bool) (hV : ∀ i, Monotone (V i))
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hcutBound : ∀ i, cuts i ≤ m)
    (hend : cuts p = m) (hq : q < m) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
          V packet ⟨cuts i + j.val, by
            have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
              _ = cuts (i + 1) := hsum
              _ ≤ m := hcutBound (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|) =
      ∑ packet : Fin c, |(boolTrueCount (V packet) : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro packet _
  have hpacket (i : Nat) (hi : i < p) :
      boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
        V packet ⟨cuts i + j.val, by
          have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
          have hsum := Nat.add_sub_of_le hab
          calc
            cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
            _ = cuts (i + 1) := hsum
            _ ≤ m := hcutBound (i + 1)⟩) =
        profileInterval m (boolTrueCount (V packet)) (cuts i) (cuts (i + 1)) := by
    apply sortedBool_rankInterval_trueCount (V packet) (hV packet)
    · exact hcuts (Nat.le_succ i)
    · exact hcutBound (i + 1)
  have hprofile := profileInterval_partition_L1_exact m p
    (boolTrueCount (V packet)) q frac cuts hstart hcuts hend
    (by
      simpa [boolTrueCount] using
        (Fintype.card_subtype_le (fun k : Fin m => V packet k = true))) hq hfrac0 hfrac1
  calc
    _ = ∑ i ∈ range p,
      |(profileInterval m (boolTrueCount (V packet)) (cuts i) (cuts (i + 1)) : Real) -
          profileIntervalMean m q frac (cuts i) (cuts (i + 1))| := by
      apply sum_congr rfl
      intro i hi
      rw [hpacket i (mem_range.mp hi)]
    _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile

theorem sortedPackets_intervalPartition_L1_sq {c m p q : Nat} (frac : Real)
    (V : Fin c → Fin m → Bool) (hV : ∀ i, Monotone (V i))
    (cuts : Nat → Nat) (hstart : cuts 0 = 0) (hcuts : Monotone cuts)
    (hcutBound : ∀ i, cuts i ≤ m) (hend : cuts p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts (i + 1) - cuts i) =>
          V packet ⟨cuts i + j.val, by
            have hab : cuts i ≤ cuts (i + 1) := hcuts (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts i + j.val < cuts i + (cuts (i + 1) - cuts i) := Nat.add_lt_add_left j.isLt _
              _ = cuts (i + 1) := hsum
              _ ≤ m := hcutBound (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts i) (cuts (i + 1))|)^2) ≤
      (c : Real) * ∑ packet : Fin c,
        ((boolTrueCount (V packet) : Real) - (q + frac))^2 := by
  rw [sortedPackets_intervalPartition_L1_exact frac V hV cuts hstart hcuts
    hcutBound hend hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun packet : Fin c => |(boolTrueCount (V packet) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))

theorem sortedPackets_individualIntervalPartitions_L1_exact {c m p q : Nat}
    (frac : Real) (V : Fin c → Fin m → Bool) (hV : ∀ packet, Monotone (V packet))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
          V packet ⟨cuts packet i + j.val, by
            have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                Nat.add_lt_add_left j.isLt _
              _ = cuts packet (i + 1) := hsum
              _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|) =
      ∑ packet : Fin c, |(boolTrueCount (V packet) : Real) - (q + frac)| := by
  apply Finset.sum_congr rfl
  intro packet _
  have hpacket (i : Nat) (hi : i < p) :
      boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
        V packet ⟨cuts packet i + j.val, by
          have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
          have hsum := Nat.add_sub_of_le hab
          calc
            cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
              Nat.add_lt_add_left j.isLt _
            _ = cuts packet (i + 1) := hsum
            _ ≤ m := hcutBound packet (i + 1)⟩) =
        profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) := by
    apply sortedBool_rankInterval_trueCount (V packet) (hV packet)
    · exact hcuts packet (Nat.le_succ i)
    · exact hcutBound packet (i + 1)
  have hprofile := profileInterval_partition_L1_exact m p
    (boolTrueCount (V packet)) q frac (cuts packet) (hstart packet) (hcuts packet)
    (hend packet) (by
      simpa [boolTrueCount] using
        (Fintype.card_subtype_le (fun k : Fin m => V packet k = true))) hq hfrac0 hfrac1
  calc
    _ = ∑ i ∈ range p,
        |(profileInterval m (boolTrueCount (V packet)) (cuts packet i) (cuts packet (i + 1)) : Real) -
          profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))| := by
      apply sum_congr rfl
      intro i hi
      rw [hpacket i (mem_range.mp hi)]
    _ = |(boolTrueCount (V packet) : Real) - (q + frac)| := hprofile

theorem sortedPackets_individualIntervalPartitions_L1_sq {c m p q : Nat}
    (frac : Real) (V : Fin c → Fin m → Bool) (hV : ∀ packet, Monotone (V packet))
    (cuts : Fin c → Nat → Nat) (hstart : ∀ packet, cuts packet 0 = 0)
    (hcuts : ∀ packet, Monotone (cuts packet))
    (hcutBound : ∀ packet i, cuts packet i ≤ m)
    (hend : ∀ packet, cuts packet p = m) (hq : q < m)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ packet : Fin c, ∑ i ∈ range p,
      |(boolTrueCount (fun j : Fin (cuts packet (i + 1) - cuts packet i) =>
          V packet ⟨cuts packet i + j.val, by
            have hab : cuts packet i ≤ cuts packet (i + 1) := hcuts packet (Nat.le_succ i)
            have hsum := Nat.add_sub_of_le hab
            calc
              cuts packet i + j.val < cuts packet i + (cuts packet (i + 1) - cuts packet i) :=
                Nat.add_lt_add_left j.isLt _
              _ = cuts packet (i + 1) := hsum
              _ ≤ m := hcutBound packet (i + 1)⟩) : Real) -
        profileIntervalMean m q frac (cuts packet i) (cuts packet (i + 1))|)^2) ≤
      (c : Real) * ∑ packet : Fin c,
        ((boolTrueCount (V packet) : Real) - (q + frac))^2 := by
  rw [sortedPackets_individualIntervalPartitions_L1_exact frac V hV cuts hstart
    hcuts hcutBound hend hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun packet : Fin c => |(boolTrueCount (V packet) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))


private theorem sum_profileTail32_differences (m K X : Nat) (hK : 32 * K ≤ m) :
    (∑ i ∈ range K,
      (profileTail m X (32 * (i + 1)) - profileTail m X (32 * i))) =
      profileTail m X (32 * K) - profileTail m X 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [sum_range_succ, ih (by omega)]
      simp only [profileTail]
      omega

theorem profileHalf_formula (K X i : Nat) (hi : i < K) :
    profileHalf K X i = min 32 (X - (32 * K - 32 * (i + 1))) := by
  have hab : 32 * i ≤ 32 * (i + 1) := by omega
  have hb : 32 * (i + 1) ≤ 32 * K := by omega
  unfold profileHalf
  rw [profileTail_interval_count32 (32 * K) X (32 * i) (32 * (i + 1)) hab hb]
  simp [Nat.mul_add]

private theorem profileHalf_mono_X (K X Y i : Nat) (hXY : Y ≤ X)
    (hi : i < K) : profileHalf K Y i ≤ profileHalf K X i := by
  rw [profileHalf_formula K Y i hi, profileHalf_formula K X i hi]
  exact min_le_min le_rfl (Nat.sub_le_sub_right hXY _)

theorem sum_profileHalf_eq_total (K X : Nat) (hX : X ≤ 32 * K) :
    (∑ i ∈ range K, profileHalf K X i) = X := by
  simp only [profileHalf]
  rw [sum_profileTail32_differences (32 * K) K X (by omega)]
  simp only [profileTail]
  omega

def profileHalfMean (K q : Nat) (frac : Real) (i : Nat) : Real :=
  (1 - frac) * profileHalf K q i + frac * profileHalf K (q + 1) i

theorem profileHalfMean_sum (K q : Nat) (frac : Real) (hq : q < 32 * K) :
    (∑ i ∈ range K, profileHalfMean K q frac i) = q + frac := by
  have hqsum : (∑ i ∈ range K, (profileHalf K q i : Real)) = q := by
    exact_mod_cast sum_profileHalf_eq_total K q (by omega)
  have hq1sum : (∑ i ∈ range K, (profileHalf K (q + 1) i : Real)) = q + 1 := by
    exact_mod_cast sum_profileHalf_eq_total K (q + 1) (by omega)
  unfold profileHalfMean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, hq1sum]
  ring

theorem profileHalfMean_L1_exact (K X q : Nat) (frac : Real) (hq : q < 32 * K)
    (hXbound : X ≤ 32 * K) (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i ∈ range K,
      |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
        |(X : Real) - (q + frac)| := by
  have hmean := profileHalfMean_sum K q frac hq
  have hxsum : (∑ i ∈ range K, (profileHalf K X i : Real)) = X := by
    exact_mod_cast sum_profileHalf_eq_total K X hXbound
  by_cases hX : X ≤ q
  · have hpoint : ∀ i ∈ range K,
        (profileHalf K X i : Real) ≤ profileHalfMean K q frac i := by
      intro i hi
      have hbase := profileHalf_mono_X K q X i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K X i : Real) ≤ profileHalf K q i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, (profileHalfMean K q frac i - (profileHalf K X i : Real)) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonpos (by linarith [hpoint i hi])]
        ring
      _ = (∑ i ∈ range K, profileHalfMean K q frac i) -
          (∑ i ∈ range K, (profileHalf K X i : Real)) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hmean, hxsum]
        have hXR : (X : Real) ≤ (q : Real) := by exact_mod_cast hX
        rw [abs_of_nonpos (by linarith [hfrac0])]
        ring
  · have hX' : q + 1 ≤ X := by omega
    have hpoint : ∀ i ∈ range K,
        profileHalfMean K q frac i ≤ (profileHalf K X i : Real) := by
      intro i hi
      have hbase := profileHalf_mono_X K X (q + 1) i (by omega) (mem_range.mp hi)
      have hnext := profileHalf_mono_X K (q + 1) q i (by omega) (mem_range.mp hi)
      unfold profileHalfMean
      have hn : (profileHalf K q i : Real) ≤ profileHalf K (q + 1) i := by exact_mod_cast hnext
      have hb : (profileHalf K (q + 1) i : Real) ≤ profileHalf K X i := by exact_mod_cast hbase
      nlinarith [hfrac0, hfrac1]
    calc
      (∑ i ∈ range K,
          |(profileHalf K X i : Real) - profileHalfMean K q frac i|) =
          ∑ i ∈ range K, ((profileHalf K X i : Real) - profileHalfMean K q frac i) := by
        apply sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (by linarith [hpoint i hi])]
      _ = (∑ i ∈ range K, (profileHalf K X i : Real)) -
          (∑ i ∈ range K, profileHalfMean K q frac i) := by rw [Finset.sum_sub_distrib]
      _ = |(X : Real) - (q + frac)| := by
        rw [hxsum, hmean]
        have hXR : (q : Real) + 1 ≤ (X : Real) := by exact_mod_cast hX'
        rw [abs_of_nonneg (by linarith [hfrac1])]

theorem sortedBool_profileHalf_trueCount {K : Nat} (v : Fin (32 * K) → Bool)
    (hv : Monotone v) (X : Nat) (hX : boolTrueCount v = X) (i : Nat) (hi : i < K) :
    boolTrueCount (fun j : Fin 32 => v ⟨32 * i + j,
      by have hj := j.isLt; omega⟩) = profileHalf K X i := by
  let m := 32 * K
  let a := 32 * i
  let b := 32 * (i + 1)
  have ha : a ≤ m := by dsimp [a, m]; omega
  have hb : b ≤ m := by dsimp [b, m]; omega
  have hab : a + 32 = b := by dsimp [a, b]; omega
  let Plo : Fin a → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le ha) (Fin.castAdd (m - a) j))
  let Phi : Fin b → Bool := fun j =>
    v (Fin.cast (Nat.add_sub_of_le hb) (Fin.castAdd (m - b) j))
  let C : Fin 32 → Bool := fun j => v ⟨a + j, by dsimp [a, m]; have hj := j.isLt; omega⟩
  have he : Fin.append Plo C = Phi ∘ Fin.cast hab := by
    funext k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [Fin.append_left, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [Plo, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_mk]
    · simp only [Fin.append_right, Function.comp_apply]
      apply congrArg v
      apply Fin.ext
      simp only [C, Phi, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, Fin.val_mk]
  have hcounts : boolTrueCount Phi = boolTrueCount Plo + boolTrueCount C := by
    calc
      boolTrueCount Phi = boolTrueCount (Phi ∘ Fin.cast hab) :=
        (boolTrueCount_finCast hab Phi).symm
      _ = boolTrueCount (Fin.append Plo C) := congrArg boolTrueCount he.symm
      _ = boolTrueCount Plo + boolTrueCount C := boolTrueCount_append_general Plo C
  have hlo := sortedBool_prefix_trueCount v hv ha
  have hhi := sortedBool_prefix_trueCount v hv hb
  rw [hX] at hlo hhi
  change boolTrueCount C = profileHalf K X i
  have hC : boolTrueCount C = boolTrueCount Phi - boolTrueCount Plo := by omega
  unfold profileHalf profileTail
  rw [hC, hhi, hlo]

theorem sortedPackets_halfProfile_L1_exact {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, |(boolTrueCount (V i) : Real) - (q + frac)| := by
  let X : Fin c → Nat := fun i => boolTrueCount (V i)
  have hcell (i : Fin c) (j : Fin K) :
      boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hk := k.isLt; omega⟩) = profileHalf K (X i) j.val := by
    exact sortedBool_profileHalf_trueCount (V i) (hV i) (X i) rfl j.val j.isLt
  have hprofiles : (∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|) =
      ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hcell i j]
  calc
    _ = ∑ i : Fin c, ∑ j : Fin K,
        |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val| := hprofiles
    _ = ∑ i : Fin c, |(X i : Real) - (q + frac)| := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j : Fin K,
            |(profileHalf K (X i) j.val : Real) - profileHalfMean K q frac j.val|) =
            ∑ j ∈ range K,
              |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j| :=
          Fin.sum_univ_eq_sum_range (fun j : Nat =>
            |(profileHalf K (X i) j : Real) - profileHalfMean K q frac j|) K
        _ = |(X i : Real) - (q + frac)| :=
          profileHalfMean_L1_exact K (X i) q frac hq (by
            dsimp [X]
            unfold boolTrueCount
            simpa using Fintype.card_subtype_le (fun k : Fin (32 * K) => V i k = true)) hfrac0 hfrac1

theorem sortedPackets_halfProfile_L1_sq {c K : Nat}
    (V : Fin c → Fin (32 * K) → Bool) (hV : ∀ i, Monotone (V i))
    (q : Nat) (frac : Real) (hq : q < 32 * K)
    (hfrac0 : 0 ≤ frac) (hfrac1 : frac ≤ 1) :
    ((∑ i : Fin c, ∑ j : Fin K,
      |(boolTrueCount (fun k : Fin 32 => V i ⟨32 * j.val + k,
        by have hj := j.isLt; have hk := k.isLt; omega⟩) : Real) -
          profileHalfMean K q frac j.val|)^2) ≤
      (c : Real) * ∑ i : Fin c,
        ((boolTrueCount (V i) : Real) - (q + frac))^2 := by
  rw [sortedPackets_halfProfile_L1_exact V hV q frac hq hfrac0 hfrac1]
  simpa [sq_abs, mul_comm] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin c => |(boolTrueCount (V i) : Real) - (q + frac)|)
      (fun _ => (1 : Real)))
