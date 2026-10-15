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

private theorem cuts_le_end (p : Nat) (cuts : Nat → Nat) (hcuts : Monotone cuts)
    (i : Nat) (hi : i ≤ p) : cuts i ≤ cuts p := hcuts hi

private theorem profileInterval_partition_total (m p X : Nat) (cuts : Nat → Nat)
    (hstart : cuts 0 = 0) (hcuts : Monotone cuts) (hend : cuts p = m)
    (hX : X ≤ m) : (∑ i ∈ range p, profileInterval m X (cuts i) (cuts (i + 1))) = X := by
  rw [sum_profileIntervals_partition m p X cuts hstart hcuts hend]
  simp only [profileTail]
  omega

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

noncomputable def senderOutgoingProfileErrorVar {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (packet : Fin c) (i : Nat) : Real :=
  |(trueCountOn (senderOutgoingPiece (S packet) (up packet) (down packet) i)
      (v packet) : Real) -
    profileIntervalMean (S packet).card (q packet) (frac packet)
      (senderRankCut (up packet) (down packet) i)
      (senderRankCut (up packet) (down packet) (i + 1))|

/-- The no-loss sender partition identity also holds for unequal source bag
sizes and a separate fractional ideal count for each sender. This is the
shape needed when a receiver combines its larger parent bag with smaller child
bags. -/
theorem sortedSenderOutgoing_profile_error_exact_var {c N : Nat}
    (S : Fin c → Finset (Fin N)) (v : Fin c → Fin N → Bool)
    (up down q : Fin c → Nat) (frac : Fin c → Real)
    (hsize : ∀ packet, (S packet).card = up packet + 64 * down packet)
    (hu : ∀ packet, 2 ∣ up packet)
    (hsorted : ∀ packet, Monotone (v packet ∘ (S packet).orderEmbOfFin rfl))
    (hq : ∀ packet, q packet < (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1) :
    (∑ packet : Fin c, ∑ i ∈ range 66,
      senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hlocal (packet : Fin c) :
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
    have hprofile := profileInterval_partition_L1_exact
      (S packet).card 66 (trueCountOn (S packet) (v packet)) (q packet)
      (frac packet) cuts hstart hcuts hend hX
      (hq packet) (hfrac0 packet) (hfrac1 packet)
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
    (∑ packet : Fin c, ∑ i ∈ range 66,
        senderOutgoingProfileErrorVar S v up down q frac packet i) =
      ∑ packet : Fin c,
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
    (hq : ∀ packet, q packet < (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
    (selected : Fin c → Finset Nat)
    (hselected : ∀ packet, selected packet ⊆ range 66) :
    (∑ packet : Fin c, ∑ i ∈ selected packet,
      senderOutgoingProfileErrorVar S v up down q frac packet i) ≤
      ∑ packet : Fin c,
        |(trueCountOn (S packet) (v packet) : Real) - (q packet + frac packet)| := by
  have hfull := sortedSenderOutgoing_profile_error_exact_var S v up
    down q frac hsize hu hsorted hq hfrac0 hfrac1
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
    (hq : ∀ packet, q packet < (S packet).card)
    (hfrac0 : ∀ packet, 0 ≤ frac packet)
    (hfrac1 : ∀ packet, frac packet ≤ 1)
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
    S v up down q frac hsize hu hsorted hq hfrac0 hfrac1 selected hselected
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
    (hq : ∀ source, q source < (S source).card)
    (hfrac0 : ∀ source, 0 ≤ frac source)
    (hfrac1 : ∀ source, frac source ≤ 1)
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
    hq hfrac0 hfrac1 (receiverOutgoingSelection parentPort)
    (fun source => receiverOutgoingSelection_subset parentPort hport source)


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
