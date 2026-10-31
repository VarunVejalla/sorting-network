import D2InversionLocalization

open Chvatal.D2InversionLocalization

namespace Chvatal.D2BandInversion

/-- The number of wires in a finite index interval is at most its integer
width. -/
theorem interval_band_card_le {N lo hi : Nat} :
    (Finset.univ.filter fun p : Fin N => lo ≤ p.val ∧ p.val < hi).card ≤ hi - lo := by
  classical
  let band := Finset.univ.filter fun p : Fin N => lo ≤ p.val ∧ p.val < hi
  have hmaps : Set.MapsTo (fun p : Fin N => p.val - lo) band (Finset.range (hi - lo)) := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    exact Finset.mem_range.mpr (Nat.sub_lt_sub_right hp'.1 hp'.2)
  have hinj : Set.InjOn (fun p : Fin N => p.val - lo) band := by
    intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hpq' : p.val - lo = q.val - lo := hpq
    have hpadd : p.val - lo + lo = p.val := Nat.sub_add_cancel hp'.1
    have hqadd : q.val - lo + lo = q.val := Nat.sub_add_cancel hq'.1
    apply Fin.ext
    calc
      p.val = (p.val - lo) + lo := hpadd.symm
      _ = (q.val - lo) + lo := congrArg (fun x : Nat => x + lo) hpq'
      _ = q.val := hqadd
  calc
    band.card ≤ (Finset.range (hi - lo)).card :=
      Finset.card_le_card_of_injOn _ hmaps hinj
    _ = hi - lo := Finset.card_range _

/-- If a Boolean word is all false before a band and all true after it, every
one-before-zero inversion lies entirely inside that band. Thus a band with
at most `K` wires contributes at most `K^2` inversions. -/
theorem inversionCount_le_of_uniform_exterior {N K lo hi : Nat}
    (v : Fin N → Bool)
    (hlo : ∀ p : Fin N, p.val < lo → v p = false)
    (hhi : ∀ p : Fin N, hi ≤ p.val → v p = true)
    (hband : (Finset.univ.filter fun p : Fin N =>
      lo ≤ p.val ∧ p.val < hi).card ≤ K) :
    inversionCount v ≤ K * K := by
  classical
  let band := Finset.univ.filter fun p : Fin N => lo ≤ p.val ∧ p.val < hi
  have hsubset : inversionPairs v ⊆ band ×ˢ band := by
    intro ij hij
    change ij ∈ Finset.univ.filter (fun ij =>
      ij.1.val < ij.2.val ∧ v ij.1 = true ∧ v ij.2 = false) at hij
    rcases Finset.mem_filter.mp hij with ⟨_, hpair⟩
    rcases hpair with ⟨horder, htrue, hfalse⟩
    have hiLo : lo ≤ ij.1.val := by
      by_contra h
      have hfalse' := hlo ij.1 (by omega)
      rw [hfalse'] at htrue
      contradiction
    have hjHi : ij.2.val < hi := by
      by_contra h
      have htrue' := hhi ij.2 (by omega)
      rw [htrue'] at hfalse
      contradiction
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hiLo, lt_trans horder hjHi⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨le_trans hiLo (Nat.le_of_lt horder), hjHi⟩⟩
  calc
    inversionCount v = (inversionPairs v).card := rfl
    _ ≤ (band ×ˢ band).card := Finset.card_le_card hsubset
    _ = band.card * band.card := by rw [Finset.card_product]
    _ ≤ K * K := Nat.mul_le_mul hband hband

/-- A common exterior band of width at most `W` immediately gives a uniform
aggregate inversion budget `W^2`. -/
theorem inversionCount_le_of_uniform_exterior_width {N W lo hi : Nat}
    (v : Fin N → Bool)
    (hwidth : hi - lo ≤ W)
    (hbefore : ∀ p : Fin N, p.val < lo → v p = false)
    (hafter : ∀ p : Fin N, hi ≤ p.val → v p = true) :
    inversionCount v ≤ W * W := by
  apply inversionCount_le_of_uniform_exterior v hbefore hafter
  exact (interval_band_card_le).trans hwidth

private theorem card_prefix_positions {N q : Nat} (hq : q ≤ N) :
    (Finset.univ.filter fun p : Fin N => p.val < q).card = q := by
  classical
  calc
    (Finset.univ.filter fun p : Fin N => p.val < q).card =
        (Finset.range q).card := by
      apply Finset.card_bij (fun p _ => p.val)
      · intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      · intro p hp r hr hpr
        exact Fin.ext hpr
      · intro r hr
        have hr' := Finset.mem_range.mp hr
        refine ⟨⟨r, lt_of_lt_of_le hr' hq⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr'⟩
    _ = q := Finset.card_range _

/-- The true zero-count cut lies inside any interval with an all-false prefix
and an all-true suffix, provided the interval endpoints fit in the word. -/
theorem zeroCount_mem_uniform_exterior_band {N lo hi : Nat}
    (v : Fin N → Bool) (hloN : lo ≤ N) (hhiN : hi ≤ N)
    (hbefore : ∀ p : Fin N, p.val < lo → v p = false)
    (hafter : ∀ p : Fin N, hi ≤ p.val → v p = true) :
    lo ≤ zeroCount v ∧ zeroCount v ≤ hi := by
  classical
  let prefixLo := Finset.univ.filter fun p : Fin N => p.val < lo
  let prefixHi := Finset.univ.filter fun p : Fin N => p.val < hi
  have hloCard : prefixLo.card = lo := by
    dsimp [prefixLo]
    exact card_prefix_positions hloN
  have hhiCard : prefixHi.card = hi := by
    dsimp [prefixHi]
    exact card_prefix_positions hhiN
  have hloSubset : prefixLo ⊆ zeroPositions v := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    simp [zeroPositions, hbefore p hp'.2]
  have hhiSubset : zeroPositions v ⊆ prefixHi := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · by_contra hnot
      have htrue := hafter p (by omega)
      rw [htrue] at hp'
      simp at hp'
  constructor
  · dsimp [zeroCount]
    rw [← hloCard]
    exact Finset.card_le_card hloSubset
  · dsimp [zeroCount]
    rw [← hhiCard]
    exact Finset.card_le_card hhiSubset

/-- If the uniform exterior band has width `W`, every misplaced bit lies
within distance `W` of the exact zero-count cut. This is much sharper than
deducing distance from a quadratic inversion-count bound. -/
theorem misplaced_bits_within_uniform_exterior_band {N W lo hi : Nat}
    (v : Fin N → Bool) (hloN : lo ≤ N) (hhiN : hi ≤ N)
    (hwidth : hi - lo ≤ W)
    (hbefore : ∀ p : Fin N, p.val < lo → v p = false)
    (hafter : ∀ p : Fin N, hi ≤ p.val → v p = true) :
    (∀ p : Fin N, v p = false → zeroCount v ≤ p.val →
      p.val < zeroCount v + W) ∧
    (∀ p : Fin N, v p = true → p.val < zeroCount v →
      zeroCount v ≤ p.val + W) := by
  have hcut := zeroCount_mem_uniform_exterior_band v hloN hhiN hbefore hafter
  have hhiLe : hi ≤ lo + W := by omega
  constructor
  · intro p hp hq
    have hbelow : p.val < hi := by
      by_contra h
      have htrue := hafter p (by omega)
      rw [htrue] at hp
      contradiction
    omega
  · intro p hp hpq
    have habove : lo ≤ p.val := by
      by_contra h
      have hfalse := hbefore p (by omega)
      rw [hfalse] at hp
      contradiction
    omega

/-- The total number of wrong-side bits at the exact zero-count cut is at
most the width of the uniform-exterior band. -/
theorem misplaced_population_le_uniform_exterior_band {N W lo hi : Nat}
    (v : Fin N → Bool) (hloN : lo ≤ N) (hhiN : hi ≤ N)
    (hwidth : hi - lo ≤ W)
    (hbefore : ∀ p : Fin N, p.val < lo → v p = false)
    (hafter : ∀ p : Fin N, hi ≤ p.val → v p = true) :
    (cutWrongOnes v (zeroCount v)).card +
      (cutWrongZeros v (zeroCount v)).card ≤ W := by
  classical
  let q := zeroCount v
  let band := Finset.univ.filter fun p : Fin N => lo ≤ p.val ∧ p.val < hi
  let wrongOnes := cutWrongOnes v q
  let wrongZeros := cutWrongZeros v q
  have hcut := zeroCount_mem_uniform_exterior_band v hloN hhiN hbefore hafter
  have hones : wrongOnes ⊆ band := by
    intro p hp
    change p ∈ cutWrongOnes v q at hp
    simp only [cutWrongOnes, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hpq, hptrue⟩
    have hloP : lo ≤ p.val := by
      by_contra h
      have hfalse := hbefore p (by omega)
      rw [hfalse] at hptrue
      contradiction
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hloP, lt_of_lt_of_le hpq hcut.2⟩⟩
  have hzeros : wrongZeros ⊆ band := by
    intro p hp
    change p ∈ cutWrongZeros v q at hp
    simp only [cutWrongZeros, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hqp, hpfalse⟩
    have hloP : lo ≤ p.val := le_trans hcut.1 hqp
    have hhiP : p.val < hi := by
      by_contra h
      have htrue := hafter p (by omega)
      rw [htrue] at hpfalse
      contradiction
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hloP, hhiP⟩⟩
  have hdisj : Disjoint wrongOnes wrongZeros := by
    rw [Finset.disjoint_left]
    intro p hp1 hp0
    change p ∈ cutWrongOnes v q at hp1
    change p ∈ cutWrongZeros v q at hp0
    simp only [cutWrongOnes, Finset.mem_filter, Finset.mem_univ, true_and] at hp1
    simp only [cutWrongZeros, Finset.mem_filter, Finset.mem_univ, true_and] at hp0
    omega
  have hunion : wrongOnes ∪ wrongZeros ⊆ band := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hones hp
    · exact hzeros hp
  have hband : band.card ≤ W := (interval_band_card_le).trans hwidth
  calc
    wrongOnes.card + wrongZeros.card = (wrongOnes ∪ wrongZeros).card := by
      rw [Finset.card_union_of_disjoint hdisj]
    _ ≤ band.card := Finset.card_le_card hunion
    _ ≤ W := hband
end Chvatal.D2BandInversion
