import AKS.Chvatal.StrangerBounds
import D2RankAlignment
import D2StaticWireSets
import D2LocalRankDisplacement

/-!
Convert a uniform rank-prefix discrepancy into the all-prefix escape profile
used by `sent_outside_le_of_tail_profile`.  This is the interface needed to
turn a fixed-core cut bound into a distance-independent, size-independent
sender tail.
-/

open Finset
open Chvatal.D2RankAlignment
open Chvatal.D2LocalRankDisplacement

namespace Chvatal.D2RankCutTail

/-- The natural-valued tail supplied by a rank-cut error `err` and protected
margin `margin`. -/
def rankCutTail (j margin err : Nat) : Nat :=
  min j (j - margin + err)

/-- Combining the top and bottom escape budgets retains one full margin of
contraction in their total outsider mass, while paying the additive defect on
both ends. -/
theorem rankCutTail_two_sided_le (j k margin err : Nat) :
    rankCutTail j margin err + rankCutTail k margin err ≤
      2 * err + (j + k - margin) := by
  unfold rankCutTail
  omega

/-- If one side has no outsiders, the two tails pay only one local error
allowance. This is the sharper aggregate interface needed if a schedule
invariant proves one-sided endpoint deficits. -/
theorem rankCutTail_one_sided_le (j k margin err : Nat)
    (hone : j = 0 ∨ k = 0) :
    rankCutTail j margin err + rankCutTail k margin err ≤
      err + (j + k - margin) := by
  rcases hone with hj | hk
  · subst j
    simp [rankCutTail]
    omega
  · subst k
    simp [rankCutTail]
    omega

private theorem card_finset_values_in_window {N : Nat}
    (s : Finset (Fin N)) (lo hi : Nat)
    (hlo : ∀ p ∈ s, lo ≤ p.val) (hhi : ∀ p ∈ s, p.val < hi) :
    s.card ≤ hi - lo := by
  classical
  let vals := s.image fun p : Fin N => p.val
  have hcard : vals.card = s.card := by
    symm
    rw [Finset.card_image_of_injOn (f := fun p : Fin N => p.val) (s := s)]
    intro a ha b hb hab
    exact Fin.ext hab
  have hsub : vals ⊆ Finset.Ico lo hi := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_Ico.mpr ⟨hlo p hp, hhi p hp⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, Nat.card_Ico] at hle
  exact hle

private theorem card_fin_val_lt {N q : Nat} (hq : q ≤ N) :
    (Finset.univ.filter fun x : Fin N => x.val < q).card = q := by
  classical
  calc
    (Finset.univ.filter fun x : Fin N => x.val < q).card =
        (Finset.range q).card := by
      apply Finset.card_bij (fun x _ => x.val)
      · intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      · intro x hx y hy hxy
        exact Fin.ext hxy
      · intro y hy
        have hy' := Finset.mem_range.mp hy
        refine ⟨⟨y, lt_of_lt_of_le hy' hq⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩
    _ = q := Finset.card_range q

private theorem card_perm_val_lt {N q : Nat} (out : Fin N → Fin N)
    (hout : Function.Bijective out) (hq : q ≤ N) :
    (Finset.univ.filter fun p : Fin N => (out p).val < q).card = q := by
  classical
  calc
    (Finset.univ.filter fun p : Fin N => (out p).val < q).card =
        (Finset.univ.filter fun x : Fin N => x.val < q).card := by
      apply Finset.card_bij (fun p _ => out p)
      · intro p hp
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
      · intro a ha b hb hab
        exact hout.1 hab
      · intro x hx
        obtain ⟨p, rfl⟩ := hout.2 x
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        exact (Finset.mem_filter.mp hx).2
    _ = q := card_fin_val_lt hq

/-- A pointwise rank-displacement bound for a permutation implies a uniform
rank-prefix cut error of the same size. `pos` is the inverse permutation,
viewed as the output address of each key. -/
theorem rank_cut_error_of_pointwise_displacement
    {N E : Nat} (out : Fin N → Fin N) (hout : Function.Bijective out)
    (hdisp : ∀ p, (out p).val ≤ p.val + E ∧ p.val ≤ (out p).val + E) :
    ∀ q c, q ≤ N → c ≤ N →
      countDistance
        ((Finset.univ.filter fun x : Fin N => x.val < q ∧
          ((Equiv.ofBijective out hout).symm x).val < c).card)
        (min q c) ≤ E := by
  classical
  intro q c hq hc
  let e := Equiv.ofBijective out hout
  let a := Finset.univ.filter fun p : Fin N => (out p).val < q ∧ p.val < c
  let missingLow := Finset.univ.filter fun p : Fin N => (out p).val < q ∧ c ≤ p.val
  let missingPos := Finset.univ.filter fun p : Fin N => p.val < c ∧ q ≤ (out p).val
  let keys := Finset.univ.filter fun x : Fin N => x.val < q ∧ (e.symm x).val < c
  have himage : keys.image e.symm = a := by
    ext p
    simp only [keys, a, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, ⟨hxq, hxc⟩, rfl⟩
      have hq' : (out (e.symm x)).val < q := by
        change (e (e.symm x)).val < q
        rw [e.apply_symm_apply]
        exact hxq
      exact ⟨hq', hxc⟩
    · intro hp
      refine ⟨out p, ⟨hp.1, ?_⟩, ?_⟩
      · change (e.symm (e p)).val < c
        simpa using hp.2
      change e.symm (e p) = p
      exact e.symm_apply_apply p
  have hkeyCard : keys.card = a.card := by
    calc
      keys.card = (keys.image e.symm).card := by
        rw [Finset.card_image_of_injOn (f := e.symm) (s := keys)]
        intro x hx y hy hxy
        exact e.symm.injective hxy
      _ = a.card := by rw [himage]
  have hlowSplit : a.card + missingLow.card = q := by
    have hpart : a ∪ missingLow =
        Finset.univ.filter fun p : Fin N => (out p).val < q := by
      ext p
      simp only [a, missingLow, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact h
        · exact h
      · intro h
        by_cases hpc : p.val < c
        · exact Or.inl ⟨h, hpc⟩
        · exact Or.inr ⟨h, by omega⟩
    have hdisj : Disjoint a missingLow := by
      apply Finset.disjoint_left.mpr
      intro p hp1 hp2
      simp only [a, missingLow, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp1 hp2
      omega
    have hcard := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hdisj, card_perm_val_lt out hout hq] at hcard
    exact hcard
  have hposSplit : a.card + missingPos.card = c := by
    have hpart : a ∪ missingPos =
        Finset.univ.filter fun p : Fin N => p.val < c := by
      ext p
      simp only [a, missingPos, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨_, h⟩ | ⟨h, _⟩)
        · exact h
        · exact h
      · intro h
        by_cases hpq : (out p).val < q
        · exact Or.inl ⟨hpq, h⟩
        · exact Or.inr ⟨h, by omega⟩
    have hdisj : Disjoint a missingPos := by
      apply Finset.disjoint_left.mpr
      intro p hp1 hp2
      simp only [a, missingPos, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp1 hp2
      omega
    have hcard := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hdisj, card_fin_val_lt hc] at hcard
    exact hcard
  have hupperQ : a.card ≤ q := by
    have hsub : a ⊆ Finset.univ.filter fun p : Fin N => (out p).val < q := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hp).2.1⟩
    calc a.card ≤ (Finset.univ.filter fun p : Fin N => (out p).val < q).card :=
      Finset.card_le_card hsub
      _ = q := card_perm_val_lt out hout hq
  have hupperC : a.card ≤ c := by
    have hsub : a ⊆ Finset.univ.filter fun p : Fin N => p.val < c := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hp).2.2⟩
    calc a.card ≤ (Finset.univ.filter fun p : Fin N => p.val < c).card :=
      Finset.card_le_card hsub
      _ = c := card_fin_val_lt hc
  by_cases hqc : q ≤ c
  · have hdist : countDistance a.card q = q - a.card := by
      simp [countDistance, Nat.sub_eq_zero_of_le hupperQ]
    have hmissingLow : missingLow.card ≤ E := by
      have hlo (p : Fin N) (hp : p ∈ missingLow) : c ≤ p.val :=
        (Finset.mem_filter.mp hp).2.2
      have hhi (p : Fin N) (hp : p ∈ missingLow) : p.val < q + E := by
        have hp' := (Finset.mem_filter.mp hp).2.1
        have hd := hdisp p
        omega
      have hcard := card_finset_values_in_window missingLow c (q + E) hlo hhi
      omega
    rw [hkeyCard, Nat.min_eq_left hqc, hdist]
    omega
  · have hcq : c ≤ q := Nat.le_of_not_ge hqc
    have hdist : countDistance a.card c = c - a.card := by
      simp [countDistance, Nat.sub_eq_zero_of_le hupperC]
    have hmissingPos : missingPos.card ≤ E := by
      have hlo (p : Fin N) (hp : p ∈ missingPos) : q - E ≤ p.val := by
        have hp' := (Finset.mem_filter.mp hp).2.2
        have hd := hdisp p
        omega
      have hhi (p : Fin N) (hp : p ∈ missingPos) : p.val < c :=
        (Finset.mem_filter.mp hp).2.1
      have hcard := card_finset_values_in_window missingPos (q - E) c hlo hhi
      omega
    rw [hkeyCard, Nat.min_eq_right hcq, hdist]
    omega

/-- The inverse position map of a permutation has exactly `c` keys before
every cut `c`. -/
theorem inverse_position_prefix_card
    {N : Nat} (out : Fin N → Fin N) (hout : Function.Bijective out)
    (c : Nat) (hc : c ≤ N) :
    (Finset.univ.filter fun x : Fin N =>
      ((Equiv.ofBijective out hout).symm x).val < c).card = c := by
  classical
  let e := Equiv.ofBijective out hout
  let keys := Finset.univ.filter fun x : Fin N => (e.symm x).val < c
  have himage : keys.image e.symm = Finset.univ.filter
      fun p : Fin N => p.val < c := by
    ext p
    simp only [keys, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      refine ⟨out p, ?_, ?_⟩
      · change (e.symm (e p)).val < c
        simpa using hp
      · change e.symm (e p) = p
        exact e.symm_apply_apply p
  have hcard : keys.card =
      (Finset.univ.filter fun p : Fin N => p.val < c).card := by
    calc
      keys.card = (keys.image e.symm).card := by
        rw [Finset.card_image_of_injOn (f := e.symm) (s := keys)]
        intro x hx y hy hxy
        exact e.symm.injective hxy
      _ = _ := by rw [himage]
  simpa [keys, card_fin_val_lt hc] using hcard

theorem top_prefix_escape_le_of_rank_cut_error
    {N : Nat} (K : Finset (Fin N)) (pos : Fin N → Nat)
    (margin err j : Nat) (hj : j ≤ K.card) (hm : margin ≤ K.card)
    (hprefix : ∀ c, c ≤ K.card →
      (K.filter fun x => pos x < c).card = c)
    (hcut : ∀ q c, q ≤ K.card → c ≤ K.card →
      countDistance
        ((K.filter fun x => rankIn K x < q ∧ pos x < c).card)
        (min q c) ≤ err) :
    (K.filter fun x => K.card - j ≤ rankIn K x ∧
      pos x < K.card - margin).card ≤
      min j (j - margin + err) := by
  classical
  let c := K.card - margin
  let q := K.card - j
  let low := K.filter fun x => rankIn K x < q ∧ pos x < c
  let high := K.filter fun x => q ≤ rankIn K x ∧ pos x < c
  have hc : c ≤ K.card := Nat.sub_le _ _
  have hq : q ≤ K.card := Nat.sub_le _ _
  have hlowerr : countDistance low.card (min q c) ≤ err := by
    simpa [low, c, q] using hcut q c hq hc
  have hlowlo : min q c - low.card ≤ err := by
    unfold countDistance at hlowerr
    omega
  have hsplit : low.card + high.card = c := by
    have hpart : low ∪ high = K.filter (fun x => pos x < c) := by
      ext x
      simp only [low, high, mem_union, mem_filter]
      constructor
      · rintro (⟨⟨hx, _, _⟩⟩ | ⟨⟨hx, _, _⟩⟩) <;> exact ⟨hx, by assumption⟩
      · rintro ⟨hx, hpos⟩
        by_cases hr : rankIn K x < q
        · exact Or.inl ⟨hx, hr, hpos⟩
        · exact Or.inr ⟨hx, by omega, hpos⟩
    have hdisj : Disjoint low high := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx1 hx2
      simp only [low, high, mem_filter] at hx1 hx2
      omega
    rw [← hprefix c hc, ← hpart, Finset.card_union_of_disjoint hdisj]
  have hbase : high.card ≤ c - min q c + err := by omega
  have hbase' : c - min q c = j - margin := by
    dsimp [c, q]
    omega
  have hsmall : high.card ≤ j := by
    have hsub : high ⊆ K.filter (fun x => K.card - j ≤ rankIn K x) := by
      intro x hx
      simp only [high, mem_filter] at hx
      simp only [mem_filter]
      exact ⟨hx.1, by simpa [q] using hx.2.1⟩
    calc
      high.card ≤ (K.filter fun x => K.card - j ≤ rankIn K x).card :=
        Finset.card_le_card hsub
      _ = j := top_rank_prefix_card_eq K j hj
  have htail : high.card ≤ j - margin + err := by
    rw [hbase'] at hbase
    exact hbase
  have hresult : high.card ≤ min j (j - margin + err) := by omega
  simpa [high, q, c] using hresult

/-- The symmetric lower-rank tail: at most the surplus below a protected
margin, plus the uniform cut error, can cross its lower edge. -/
theorem bottom_prefix_escape_le_of_rank_cut_error
    {N : Nat} (K : Finset (Fin N)) (pos : Fin N → Nat)
    (margin err j : Nat) (hj : j ≤ K.card) (hm : margin ≤ K.card)
    (hcut : ∀ q c, q ≤ K.card → c ≤ K.card →
      countDistance
        ((K.filter fun x => rankIn K x < q ∧ pos x < c).card)
        (min q c) ≤ err) :
    (K.filter fun x => rankIn K x < j ∧ margin ≤ pos x).card ≤
      min j (j - margin + err) := by
  classical
  let low := K.filter fun x => rankIn K x < j ∧ pos x < margin
  let high := K.filter fun x => rankIn K x < j ∧ margin ≤ pos x
  have hlowerr : countDistance low.card (min j margin) ≤ err := by
    simpa [low] using hcut j margin hj hm
  have hlowlo : min j margin - low.card ≤ err := by
    unfold countDistance at hlowerr
    omega
  have hsplit : low.card + high.card = j := by
    have hpart : low ∪ high = K.filter (fun x => rankIn K x < j) := by
      ext x
      simp only [low, high, mem_union, mem_filter]
      constructor
      · rintro (⟨⟨hx, hr, _⟩⟩ | ⟨⟨hx, hr, _⟩⟩) <;> exact ⟨hx, hr⟩
      · rintro ⟨hx, hr⟩
        by_cases hp : pos x < margin
        · exact Or.inl ⟨hx, hr, hp⟩
        · exact Or.inr ⟨hx, hr, by omega⟩
    have hdisj : Disjoint low high := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx1 hx2
      simp only [low, high, mem_filter] at hx1 hx2
      omega
    have hcard := congrArg Finset.card hpart
    rw [Finset.card_union_of_disjoint hdisj,
      bottom_rank_prefix_card_eq K j hj] at hcard
    exact hcard
  have hsmall : high.card ≤ j := by omega
  have htail : high.card ≤ j - margin + err := by
    have hdelta : j - min j margin = j - margin := by omega
    omega
  have hresult : high.card ≤ min j (j - margin + err) := by omega
  simpa [high] using hresult

/-- A uniform rank-cut discrepancy supplies the complete UB-34 fringe-send
profile, with no bound on either outsider count. -/
theorem sent_outside_le_of_rank_cut_error
    {N : Nat} (K : Finset (Fin N)) (pos : Fin N → Nat)
    (pi Ilo Ihi err : Nat)
    (hmargin : pi / 2 ≤ K.card)
    (hprefix : ∀ c, c ≤ K.card →
      (K.filter fun x => pos x < c).card = c)
    (hcut : ∀ q c, q ≤ K.card → c ≤ K.card →
      countDistance
        ((K.filter fun x => rankIn K x < q ∧ pos x < c).card)
        (min q c) ≤ err) :
    (((K.filter fun (x : Fin N) => pi / 2 ≤ pos x ∧
        pos x < K.card - pi / 2).filter
        fun (x : Fin N) => ¬ (Ilo ≤ (x : Nat) ∧ (x : Nat) < Ihi)).card : Real) ≤
      (((min ((K.filter fun (x : Fin N) => Ihi ≤ (x : Nat)).card)
        ((K.filter fun (x : Fin N) => Ihi ≤ (x : Nat)).card - pi / 2 + err) : Nat) : Real) +
       ((min ((K.filter fun (x : Fin N) => (x : Nat) < Ilo).card)
        ((K.filter fun (x : Fin N) => (x : Nat) < Ilo).card - pi / 2 + err) : Nat) : Real)) := by
  classical
  let tail : Nat → Real := fun j =>
    ((min j (j - pi / 2 + err) : Nat) : Real)
  have hhi : ∀ j, j ≤ K.card →
      ((K.filter fun x => K.card - j ≤ rankIn K x ∧
        pos x < K.card - pi / 2).card : Real) ≤ tail j := by
    intro j hj
    have hn := top_prefix_escape_le_of_rank_cut_error
      K pos (pi / 2) err j hj hmargin hprefix hcut
    have hnR : ((K.filter fun x => K.card - j ≤ rankIn K x ∧
        pos x < K.card - pi / 2).card : Real) ≤
        ((min j (j - pi / 2 + err) : Nat) : Real) := by exact_mod_cast hn
    simpa [tail] using hnR
  have hlo : ∀ j, j ≤ K.card →
      ((K.filter fun x => rankIn K x < j ∧ pi / 2 ≤ pos x).card : Real) ≤
        tail j := by
    intro j hj
    have hn := bottom_prefix_escape_le_of_rank_cut_error
      K pos (pi / 2) err j hj hmargin hcut
    have hnR : ((K.filter fun x => rankIn K x < j ∧ pi / 2 ≤ pos x).card : Real) ≤
        ((min j (j - pi / 2 + err) : Nat) : Real) := by exact_mod_cast hn
    simpa [tail] using hnR
  have hsend := Chvatal.sent_outside_le_of_tail_profile
    K pos pi Ilo Ihi tail hhi hlo
  simpa [tail] using hsend

/-- Pointwise displacement of a bijective local sorter supplies an explicit
all-prefix fringe-send bound. The theorem is stated for a complete rank tile;
connecting scheduled ragged senders to such tiles is a separate step. -/
theorem sent_outside_le_of_pointwise_displacement
    {N E : Nat} (out : Fin N → Fin N) (hout : Function.Bijective out)
    (hdisp : ∀ p, (out p).val ≤ p.val + E ∧ p.val ≤ (out p).val + E)
    (pi Ilo Ihi : Nat) (hmargin : pi / 2 ≤ N) :
    (((Finset.univ.filter fun (x : Fin N) => pi / 2 ≤
        ((Equiv.ofBijective out hout).symm x).val ∧
        ((Equiv.ofBijective out hout).symm x).val < N - pi / 2).filter
        fun (x : Fin N) => ¬ (Ilo ≤ (x : Nat) ∧ (x : Nat) < Ihi)).card : Real) ≤
      (((min ((Finset.univ.filter fun (x : Fin N) => Ihi ≤ (x : Nat)).card)
        ((Finset.univ.filter fun (x : Fin N) => Ihi ≤ (x : Nat)).card - pi / 2 + E) : Nat) : Real) +
       ((min ((Finset.univ.filter fun (x : Fin N) => (x : Nat) < Ilo).card)
        ((Finset.univ.filter fun (x : Fin N) => (x : Nat) < Ilo).card - pi / 2 + E) : Nat) : Real)) := by
  classical
  let pos : Fin N → Nat := fun x => ((Equiv.ofBijective out hout).symm x).val
  have hprefix : ∀ c, c ≤ N →
      (Finset.univ.filter fun x : Fin N => pos x < c).card = c := by
    intro c hc
    simpa [pos] using inverse_position_prefix_card out hout c hc
  have hcut : ∀ q c, q ≤ N → c ≤ N →
      countDistance
        ((Finset.univ.filter fun x : Fin N =>
          rankIn Finset.univ x < q ∧ pos x < c).card)
        (min q c) ≤ E := by
    intro q c hq hc
    have h := rank_cut_error_of_pointwise_displacement out hout hdisp q c hq hc
    simpa [pos, Chvatal.D2StaticWireSets.rankIn_univ_eq_val] using h
  have hmargin' : pi / 2 ≤ (Finset.univ : Finset (Fin N)).card := by
    simpa using hmargin
  have hprefix' : ∀ c, c ≤ (Finset.univ : Finset (Fin N)).card →
      ((Finset.univ : Finset (Fin N)).filter fun x => pos x < c).card = c := by
    intro c hc
    exact hprefix c (by simpa using hc)
  have hcut' : ∀ q c, q ≤ (Finset.univ : Finset (Fin N)).card →
      c ≤ (Finset.univ : Finset (Fin N)).card →
      countDistance
        (((Finset.univ : Finset (Fin N)).filter fun x =>
          rankIn Finset.univ x < q ∧ pos x < c).card)
        (min q c) ≤ E := by
    intro q c hq hc
    exact hcut q c (by simpa using hq) (by simpa using hc)
  simpa [pos] using sent_outside_le_of_rank_cut_error
    (Finset.univ : Finset (Fin N)) pos pi Ilo Ihi E hmargin' hprefix' hcut'

/-- The actual 4096-by-64 D2 local macro supplies the escape profile with
`E=832` for a rank-coded tile whose input columns satisfy the scheduled
descending-order precondition. -/
theorem d2_localCore_sent_outside_profile
    (v : Wire → Wire) (hbij : Function.Bijective v)
    (perm : Row → Equiv.Perm Col)
    (hdesc : ∀ (c : Col) (r s : Row), r.val ≤ s.val →
      (v (Chvatal.matrixWire 4096 64 s c)).val ≤
        (v (Chvatal.matrixWire 4096 64 r c)).val)
    (pi Ilo Ihi : Nat) (hmargin : pi / 2 ≤ 4096 * 64) :
    (((Finset.univ.filter fun (x : Wire) => pi / 2 ≤
        ((Equiv.ofBijective (localCore v perm)
          (localCore_bijective v hbij perm)).symm x).val ∧
        ((Equiv.ofBijective (localCore v perm)
          (localCore_bijective v hbij perm)).symm x).val < 4096 * 64 - pi / 2).filter
        fun (x : Wire) => ¬ (Ilo ≤ (x : Nat) ∧ (x : Nat) < Ihi)).card : Real) ≤
      (((min ((Finset.univ.filter fun (x : Wire) => Ihi ≤ (x : Nat)).card)
        ((Finset.univ.filter fun (x : Wire) => Ihi ≤ (x : Nat)).card - pi / 2 + 832) : Nat) : Real) +
       ((min ((Finset.univ.filter fun (x : Wire) => (x : Nat) < Ilo).card)
        ((Finset.univ.filter fun (x : Wire) => (x : Nat) < Ilo).card - pi / 2 + 832) : Nat) : Real)) := by
  exact sent_outside_le_of_pointwise_displacement
    (localCore v perm) (localCore_bijective v hbij perm)
    (localCore_rank_displacement v hbij perm hdesc)
    pi Ilo Ihi hmargin

end Chvatal.D2RankCutTail
