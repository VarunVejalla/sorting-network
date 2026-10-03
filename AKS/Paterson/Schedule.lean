module

public import AKS.Paterson.FastParams
public import AKS.Paterson.LatticeRounding

/-! # Conservation-based full-bag scheduling

At a nonempty level the ideal subtree content is its native interval width
minus its share of all ancestor bags and cold storage. Rounding this total
on a common lattice, rather than rounding each outgoing piece separately,
gives consistent bag sizes and fringes. Boundary clipping and forest root
splitting are separate from the full-bag identities proved here.
Source: Paterson (1990), Sections 5 and 7.
-/

@[expose] public section

namespace Paterson.Bags

def ancestorReserve (p : Params) (cap : ℚ) : ℚ := cap / (4 * p.A ^ 2 - 1)

def idealSubtree (p : Params) (width cap : ℚ) : ℚ :=
  max 0 (width - ancestorReserve p cap)

def scheduledSubtree (p : Params) (width cap : ℚ) : ℕ :=
  ceil32 (idealSubtree p width cap)

theorem reserve_denominator_pos (p : Params) : 0 < 4 * p.A ^ 2 - 1 := by
  nlinarith [p.A_gt_one, sq_nonneg (p.A - 1)]

/-- The full bag is precisely the difference of the subtree and its four
active granddaughter subtrees, before rounding. -/
theorem full_subtree_identity (p : Params) (width cap : ℚ) :
    width - ancestorReserve p cap =
      cap + 4 * (width / 4 - ancestorReserve p (p.A ^ 2 * cap)) := by
  unfold ancestorReserve
  field_simp [ne_of_gt (reserve_denominator_pos p)]
  ring

/-- The shrink recurrence is exactly the fringe-conservation identity. -/
theorem full_fringe_identity (p : Params) (width cap : ℚ) :
    (width - ancestorReserve p cap) / 2 -
      (width / 2 - ancestorReserve p (p.nu * p.A * cap)) = p.lambda * cap / 2 := by
  have h := p.capacity
  have hA : p.A ≠ 0 := by linarith [p.A_gt_one]
  have hcoeff : 2 * p.nu * p.A - 1 = p.lambda * (4 * p.A ^ 2 - 1) := by
    field_simp at h
    nlinarith
  unfold ancestorReserve
  field_simp [ne_of_gt (reserve_denominator_pos p)]
  linear_combination cap * hcoeff

def scheduledBag (p : Params) (width cap : ℚ) : ℕ :=
  scheduledSubtree p width cap - 4 * scheduledSubtree p (width / 4) (p.A ^ 2 * cap)

def scheduledFringe (p : Params) (width cap : ℚ) : ℕ :=
  scheduledSubtree p width cap / 2 -
    scheduledSubtree p (width / 2) (p.nu * p.A * cap)

theorem scheduledBag_dvd (p : Params) (width cap : ℚ) : 32 ∣ scheduledBag p width cap :=
  Nat.dvd_sub (ceil32_dvd _) (dvd_mul_of_dvd_right (ceil32_dvd _) 4)

theorem scheduledBag_full_bounds (p : Params) {width cap : ℚ}
    (hfull : 0 ≤ width / 4 - ancestorReserve p (p.A ^ 2 * cap))
    (hcap : 128 ≤ cap) :
    cap - 128 < (scheduledBag p width cap : ℚ) ∧
      (scheduledBag p width cap : ℚ) < cap + 32 := by
  have hiden := full_subtree_identity p width cap
  have ha : 0 ≤ width - ancestorReserve p cap := by linarith
  simp only [scheduledBag, scheduledSubtree, idealSubtree,
    max_eq_right ha, max_eq_right hfull]
  exact latticeBag_bounds hfull hiden hcap

/-- The actual lattice fringe covers the checked separator's n/32 fringe,
with the faster parameters and their checked capacity threshold. -/
theorem fast_scheduled_fringe_bounds {width cap : ℚ}
    (hfull : 0 ≤ width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap))
    (hcap : fastParams.minCapacity ≤ cap) :
    (scheduledBag fastParams width cap : ℚ) / 32 ≤
      (scheduledFringe fastParams width cap : ℚ) := by
  let a := width - ancestorReserve fastParams cap
  let g := width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap)
  let next := width / 2 - ancestorReserve fastParams (fastParams.nu * fastParams.A * cap)
  have hcap0 : 0 ≤ cap := fastParams.minCapacity_pos.le.trans hcap
  have hiden : a = cap + 4 * g := full_subtree_identity _ _ _
  have hfiden : a / 2 - next = fastParams.lambda * cap / 2 := full_fringe_identity _ _ _
  have ha : 0 ≤ a := by dsimp [a, g] at *; linarith
  have hn : 0 ≤ next := by
    norm_num [a, next, ancestorReserve, fastParams] at hfull ⊢
    linarith
  have hbag := (scheduledBag_full_bounds fastParams hfull
    (show 128 ≤ cap by norm_num [fastParams] at hcap; linarith)).2
  have ha' := le_ceil32 a
  have hn' := ceil32_lt_add hn
  have heven : 2 ∣ ceil32 a := dvd_trans (by norm_num) (ceil32_dvd a)
  have hhalf : (ceil32 a / 2 : ℕ) * 2 = ceil32 a := Nat.div_mul_cancel heven
  have hhalfQ : ((ceil32 a / 2 : ℕ) : ℚ) * 2 = ceil32 a := by exact_mod_cast hhalf
  have hdiff : ceil32 next ≤ ceil32 a / 2 := by
    have hQ : (ceil32 next : ℚ) ≤ (ceil32 a / 2 : ℕ) := by
      norm_num [fastParams] at hfiden hcap
      linarith
    exact_mod_cast hQ
  have haMax : idealSubtree fastParams width cap = a := max_eq_right ha
  have hnMax : idealSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) =
      next := max_eq_right hn
  simp only [scheduledFringe, scheduledSubtree, haMax, hnMax, Nat.cast_sub hdiff]
  norm_num [fastParams] at hcap hfiden
  linarith

/-- Exact outgoing middle and parent counts for a full rounded bag. -/
theorem fast_scheduled_routing {width cap : ℚ}
    (hfull : 0 ≤ width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap))
    (hcap : fastParams.minCapacity ≤ cap) :
    scheduledFringe fastParams width cap ≤ scheduledBag fastParams width cap / 2 ∧
      scheduledBag fastParams width cap / 2 - scheduledFringe fastParams width cap =
        scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) -
          2 * scheduledSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) ∧
      2 * scheduledFringe fastParams width cap =
        scheduledSubtree fastParams width cap -
          2 * scheduledSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) := by
  let a := width - ancestorReserve fastParams cap
  let g := width / 4 - ancestorReserve fastParams (fastParams.A ^ 2 * cap)
  let next := width / 2 - ancestorReserve fastParams (fastParams.nu * fastParams.A * cap)
  have hiden : a = cap + 4 * g := full_subtree_identity _ _ _
  have hfiden : a / 2 - next = fastParams.lambda * cap / 2 := full_fringe_identity _ _ _
  have hg : 0 ≤ g := hfull
  have hcap0 : 0 ≤ cap := fastParams.minCapacity_pos.le.trans hcap
  have hmid : next - 2 * g = (1 - fastParams.lambda) * cap / 2 := by
    linarith
  have ha : 0 ≤ a := by
    norm_num [fastParams] at hcap
    linarith
  have hn : 0 ≤ next := by
    have hprod := mul_nonneg (sub_nonneg.mpr fastParams.lambda_lt_one.le) hcap0
    linarith
  have haLow := le_ceil32 a
  have hgHigh := ceil32_lt_add hg
  have hnLow := le_ceil32 next
  have hnHigh := ceil32_lt_add hn
  have hsmall : 2 * ceil32 g ≤ ceil32 next := by
    have hQ : (2 : ℚ) * ceil32 g ≤ ceil32 next := by
      norm_num [fastParams] at hcap hfiden
      linarith
    exact_mod_cast hQ
  have hlarge : 2 * ceil32 next ≤ ceil32 a := by
    have hQ : (2 : ℚ) * ceil32 next ≤ ceil32 a := by
      norm_num [fastParams] at hcap hfiden
      linarith
    exact_mod_cast hQ
  have heven : 2 ∣ ceil32 a := dvd_trans (by norm_num) (ceil32_dvd a)
  have hhalf : 2 * (ceil32 a / 2) = ceil32 a := Nat.mul_div_cancel' heven
  have haMax : idealSubtree fastParams width cap = a := max_eq_right ha
  have hgMax : idealSubtree fastParams (width / 4) (fastParams.A ^ 2 * cap) = g :=
    max_eq_right hfull
  have hnMax : idealSubtree fastParams (width / 2) (fastParams.nu * fastParams.A * cap) =
      next := max_eq_right hn
  simp only [scheduledFringe, scheduledBag, scheduledSubtree, haMax, hgMax, hnMax]
  omega

/-- Incoming register counts telescope to the destination's prescribed bag
size. This uses coherent rounded subtree totals at two consecutive stages. -/
theorem lattice_destination_cardinality (next oldGrand newGrand : ℕ)
    (hparent : 2 * oldGrand ≤ next) (hchildren : 2 * newGrand ≤ oldGrand) :
    (next - 2 * oldGrand) + 2 * (oldGrand - 2 * newGrand) = next - 4 * newGrand := by
  omega

end Paterson.Bags
