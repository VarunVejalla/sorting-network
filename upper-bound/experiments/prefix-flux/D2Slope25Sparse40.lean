import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import AKS.Bitonic.Sorts
import AKS.Chvatal.ExecPlacement

set_option maxHeartbeats 0

namespace Chvatal.D2Slope25Sparse40

open scoped BigOperators

theorem exists_sorted_three {α : Type*} [LinearOrder α]
    (a b c : α) (P : α → Prop)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : P a) (hb : P b) (hc : P c) :
    ∃ i j k, i < j ∧ j < k ∧ P i ∧ P j ∧ P k := by
  rcases lt_trichotomy a b with hablt | habeq | habgt
  · rcases lt_trichotomy b c with hbclt | hbceq | hbcgt
    · exact ⟨a, b, c, hablt, hbclt, ha, hb, hc⟩
    · exact (hbc hbceq).elim
    · rcases lt_trichotomy a c with haclt | haceq | hacgt
      · exact ⟨a, c, b, haclt, hbcgt, ha, hc, hb⟩
      · exact (hac haceq).elim
      · exact ⟨c, a, b, hacgt, hablt, hc, ha, hb⟩
  · exact (hab habeq).elim
  · rcases lt_trichotomy a c with haclt | haceq | hacgt
    · exact ⟨b, a, c, habgt, haclt, hb, ha, hc⟩
    · exact (hac haceq).elim
    · rcases lt_trichotomy b c with hbclt | hbceq | hbcgt
      · exact ⟨b, c, a, hbclt, hacgt, hb, hc, ha⟩
      · exact (hbc hbceq).elim
      · exact ⟨c, b, a, hbcgt, habgt, hc, hb, ha⟩

abbrev Col := Fin 64

def forwardNeed (target start : Nat) : Nat :=
  (target + 64 - start % 64) % 64 + 1

theorem forwardNeed_start_mod (target start : Nat) :
    forwardNeed target start = forwardNeed target (start % 64) := by
  simp [forwardNeed]

theorem forwardNeed_le_two_classify (target start : Nat)
    (ht : target < 64) (h : forwardNeed target start ≤ 2) :
    (start % 64 = target ∧ forwardNeed target start = 1) ∨
      ((start % 64 + 1) % 64 = target ∧ forwardNeed target start = 2) := by
  have hval : (target + 64 - start % 64) % 64 + 1 ≤ 2 := by
    simpa [forwardNeed] using h
  have hs : start % 64 < 64 := Nat.mod_lt _ (by omega)
  have hrem : (target + 64 - start % 64) % 64 ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos ((target + 64 - start % 64) % 64) with hz | hp
  · left
    constructor
    · omega
    · simp [forwardNeed]
      omega
  · right
    have hone : (target + 64 - start % 64) % 64 = 1 := by omega
    constructor
    · omega
    · simp [forwardNeed]
      omega

def tripleMass (d e target : Nat) : Nat :=
  let a := forwardNeed target 0
  let b := forwardNeed target (25 * d)
  let c := forwardNeed target (25 * (d + e))
  max a (max b c) + d * max b c + e * c

theorem forwardNeed_shift (target start delta : Nat)
    (ht : target < 64) (hn : target + delta < 64)
    (hside : start % 64 ≤ target ∨ target + delta < start % 64) :
    forwardNeed (target + delta) start = forwardNeed target start + delta := by
  unfold forwardNeed
  rcases hside with hpassed | hunreached
  · have hstart : start % 64 < 64 := Nat.mod_lt _ (by omega)
    omega
  · have hcur : target < start % 64 := by omega
    have hstart : start % 64 < 64 := Nat.mod_lt _ (by omega)
    have hmod₁ : (target + 64 - start % 64) % 64 =
        target + 64 - start % 64 := Nat.mod_eq_of_lt (by omega)
    have hmod₂ : (target + delta + 64 - start % 64) % 64 =
        target + delta + 64 - start % 64 := Nat.mod_eq_of_lt (by omega)
    rw [hmod₁, hmod₂]
    omega

theorem forwardNeed_translate (target shift start : Nat)
    (ht : target < 64) (hs : shift < 64) :
    forwardNeed target (shift + start) =
      forwardNeed ((target + 64 - shift) % 64) start := by
  unfold forwardNeed
  omega

theorem max_shift (a b delta : Nat) :
    max (a + delta) (b + delta) = max a b + delta := by
  by_cases hab : a ≤ b
  · simp [max_eq_right hab, max_eq_right (Nat.add_le_add_right hab delta)]
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    simp [max_eq_left hba, max_eq_left (Nat.add_le_add_right hba delta)]

theorem tripleMass_shift (d e target delta : Nat)
    (ht : target < 64) (hn : target + delta < 64)
    (h1 : (25 * d) % 64 ≤ target ∨ target + delta < (25 * d) % 64)
    (h2 : (25 * (d + e)) % 64 ≤ target ∨
      target + delta < (25 * (d + e)) % 64) :
    tripleMass d e (target + delta) =
      tripleMass d e target + delta * (1 + d + e) := by
  unfold tripleMass
  dsimp only
  have h0 : 0 % 64 ≤ target := by omega
  rw [forwardNeed_shift target 0 delta ht hn (Or.inl h0),
    forwardNeed_shift target (25 * d) delta ht hn h1,
    forwardNeed_shift target (25 * (d + e)) delta ht hn h2]
  rw [max_shift, max_shift]
  ring

/-- The finite modular cases at the three row-start targets. -/
theorem tripleMass_ge_41_at_starts :
    ∀ d e : Col,
      0 < d.val → 0 < e.val → d.val + e.val < 64 →
        41 ≤ tripleMass d.val e.val 0 ∧
        41 ≤ tripleMass d.val e.val (25 * d.val % 64) ∧
        41 ≤ tripleMass d.val e.val (25 * (d.val + e.val) % 64) := by
  decide

theorem stride25_gap_one :
    ∀ gap : Col, 0 < gap.val → 25 * gap.val % 64 = 1 → gap.val = 41 := by
  decide

theorem stride25_gap_minus_one :
    ∀ gap : Col, 0 < gap.val → 25 * gap.val % 64 = 63 → gap.val = 23 := by
  decide

theorem stride25_nonzero :
    ∀ n : Col, 0 < n.val → 0 < 25 * n.val % 64 := by
  decide

theorem stride25_injective :
    ∀ a b : Col, 25 * a.val % 64 = 25 * b.val % 64 → a = b := by
  decide

theorem adjacent_stride25_row_gaps :
    ∀ i j : Col, i.val < j.val →
      ((25 * i.val % 64 + 1) % 64 = 25 * j.val % 64 → j.val - i.val = 41) ∧
      ((25 * j.val % 64 + 1) % 64 = 25 * i.val % 64 → j.val - i.val = 23) := by
  decide

/-- The minimum triple-collision mass occurs at a row start, so it is at least
41 for every target column. -/
theorem tripleMass_ge_41 (d e target : Col)
    (hd : 0 < d.val) (he : 0 < e.val) (hde : d.val + e.val < 64) :
    41 ≤ tripleMass d.val e.val target.val := by
  have hstarts := tripleMass_ge_41_at_starts d e hd he hde
  rcases hstarts with ⟨hzero, hpBound, hqBound⟩
  let p := 25 * d.val % 64
  let q := 25 * (d.val + e.val) % 64
  have hpVal : 0 < 25 * d.val % 64 :=
    stride25_nonzero ⟨d.val, by omega⟩ hd
  have hsumPos : 0 < d.val + e.val := by omega
  have hsumStride : 0 < 25 * (⟨d.val + e.val, hde⟩ : Col).val % 64 :=
    stride25_nonzero ⟨d.val + e.val, hde⟩ hsumPos
  have hqVal : 0 < 25 * (d.val + e.val) % 64 := by
    simpa using hsumStride
  have hp : 0 < p := by simpa [p] using hpVal
  have hq : 0 < q := by simpa [q] using hqVal
  have hpq : p ≠ q := by
    intro heq
    change 25 * d.val % 64 = 25 * (d.val + e.val) % 64 at heq
    have hinj := stride25_injective ⟨d.val, by omega⟩
      ⟨d.val + e.val, hde⟩ heq
    have hval : d.val = d.val + e.val := by
      simpa using congrArg Fin.val hinj
    omega
  by_cases hpqOrder : p < q
  · by_cases hx : target.val < p
    · have hshift := tripleMass_shift d.val e.val 0 target.val
        (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      have hshift' : tripleMass d.val e.val target.val =
          tripleMass d.val e.val 0 + target.val * (1 + d.val + e.val) := by
        simpa using hshift
      have hbase : 41 ≤ tripleMass d.val e.val 0 := hzero
      omega
    · by_cases hxq : target.val < q
      · have htarget : p + (target.val - p) = target.val := by omega
        have hNoWrap : p + (target.val - p) < q := by rw [htarget]; exact hxq
        have hshift := tripleMass_shift d.val e.val p (target.val - p)
          (by omega) (by omega) (Or.inl (by omega)) (Or.inr hNoWrap)
        rw [htarget] at hshift
        have hbase : 41 ≤ tripleMass d.val e.val p := by simpa [p] using hpBound
        omega

      · have htarget : q + (target.val - q) = target.val := by omega
        have hshift := tripleMass_shift d.val e.val q (target.val - q)
          (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        rw [htarget] at hshift
        have hbase : 41 ≤ tripleMass d.val e.val q := by simpa [q] using hqBound
        omega
  · have hqp : q < p := by omega
    by_cases hx : target.val < q
    · have hshift := tripleMass_shift d.val e.val 0 target.val
        (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      have hshift' : tripleMass d.val e.val target.val =
          tripleMass d.val e.val 0 + target.val * (1 + d.val + e.val) := by
        simpa using hshift
      have hbase : 41 ≤ tripleMass d.val e.val 0 := hzero
      omega
    · by_cases hxp : target.val < p
      · have htarget : q + (target.val - q) = target.val := by omega
        have hNoWrap : q + (target.val - q) < p := by rw [htarget]; exact hxp
        have hshift := tripleMass_shift d.val e.val q (target.val - q)
          (by omega) (by omega) (Or.inr hNoWrap) (Or.inl (by omega))
        rw [htarget] at hshift
        have hbase : 41 ≤ tripleMass d.val e.val q := by simpa [q] using hqBound
        omega
      · have htarget : p + (target.val - p) = target.val := by omega
        have hshift := tripleMass_shift d.val e.val p (target.val - p)
          (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        rw [htarget] at hshift
        have hbase : 41 ≤ tripleMass d.val e.val p := by simpa [p] using hpBound
        omega

theorem profileMass_ge_three_blocks
    (profile : Col → Nat) (i j k : Col) (A B C : Nat)
    (hij : i.val < j.val)
    (hA : ∀ r, r.val ≤ i.val → A ≤ profile r)
    (hB : ∀ r, i.val < r.val → r.val ≤ j.val → B ≤ profile r)
    (hC : ∀ r, j.val < r.val → r.val ≤ k.val → C ≤ profile r) :
    A * (i.val + 1) + B * (j.val - i.val) + C * (k.val - j.val) ≤
      ∑ r : Col, profile r := by
  let s₁ : Finset Col := Finset.Iic i
  let s₂ : Finset Col := Finset.Ioc i j
  let s₃ : Finset Col := Finset.Ioc j k
  have hdisj12 : Disjoint s₁ s₂ := by
    rw [Finset.disjoint_left]
    intro r hr₁ hr₂
    have hr₁' : r ≤ i := by simpa [s₁] using hr₁
    have hr₂' : i < r ∧ r ≤ j := by simpa [s₂] using hr₂
    have h₁ : r.val ≤ i.val := by simpa using hr₁'
    have h₂ : i.val < r.val := by simpa using hr₂'.1
    omega
  have hdisj123 : Disjoint (s₁ ∪ s₂) s₃ := by
    rw [Finset.disjoint_left]
    intro r hr hr₃
    simp only [Finset.mem_union] at hr
    have hr₃' : j < r ∧ r ≤ k := by simpa [s₃] using hr₃
    rcases hr with hr₁ | hr₂
    · have hr₁' : r ≤ i := by simpa [s₁] using hr₁
      have h₁ : r.val ≤ i.val := by simpa using hr₁'
      have h₂ : i.val < j.val := hij
      have h₃ : j.val < r.val := by simpa using hr₃'.1
      omega
    · have hr₂' : i < r ∧ r ≤ j := by simpa [s₂] using hr₂
      have h₁ : r.val ≤ j.val := by simpa using hr₂'.2
      have h₂ : j.val < r.val := by simpa using hr₃'.1
      omega
  have hsubset : s₁ ∪ s₂ ∪ s₃ ⊆ Finset.univ := by
    intro r hr
    simp
  have htotal := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r hr hnot => Nat.zero_le (profile r))
  have hsum₁ : (∑ r ∈ s₁, A) ≤ ∑ r ∈ s₁, profile r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hA r (by simpa [s₁, Finset.mem_Iic] using hr)
  have hsum₂ : (∑ r ∈ s₂, B) ≤ ∑ r ∈ s₂, profile r := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' : i.val < r.val ∧ r.val ≤ j.val :=
      by simpa [s₂, Finset.mem_Ioc] using hr
    exact hB r hr'.1 hr'.2
  have hsum₃ : (∑ r ∈ s₃, C) ≤ ∑ r ∈ s₃, profile r := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' : j.val < r.val ∧ r.val ≤ k.val :=
      by simpa [s₃, Finset.mem_Ioc] using hr
    exact hC r hr'.1 hr'.2
  have hconst₁ : (∑ _r ∈ s₁, A) = A * (i.val + 1) := by
    simp [s₁, Nat.mul_comm]
  have hconst₂ : (∑ _r ∈ s₂, B) = B * (j.val - i.val) := by
    simp [s₂, Nat.mul_comm]
  have hconst₃ : (∑ _r ∈ s₃, C) = C * (k.val - j.val) := by
    simp [s₃, Nat.mul_comm]
  rw [Finset.sum_union hdisj123, Finset.sum_union hdisj12] at htotal
  have hparts :
      (∑ r ∈ s₁, A) + (∑ r ∈ s₂, B) + (∑ r ∈ s₃, C) ≤
        (∑ r ∈ s₁, profile r) + (∑ r ∈ s₂, profile r) +
          (∑ r ∈ s₃, profile r) := by
    simpa [add_assoc] using add_le_add hsum₁ (add_le_add hsum₂ hsum₃)
  rw [hconst₁, hconst₂, hconst₃] at hparts
  exact hparts.trans htotal

theorem profileMass_ge_triple_hits
    (profile : Col → Nat) (i j k : Col) (a b c : Nat)
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hai : a ≤ profile i) (hbj : b ≤ profile j) (hck : c ≤ profile k) :
    max a (max b c) * (i.val + 1) +
      max b c * (j.val - i.val) + c * (k.val - j.val) ≤
        ∑ r : Col, profile r := by
  apply profileMass_ge_three_blocks profile i j k
    (max a (max b c)) (max b c) c hij
  · intro r hr
    have hai' : a ≤ profile r := le_trans hai (hmono r i hr)
    have hbj' : b ≤ profile r := by
      apply le_trans hbj
      apply hmono r j
      omega
    have hck' : c ≤ profile r := by
      apply le_trans hck
      apply hmono r k
      omega
    exact max_le hai' (max_le hbj' hck')
  · intro r hleft hright
    have hbj' : b ≤ profile r := le_trans hbj (hmono r j (by omega))
    have hck' : c ≤ profile r := le_trans hck (hmono r k (by omega))
    exact max_le hbj' hck'
  · intro r hleft hright
    exact le_trans hck (hmono r k (by omega))

theorem profileMass_ge_prefix
    (profile : Col → Nat) (i : Col) (A : Nat)
    (hA : ∀ r, r.val ≤ i.val → A ≤ profile r) :
    A * (i.val + 1) ≤ ∑ r : Col, profile r := by
  let s : Finset Col := Finset.Iic i
  have hsubset : s ⊆ Finset.univ := by intro r hr; simp
  have htotal := Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun r hr hnot => Nat.zero_le (profile r))
  have hsum : (∑ r ∈ s, A) ≤ ∑ r ∈ s, profile r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hA r (by simpa [s] using hr)
  have hconst : (∑ _r ∈ s, A) = A * (i.val + 1) := by
    simp [s, Nat.mul_comm]
  rw [hconst] at hsum
  exact hsum.trans htotal

theorem profileMass_ge_41_of_three_hits
    (profile : Col → Nat) (i j k target : Col)
    (hij : i.val < j.val) (hjk : j.val < k.val)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hi : forwardNeed target.val (25 * i.val) ≤ profile i)
    (hj : forwardNeed target.val (25 * j.val) ≤ profile j)
    (hk : forwardNeed target.val (25 * k.val) ≤ profile k) :
    41 ≤ ∑ r : Col, profile r := by
  let d := j.val - i.val
  let e := k.val - j.val
  let shift := 25 * i.val % 64
  let target' := (target.val + 64 - shift) % 64
  have hd : 0 < d := by dsimp [d]; omega
  have he : 0 < e := by dsimp [e]; omega
  have hde : d + e < 64 := by dsimp [d, e]; omega
  have hshiftlt : shift < 64 := by dsimp [shift]; exact Nat.mod_lt _ (by omega)
  have htarget' : target' < 64 := by dsimp [target']; exact Nat.mod_lt _ (by omega)
  have hival : j.val = i.val + d := by dsimp [d]; omega
  have hkval : k.val = i.val + d + e := by dsimp [d, e]; omega
  have hstartj : (25 * j.val) % 64 = (shift + 25 * d) % 64 := by
    dsimp [shift, d]
    omega
  have hstartk : (25 * k.val) % 64 = (shift + 25 * (d + e)) % 64 := by
    dsimp [shift, d, e]
    omega
  have hreqi : forwardNeed target.val (25 * i.val) = forwardNeed target' 0 := by
    calc
      forwardNeed target.val (25 * i.val) = forwardNeed target.val shift := by
        simpa [shift] using forwardNeed_start_mod target.val (25 * i.val)
      _ = forwardNeed target' 0 := by
        have h := forwardNeed_translate target.val shift 0 target.isLt hshiftlt
        simpa [target', shift] using h
  have hreqj : forwardNeed target.val (25 * j.val) =
      forwardNeed target' (25 * d) := by
    calc
      forwardNeed target.val (25 * j.val) =
          forwardNeed target.val ((25 * j.val) % 64) :=
        forwardNeed_start_mod target.val (25 * j.val)
      _ = forwardNeed target.val ((shift + 25 * d) % 64) := by rw [hstartj]
      _ = forwardNeed target.val (shift + 25 * d) :=
        (forwardNeed_start_mod target.val (shift + 25 * d)).symm
      _ = forwardNeed target' (25 * d) := by
        have h := forwardNeed_translate target.val shift (25 * d)
          target.isLt hshiftlt
        simpa [target', shift] using h
  have hreqk : forwardNeed target.val (25 * k.val) =
      forwardNeed target' (25 * (d + e)) := by
    calc
      forwardNeed target.val (25 * k.val) =
          forwardNeed target.val ((25 * k.val) % 64) :=
        forwardNeed_start_mod target.val (25 * k.val)
      _ = forwardNeed target.val ((shift + 25 * (d + e)) % 64) := by rw [hstartk]
      _ = forwardNeed target.val (shift + 25 * (d + e)) :=
        (forwardNeed_start_mod target.val (shift + 25 * (d + e))).symm
      _ = forwardNeed target' (25 * (d + e)) := by
        have h := forwardNeed_translate target.val shift (25 * (d + e))
          target.isLt hshiftlt
        simpa [target', shift] using h
  have htriple := tripleMass_ge_41 ⟨d, by omega⟩ ⟨e, by omega⟩
    ⟨target', htarget'⟩ hd he hde
  have hprofile := profileMass_ge_triple_hits profile i j k
    (forwardNeed target.val (25 * i.val))
    (forwardNeed target.val (25 * j.val))
    (forwardNeed target.val (25 * k.val)) hij hjk hmono hi hj hk
  rw [hreqi, hreqj, hreqk] at hprofile
  dsimp [tripleMass] at htriple
  have hlarge :
      max (forwardNeed target' 0)
          (max (forwardNeed target' (25 * d))
            (forwardNeed target' (25 * (d + e)))) +
        d * max (forwardNeed target' (25 * d))
          (forwardNeed target' (25 * (d + e))) +
        e * forwardNeed target' (25 * (d + e)) ≤
      max (forwardNeed target' 0)
          (max (forwardNeed target' (25 * d))
            (forwardNeed target' (25 * (d + e)))) * (i.val + 1) +
        max (forwardNeed target' (25 * d))
          (forwardNeed target' (25 * (d + e))) * d +
        forwardNeed target' (25 * (d + e)) * e := by
    let A := max (forwardNeed target' 0)
      (max (forwardNeed target' (25 * d))
        (forwardNeed target' (25 * (d + e))))
    let B := max (forwardNeed target' (25 * d))
      (forwardNeed target' (25 * (d + e)))
    let C := forwardNeed target' (25 * (d + e))
    have hfactor : 1 ≤ i.val + 1 := by omega
    have hA : A ≤ A * (i.val + 1) := by
      calc
        A = A * 1 := by omega
        _ ≤ A * (i.val + 1) := Nat.mul_le_mul_left A hfactor
    change A + d * B + e * C ≤ A * (i.val + 1) + B * d + C * e
    calc
      A + d * B + e * C ≤ A * (i.val + 1) + d * B + e * C := by omega
      _ = A * (i.val + 1) + B * d + C * e := by ring
  have htriple' : 41 ≤
      max (forwardNeed target' 0)
          (max (forwardNeed target' (25 * d))
            (forwardNeed target' (25 * (d + e)))) +
        d * max (forwardNeed target' (25 * d))
          (forwardNeed target' (25 * (d + e))) +
        e * forwardNeed target' (25 * (d + e)) := by
    simpa [tripleMass] using htriple
  have hprofile' :
      max (forwardNeed target' 0)
          (max (forwardNeed target' (25 * d))
            (forwardNeed target' (25 * (d + e)))) * (i.val + 1) +
        max (forwardNeed target' (25 * d))
          (forwardNeed target' (25 * (d + e))) * d +
        forwardNeed target' (25 * (d + e)) * e ≤
      ∑ r : Col, profile r := by
    simpa [d, e] using hprofile
  exact htriple'.trans (hlarge.trans hprofile')

theorem slope25_first_pass_max_load_le_two
    (profile : Col → Nat) (target : Col)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40) :
    (Finset.univ.filter fun r : Col =>
      forwardNeed target.val (25 * r.val) ≤ profile r).card ≤ 2 := by
  classical
  let hitRows := Finset.univ.filter fun r : Col =>
    forwardNeed target.val (25 * r.val) ≤ profile r
  by_contra hcard
  have hlarge : 2 < hitRows.card := by
    dsimp [hitRows] at hcard ⊢
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card.mp hlarge
  have hPa : forwardNeed target.val (25 * a.val) ≤ profile a := by
    simpa [hitRows] using ha
  have hPb : forwardNeed target.val (25 * b.val) ≤ profile b := by
    simpa [hitRows] using hb
  have hPc : forwardNeed target.val (25 * c.val) ≤ profile c := by
    simpa [hitRows] using hc
  obtain ⟨i, j, k, hij, hjk, hPi, hPj, hPk⟩ :=
    exists_sorted_three a b c
      (fun r : Col => forwardNeed target.val (25 * r.val) ≤ profile r)
      hab hac hbc hPa hPb hPc
  have hijv : i.val < j.val := by simpa using hij
  have hjkv : j.val < k.val := by simpa using hjk
  have hmass41 := profileMass_ge_41_of_three_hits
    profile i j k target hijv hjkv hmono hPi hPj hPk
  omega

theorem slope25_second_pass_max_load_le_one
    (profile : Col → Nat) (target : Col)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hheight : ∀ r, profile r ≤ 2) :
    (Finset.univ.filter fun r : Col =>
      forwardNeed target.val (25 * r.val) ≤ profile r).card ≤ 1 := by
  classical
  let hitRows := Finset.univ.filter fun r : Col =>
    forwardNeed target.val (25 * r.val) ≤ profile r
  have noPair : ∀ i j : Col, i.val < j.val →
      forwardNeed target.val (25 * i.val) ≤ profile i →
      forwardNeed target.val (25 * j.val) ≤ profile j → False := by
    intro i j hij hi hj
    have hi2 : forwardNeed target.val (25 * i.val) ≤ 2 :=
      hi.trans (hheight i)
    have hj2 : forwardNeed target.val (25 * j.val) ≤ 2 :=
      hj.trans (hheight j)
    have hci := forwardNeed_le_two_classify target.val (25 * i.val)
      target.isLt hi2
    have hcj := forwardNeed_le_two_classify target.val (25 * j.val)
      target.isLt hj2
    rcases hci with ⟨hiAt, hiOne⟩ | ⟨hiPrev, hiTwo⟩
    · rcases hcj with ⟨hjAt, hjOne⟩ | ⟨hjPrev, hjTwo⟩
      · have hstart : 25 * i.val % 64 = 25 * j.val % 64 := by omega
        have heq := stride25_injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hstart
        have hval := congrArg Fin.val heq
        omega
      · have hgap :
            (25 * j.val % 64 + 1) % 64 = 25 * i.val % 64 := by omega
        have hdist := (adjacent_stride25_row_gaps i j hij).2 hgap
        have hjlarge : 2 ≤ profile j := by omega
        have hprefix := profileMass_ge_prefix profile j 2 (by
          intro r hr
          exact le_trans hjlarge (hmono r j hr))
        omega
    · rcases hcj with ⟨hjAt, hjOne⟩ | ⟨hjPrev, hjTwo⟩
      · have hgap :
            (25 * i.val % 64 + 1) % 64 = 25 * j.val % 64 := by omega
        have hdist := (adjacent_stride25_row_gaps i j hij).1 hgap
        have hilarge : 2 ≤ profile i := by omega
        have hjlarge : 1 ≤ profile j := by omega
        have hblocks := profileMass_ge_three_blocks profile i j j 2 1 0 hij
          (by
            intro r hr
            exact le_trans hilarge (hmono r i hr))
          (by
            intro r hleft hright
            have hmono' := hmono r j hright
            exact le_trans hjlarge hmono')
          (by
            intro r hleft hright
            omega)
        omega
      · have hstart : 25 * i.val % 64 = 25 * j.val % 64 := by
          have hsi : 25 * i.val % 64 < 64 := Nat.mod_lt _ (by omega)
          have hsj : 25 * j.val % 64 < 64 := Nat.mod_lt _ (by omega)
          omega
        have heq := stride25_injective ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hstart
        have hval := congrArg Fin.val heq
        omega
  by_contra hcard
  have hlarge : 1 < hitRows.card := by
    dsimp [hitRows] at hcard ⊢
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
  have hPa : forwardNeed target.val (25 * a.val) ≤ profile a := by
    simpa [hitRows] using ha
  have hPb : forwardNeed target.val (25 * b.val) ≤ profile b := by
    simpa [hitRows] using hb
  have habval : a.val ≠ b.val := by
    intro heq
    exact hab (Fin.ext heq)
  by_cases hablt : a.val < b.val
  · exact noPair a b hablt hPa hPb
  · have hblt : b.val < a.val := by omega
    exact noPair b a hblt hPb hPa

private def reflectCol (r : Col) : Col :=
  ⟨63 - r.val, by omega⟩

private def reflectColEquiv : Col ≃ Col where
  toFun := reflectCol
  invFun := reflectCol
  left_inv := by
    intro r
    apply Fin.ext
    simp [reflectCol]
    omega
  right_inv := by
    intro r
    apply Fin.ext
    simp [reflectCol]
    omega

private def shiftTarget39 (target : Col) : Col :=
  ⟨(target.val + 39) % 64, Nat.mod_lt _ (by omega)⟩

/-- Reflecting row order turns stride 39 into stride 25, up to a fixed
translation of the target column. -/
private theorem forwardNeed_reflect39 (target row : Col) :
    forwardNeed target.val (39 * row.val) =
      forwardNeed (shiftTarget39 target).val (25 * (reflectCol row).val) := by
  simp [forwardNeed, shiftTarget39, reflectCol]
  omega

/-- The sparse one-hit gate also holds for an increasing profile if the next
shuffle uses stride 39. Reverse the row order: the profile becomes decreasing,
and the stride becomes 25 after translating the target by 39. This lets the
intervening sorter stay in the standard ascending comparator convention. -/
theorem slope39_second_pass_max_load_le_one_of_monotone
    (profile : Col → Nat) (target : Col)
    (hmono : ∀ r s, r.val ≤ s.val → profile r ≤ profile s)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hheight : ∀ r, profile r ≤ 2) :
    (Finset.univ.filter fun r : Col =>
      forwardNeed target.val (39 * r.val) ≤ profile r).card ≤ 1 := by
  let reflected : Col → Nat := fun r => profile (reflectCol r)
  have hmonoRef : ∀ r s, r.val ≤ s.val → reflected s ≤ reflected r := by
    intro r s hrs
    dsimp [reflected]
    apply hmono
    simp only [reflectCol]
    omega
  have hmassRef : (∑ r : Col, reflected r) = ∑ r : Col, profile r := by
    dsimp [reflected]
    exact Equiv.sum_comp reflectColEquiv profile
  have hheightRef : ∀ r, reflected r ≤ 2 := fun r => hheight (reflectCol r)
  have hgate := slope25_second_pass_max_load_le_one reflected
    (shiftTarget39 target) hmonoRef (by rw [hmassRef]; exact hmass) hheightRef
  have hcard :
      (Finset.univ.filter fun r : Col =>
        forwardNeed target.val (39 * r.val) ≤ profile r).card =
      (Finset.univ.filter fun r : Col =>
        forwardNeed (shiftTarget39 target).val (25 * r.val) ≤ reflected r).card := by
    apply Finset.card_bij
      (s := Finset.univ.filter fun r : Col =>
        forwardNeed target.val (39 * r.val) ≤ profile r)
      (t := Finset.univ.filter fun r : Col =>
        forwardNeed (shiftTarget39 target).val (25 * r.val) ≤ reflected r)
      (fun r _ => reflectCol r)
    · intro r hr
      have hr' := (Finset.mem_filter.mp hr).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← forwardNeed_reflect39 target r]
      have hrr : reflectCol (reflectCol r) = r :=
        reflectColEquiv.symm_apply_apply r
      dsimp [reflected]
      rw [hrr]
      exact hr'
    · intro r hr s hs heq
      exact reflectColEquiv.injective heq
    · intro s hs
      have hs' := (Finset.mem_filter.mp hs).2
      refine ⟨reflectCol s, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [forwardNeed_reflect39 target (reflectCol s)]
        have hrr : reflectCol (reflectCol s) = s :=
          reflectColEquiv.symm_apply_apply s
        rw [hrr]
        exact hs'
      · exact reflectColEquiv.symm_apply_apply s
  rw [hcard]
  exact hgate

/-- Number of first-pass rows which contribute a one to a destination column.
This is the actual load vector that the intervening column sort must order. -/
def slope25Load (profile : Col → Nat) (target : Col) : Nat :=
  (Finset.univ.filter fun r : Col =>
    forwardNeed target.val (25 * r.val) ≤ profile r).card

private def distanceFromStart (start target : Col) : Col :=
  ⟨(target.val + 64 - start.val) % 64, Nat.mod_lt _ (by omega)⟩

private def distanceFromStartEquiv (start : Col) : Col ≃ Col where
  toFun := distanceFromStart start
  invFun := fun distance =>
    ⟨(distance.val + start.val) % 64, Nat.mod_lt _ (by omega)⟩
  left_inv := by
    intro target
    apply Fin.ext
    simp [distanceFromStart]
    omega
  right_inv := by
    intro distance
    apply Fin.ext
    simp [distanceFromStart]
    omega

private theorem forwardNeed_eq_distance_add_one (start target : Col) :
    forwardNeed target.val start.val = (distanceFromStart start target).val + 1 := by
  simp [forwardNeed, distanceFromStart]
  omega

private theorem card_lt_64 (k : Nat) (hk : k ≤ 64) :
    (Finset.univ.filter fun i : Col => i.val < k).card = k := by
  calc
    (Finset.univ.filter fun i : Col => i.val < k).card =
        (Finset.Ico 0 k).card := by
      apply Finset.card_bij (s := Finset.univ.filter fun i : Col => i.val < k)
        (t := Finset.Ico 0 k) (fun i _ => i.val)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, hi⟩
      · intro i hi j hj hij
        exact Fin.ext hij
      · intro x hx
        have hx' := Finset.mem_Ico.mp hx
        let i : Col := ⟨x, lt_of_lt_of_le hx'.2 hk⟩
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'.2⟩, rfl⟩
    _ = k := by simp

private theorem forwardNeed_count (start : Col) (k : Nat) (hk : k ≤ 64) :
    (∑ target : Col,
      if forwardNeed target.val start.val ≤ k then 1 else 0) = k := by
  let e := distanceFromStartEquiv start
  calc
    (∑ target : Col,
      if forwardNeed target.val start.val ≤ k then 1 else 0) =
        ∑ target : Col, if (e target).val < k then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro target _
          rw [forwardNeed_eq_distance_add_one]
          change (if (distanceFromStart start target).val + 1 ≤ k then 1 else 0) =
            (if (distanceFromStart start target).val < k then 1 else 0)
          by_cases h : (distanceFromStart start target).val < k <;> simp [h] <;> omega
    _ = ∑ d : Col, if d.val < k then 1 else 0 := by
          exact Equiv.sum_comp e (fun d : Col => if d.val < k then 1 else 0)
    _ = k := by
          rw [Finset.sum_boole]
          exact card_lt_64 k hk

/-- The row permutation conserves all occupied cells: summing the raw loads
over output columns gives the input profile's mass exactly. -/
theorem slope25Load_sum_eq_profile_sum (profile : Col → Nat)
    (hbound : ∀ r, profile r ≤ 64) :
    (∑ target : Col, slope25Load profile target) = ∑ r : Col, profile r := by
  unfold slope25Load
  calc
    (∑ target : Col,
        (Finset.univ.filter fun r : Col =>
          forwardNeed target.val (25 * r.val) ≤ profile r).card) =
      ∑ target : Col, ∑ r : Col,
        if forwardNeed target.val (25 * r.val) ≤ profile r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.card_filter]
    _ = ∑ r : Col, ∑ target : Col,
        if forwardNeed target.val (25 * r.val) ≤ profile r then 1 else 0 := by
          exact Finset.sum_comm
    _ =
      ∑ r : Col, profile r := by
        apply Finset.sum_congr rfl
        intro r _
        let start : Col := ⟨(25 * r.val) % 64, Nat.mod_lt _ (by omega)⟩
        have hcount := forwardNeed_count start (profile r) (hbound r)
        simpa [start, forwardNeed_start_mod] using hcount

/-- Composition interface for two slope-25 passes. The first pass's sparse
gate bounds every raw column load by two. If the column sorter presents those
loads in nonincreasing order and preserves their total mass, the second pass
has at most one hit in every destination column. -/
theorem slope25_two_pass_no_collision_of_sorted_permutation
    (profile : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hbound : ∀ r, profile r ≤ 64)
    (sort : Col ≃ Col)
    (sortedMono : ∀ r s, r.val ≤ s.val →
      slope25Load profile (sort s) ≤ slope25Load profile (sort r)) :
    ∀ target : Col,
      (Finset.univ.filter fun r : Col =>
        forwardNeed target.val (25 * r.val) ≤ slope25Load profile (sort r)).card ≤ 1 := by
  intro target
  apply slope25_second_pass_max_load_le_one
    (fun r => slope25Load profile (sort r)) target sortedMono
  · calc
      (∑ r : Col, slope25Load profile (sort r))
          = ∑ c : Col, slope25Load profile c := by
              exact Equiv.sum_comp sort (fun c => slope25Load profile c)
      _ ≤ 40 := by
        rw [slope25Load_sum_eq_profile_sum profile hbound]
        exact hmass
  · intro r
    have hfirst := slope25_first_pass_max_load_le_two profile (sort r) hmono hmass
    simpa [slope25Load] using hfirst

/-- The abstract sort contract above is supplied by Batcher's 64-wire
bitonic network, interpreted in the dual order so that scalar loads are
descending. This proves the scalar comparator-network statement; realizing
that dual-order execution as a flattened Boolean bundle network is a separate
physical obligation. -/
theorem slope25_two_pass_no_collision_bitonic64
    (profile : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hbound : ∀ r, profile r ≤ 64) :
    ∀ target : Col,
      (Finset.univ.filter fun r : Col =>
        forwardNeed target.val (25 * r.val) ≤
          OrderDual.ofDual ((Bitonic.bitonicSort 6).exec
            (fun c : Col => (slope25Load profile c : OrderDual Nat)) r)).card ≤ 1 := by
  let input : Col → OrderDual Nat := fun c => slope25Load profile c
  let net := Bitonic.bitonicSort 6
  have hsorted : Monotone (net.exec input) := by
    exact (Bitonic.bitonicSort_sorts 6) (OrderDual Nat) input
  obtain ⟨sort, hperm⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm net input
  have hvalue (c : Col) : net.exec input c = slope25Load profile (sort c) := by
    have h := congrFun hperm c
    simpa [input, Function.comp] using h
  have hmonoSorted : ∀ r s, r.val ≤ s.val →
      slope25Load profile (sort s) ≤ slope25Load profile (sort r) := by
    intro r s hrs
    have h := hsorted hrs
    rw [hvalue r, hvalue s] at h
    exact h
  have hgate := slope25_two_pass_no_collision_of_sorted_permutation
    profile hmono hmass hbound sort hmonoSorted
  intro target
  have h := hgate target
  simpa [net, input, hvalue] using h

/-- Any standard ascending 64-wire sorting network followed by a stride-39 shuffle
closes the sparse two-pass gate. The first stride-25 shuffle has loads at most
two; sorting those loads ascending makes an increasing profile, and the
reflection lemma proves the stride-39 pass has no collisions. -/
theorem slope25_then_ascending_sort_stride39_no_collision
    (net : ComparatorNetwork 64)
    (hsorts : ∀ v : Col → Nat, Monotone (net.exec v))
    (profile : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hbound : ∀ r, profile r ≤ 64) :
    ∀ target : Col,
      (Finset.univ.filter fun r : Col =>
        forwardNeed target.val (39 * r.val) ≤
          net.exec (slope25Load profile) r).card ≤ 1 := by
  let raw := slope25Load profile
  have hsorted : Monotone (net.exec raw) := by
    exact hsorts raw
  obtain ⟨sort, hperm⟩ := Chvatal.ComparatorNetwork.exec_eq_comp_perm net raw
  have hvalue (r : Col) : net.exec raw r = raw (sort r) := by
    exact congrFun hperm r
  have hmassOut : (∑ r : Col, net.exec raw r) ≤ 40 := by
    calc
      (∑ r : Col, net.exec raw r) = ∑ r : Col, raw (sort r) := by
        apply Finset.sum_congr rfl
        intro r _
        exact hvalue r
      _ = ∑ c : Col, raw c := Equiv.sum_comp sort raw
      _ ≤ 40 := by
        rw [slope25Load_sum_eq_profile_sum profile hbound]
        exact hmass
  have hmonoOut : ∀ r s, r.val ≤ s.val → net.exec raw r ≤ net.exec raw s := by
    intro r s hrs
    exact hsorted hrs
  have hheightOut : ∀ r, net.exec raw r ≤ 2 := by
    intro r
    rw [hvalue r]
    exact slope25_first_pass_max_load_le_two profile (sort r) hmono hmass
  intro target
  exact slope39_second_pass_max_load_le_one_of_monotone
    (net.exec raw) target hmonoOut hmassOut hheightOut

/-- In particular, the standard ascending Batcher network closes the local
sparse gate without requiring dual-order comparator directions. -/
theorem slope25_then_ascending_bitonic_stride39_no_collision
    (profile : Col → Nat)
    (hmono : ∀ r s, r.val ≤ s.val → profile s ≤ profile r)
    (hmass : (∑ r : Col, profile r) ≤ 40)
    (hbound : ∀ r, profile r ≤ 64) :
    ∀ target : Col,
      (Finset.univ.filter fun r : Col =>
        forwardNeed target.val (39 * r.val) ≤
          (Bitonic.bitonicSort 6).exec (slope25Load profile) r).card ≤ 1 := by
  have hsorts : ∀ v : Col → Nat,
      Monotone ((Bitonic.bitonicSort 6).exec v) := by
    intro v
    exact (Bitonic.bitonicSort_sorts 6) Nat v
  exact slope25_then_ascending_sort_stride39_no_collision
    (Bitonic.bitonicSort 6) hsorts
    profile hmono hmass hbound

/-- Applying the same comparator network across every row of a unary-column
matrix is exactly its scalar action on column heights. This is the semantic
identity needed to lift the load sort to bundled wires. -/
theorem comparatorNetwork_exec_unaryThreshold
    (net : ComparatorNetwork 64) (height : Col → Nat) (row : Col) (column : Col) :
    net.exec (fun c : Col => decide (row.val < height c)) column =
      decide (row.val < net.exec height column) := by
  let threshold : Nat → Bool := fun x => decide (row.val < x)
  have hthreshold : Monotone threshold := by
    intro a b hab
    by_cases ha : row.val < a
    · have hb : row.val < b := lt_of_lt_of_le ha hab
      simp [threshold, ha, hb]
    · by_cases hb : row.val < b
      · simp [threshold, ha, hb]
      · simp [threshold, ha, hb]
  have hcomm := ComparatorNetwork.exec_comp_monotone net hthreshold height
  have hpoint := congrFun hcomm column
  simpa [threshold, Function.comp] using hpoint.symm

end Chvatal.D2Slope25Sparse40
