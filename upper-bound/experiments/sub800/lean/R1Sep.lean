import R1Design
import SepExists
import BaselineFringeD

/-! # Node specifications of the three network families (W2, step 1)

* `nodeSpec_sorter`: an exact sorter meets `NodeSpecAll` with any `EB ≥ 0` when `Jmax ≤ π/2`.
* `nodeSpec_padded`: the padded two-round separator `paddedPack2Net` on `a ≤ (m+1)n` wires, with
  scrambles from `SepExists`, meets `NodeSpecAll` with `EB ≥ ε_B (m+1) n / 2 + n` and
  `Jmax ≤ jmax_P(n)` when `(f+1) n ≤ π/2`.
* `nodeSpec_Bonly`: the same network with any two-sided B2 pair and `Jmax = 0` (no fringe). -/

namespace R1T

open Chvatal Tapered945 Sub800

theorem exec_eq_self_of_sorts' {a : ℕ} (net : ComparatorNetwork a) (hs : ComparatorNetwork.Sorts.{0} net)
    (x : Equiv.Perm (Fin a)) (c : Fin a) : net.exec (x : Fin a → Fin a) c = c := by
  have hm : Monotone (net.exec (x : Fin a → Fin a)) := hs (Fin a) _
  have hinj := net.exec_injective x.injective
  have hsm := hm.strictMono_of_injective hinj
  have hsurj := Finite.surjective_of_injective hinj
  have h2 : (net.exec (x : Fin a → Fin a)) = id := by
    have hsub : Subsingleton (Fin a ≃o Fin a) := inferInstance
    have := hsub.elim (StrictMono.orderIsoOfSurjective _ hsm hsurj) (OrderIso.refl _)
    funext c
    exact congrArg (fun e : Fin a ≃o Fin a => e c) this
  rw [h2]; rfl

/-- **Exact sorters.** -/
theorem nodeSpec_sorter {a : ℕ} (π : ℕ) (net : ComparatorNetwork a)
    (hs : ComparatorNetwork.Sorts.{0} net) {EB εF : ℝ} (hEB : 0 ≤ EB) (hε : 0 < εF) {Jmax : ℕ}
    (hJ : Jmax ≤ π / 2) : NodeSpecAll a π net EB Jmax εF := by
  have hid := exec_eq_self_of_sorts' net hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p _
    have : (Finset.univ.filter fun c : Fin a =>
        a - p ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - p) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]; simpa using hEB
  · intro x p _
    have : (Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < p ∧ p ≤ c.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]; simpa using hEB
  · intro x j hj hjJ _
    have : (Finset.univ.filter fun c : Fin a =>
        a - j ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - π / 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]
    have : (0 : ℝ) < j := by exact_mod_cast hj
    simpa using mul_pos hε this
  · intro x j hj hjJ _
    have : (Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < j ∧ π / 2 ≤ c.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]
    have : (0 : ℝ) < j := by exact_mod_cast hj
    simpa using mul_pos hε this

/-- **The padded two-round separator with fringe.** -/
theorem nodeSpec_padded {m n a : ℕ} (P : F2PD) (hn : 0 < n) (ha : a ≤ (m + 1) * n)
    (hlive : m * n ≤ a) (hfm : P.f ≤ m) (σ1 σ2 : Scramble (m + 1) n)
    (hgood : (SRd P (truncateBottomScramble σ1) ∧ R1d P (truncateBottomScramble σ1) ∧
        R2nd P (truncateBottomScramble σ2) ∧ HasPackSemanticPropertyB2 hn σ1 σ2 (1 / 105000)) ∧
      (SRd P (truncateBottomScramble (flipScramble σ1)) ∧
        R1d P (truncateBottomScramble (flipScramble σ1)) ∧
        R2nd P (truncateBottomScramble (flipScramble σ2)) ∧
        HasPackSemanticPropertyB2 hn (flipScramble σ1) (flipScramble σ2) (1 / 105000)))
    (π : ℕ) (hπa : π / 2 ≤ a) (hfringe : (P.f + 1) * n ≤ π / 2) (Jmax : ℕ) (hJ : Jmax ≤ P.jmax n)
    (EB : ℝ) (hEB : (1 / 105000 : ℝ) / 2 * (((m + 1 : ℕ) : ℝ) * n) + n ≤ EB) :
    NodeSpecAll a π (paddedPack2Net hn ha σ1 σ2) EB Jmax (1 / (P.J : ℝ)) := by
  obtain ⟨⟨hSR, hR1, hR2, hB⟩, ⟨hSR', hR1', hR2', hB'⟩⟩ := hgood
  have hcut := fun p r hr => paddedPack2Net_all_cut_bounds hn ha σ1 σ2 (1 / 105000) (by norm_num)
    hB hB' p r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p hp
    have := (hcut x (a - p) (by omega)).1
    push_cast at this hEB ⊢
    linarith
  · intro x p hp
    have := (hcut x p hp).2
    push_cast at this hEB ⊢
    linarith
  · intro x j hj hjJ hja
    exact paddedPack2Net_fHigh_baseline P hn ha hlive hfm σ1 σ2 hSR hR1 hR2 x (π / 2) j hπa
      (by omega) hj hja (hjJ.trans hJ)
  · intro x j hj hjJ hja
    exact paddedPack2Net_fLow_baseline P hn ha hfm σ1 σ2 hSR' hR1' hR2' x (π / 2) j hfringe hj hja
      (hjJ.trans hJ)

/-- **The B-only separator** (no fringe: `Jmax = 0`). -/
theorem nodeSpec_Bonly {M n a : ℕ} (hn : 0 < n) (ha : a ≤ M * n) (σ1 σ2 : Scramble M n)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hB : HasPackSemanticPropertyB2 hn σ1 σ2 eps)
    (hB' : HasPackSemanticPropertyB2 hn (flipScramble σ1) (flipScramble σ2) eps)
    (π : ℕ) (EB εF : ℝ) (hEB : eps / 2 * ((M : ℝ) * n) + n ≤ EB) :
    NodeSpecAll a π (paddedPack2Net hn ha σ1 σ2) EB 0 εF := by
  have hcut := fun p r hr => paddedPack2Net_all_cut_bounds hn ha σ1 σ2 eps heps hB hB' p r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p hp
    exact (hcut x (a - p) (by omega)).1.trans hEB
  · intro x p hp
    exact (hcut x p hp).2.trans hEB
  · intro x j hj hjJ; omega
  · intro x j hj hjJ; omega

end R1T
