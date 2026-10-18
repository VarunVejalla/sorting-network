import FrontierPositivity
import IntegerRounding

namespace Tapered945

/-- Round a real up-port to an even integer and keep it inside a parent whose
real mass has at least one unit of slack beyond that target. -/
theorem even_up_round_within_parent (idealUp : Rat) (parent : Nat)
    (hpos : 0 < idealUp)
    (hroom : idealUp + 1 ≤ (parent : Rat)) :
    ∃ up : Nat, Even up ∧ up ≤ parent ∧
      |(up : Rat) - idealUp| ≤ 1 := by
  obtain ⟨up, heven, hnear⟩ := exists_even_nat_within_one idealUp hpos.le
  have huple : (up : Rat) ≤ parent := by
    have hup := (abs_le.mp hnear).2
    linarith
  exact ⟨up, heven, by exact_mod_cast huple, hnear⟩

/-- The upper moving frontier has a complete integer split into its parent
up-port and 64 ordinary child blocks. This is the local rounding step; the
separate global proof must still show the actual parent count has the stated
frontier mass. -/
theorem top_retreat_integer_split (C e eta : Rat) (parent : Nat)
    (hC : 2^34 ≤ C) (he : -eAbs ≤ e ∧ e ≤ ePos)
    (heta : |eta| ≤ 69)
    (hcount : (parent : Rat) = frontierTopMass C e + eta) :
    ∃ up : Nat, Even up ∧ up ≤ parent ∧
      |(up : Rat) - frontierTopRetreatUp C e| ≤ 1 ∧
      ∃ blocks : Fin 64 → Nat,
        (∑ j, blocks j) = parent - up ∧
        ∀ j, |(blocks j : Rat) - frontierOrdinaryDown C e j| ≤ 1 + 70/64 := by
  let coeff : Fin 64 → Rat := fun j => addressDownCoeff j.val
  have hcoeff : ∀ j, coeff j = rEnd ∨ coeff j = rMid := by
    intro j
    exact addressDownCoeff_cases j.val
  have heq : (∑ j : Fin 64, (coeff j * C + e * C / 64)) =
      ∑ j : Fin 64, frontierOrdinaryDown C e j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [coeff, frontierOrdinaryDown]
    ring
  have hparent : (parent : Rat) = frontierTopRetreatUp C e +
      (∑ j, (coeff j * C + e * C / 64)) + eta := by
    calc
      (parent : Rat) = frontierTopMass C e + eta := hcount
      _ = frontierTopRetreatUp C e +
          (∑ j, frontierOrdinaryDown C e j) + eta := by
        rw [← frontier_top_retreat_split]
      _ = frontierTopRetreatUp C e +
          (∑ j, (coeff j * C + e * C / 64)) + eta := by rw [heq]
  have hsumdown := frontier_ordinary_down_sum C e
  have hsumCoeff : (∑ j : Fin 64, (coeff j * C + e * C / 64)) =
      (1 - 256 / (64^2 * 64^2)) * C + e * C := by
    rw [heq, hsumdown]
    norm_num [cap]
  have hsumEta : 1 ≤
      (∑ j : Fin 64, (coeff j * C + e * C / 64)) + eta := by
    have hetaLo := (abs_le.mp heta).1
    have heLo := he.1
    unfold cap at hsumCoeff
    unfold eAbs at heLo
    nlinarith [hC]
  have hroom : frontierTopRetreatUp C e + 1 ≤ (parent : Rat) := by
    rw [hparent]
    linarith
  have hcoeffpos : 0 < 1/65536 + e/15 :=
    frontier_top_retreat_coeff_positive e he.1
  have hCpos : 0 < C := by linarith
  have hupPos : 0 < frontierTopRetreatUp C e := by
    unfold frontierTopRetreatUp
    exact mul_pos hcoeffpos hCpos
  obtain ⟨up, heven, huple, hupNear⟩ :=
    even_up_round_within_parent (frontierTopRetreatUp C e) parent hupPos hroom
  have hdebtLo : -eAbs * C ≤ e * C := mul_le_mul_of_nonneg_right he.1 hCpos.le
  have hdebtHi : e * C ≤ ePos * C := mul_le_mul_of_nonneg_right he.2 hCpos.le
  obtain ⟨blocks, htotal, herror⟩ := candidate_integerize_parent
    C (e*C) (frontierTopRetreatUp C e) eta
    (fun j : Fin 64 => addressDownCoeff j.val) parent up hC
    hdebtLo hdebtHi hcoeff heta hparent hupNear huple
  have htarget : ∀ j, addressDownCoeff j.val * C + e*C/64 =
      frontierOrdinaryDown C e j := by
    intro j
    simp [frontierOrdinaryDown]
    ring
  refine ⟨up, heven, huple, hupNear, blocks, htotal, ?_⟩
  intro j
  rw [← htarget j]
  exact herror j

/-! Integer realization of a top-advance split. Choice across successive
stages and the receiving discrepancy invariant remain separate obligations. -/

theorem top_advance_block_lower (C e : Rat) (j : Fin 64)
    (hC : 0 ≤ C) (he : -eAbs ≤ e) :
    C / 128 ≤ frontierTopAdvanceDown C e j := by
  have hq := (addressQ_bounds j.val).1
  have hc : (1 / 128 : Rat) ≤
      1 / 64 + boundaryDebtCoeff * (addressQ j.val + e / 64) := by
    unfold boundaryDebtCoeff eAbs qEnd at *
    linarith
  have hm := mul_le_mul_of_nonneg_right hc hC
  unfold frontierTopAdvanceDown
  linarith

theorem top_advance_integer_split (C e eta : Rat) (count : Nat)
    (hC : 2 ^ 34 ≤ C) (he : -eAbs ≤ e) (heta : |eta| ≤ 69)
    (hcount : (count : Rat) = frontierTopMass C e + eta) :
    ∃ blocks : Fin 64 → Nat, (∑ j, blocks j) = count ∧
      ∀ j, |(blocks j : Rat) - frontierTopAdvanceDown C e j| ≤
        1 + 69 / 64 := by
  have hsum := frontier_top_advance_split C e
  have hdelta : (count : Rat) - ∑ j, frontierTopAdvanceDown C e j = eta := by
    rw [hsum, hcount]
    ring
  have hshift : ∀ j, 0 ≤ frontierTopAdvanceDown C e j +
      ((count : Rat) - ∑ i, frontierTopAdvanceDown C e i) / 64 := by
    intro j
    rw [hdelta]
    have hl := top_advance_block_lower C e j (by norm_num at hC ⊢; linarith) he
    have helo := (abs_le.mp heta).1
    norm_num at hC
    linarith
  obtain ⟨blocks, htotal, herr⟩ := balanced_rounding_with_total_error
    (frontierTopAdvanceDown C e) count hshift
  refine ⟨blocks, htotal, ?_⟩
  intro j
  have h := herr j
  rw [hdelta] at h
  linarith

end Tapered945
