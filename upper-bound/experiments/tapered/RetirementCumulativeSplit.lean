import FrontierEvenFlow
import CumulativeEvenRounding

namespace Tapered945

def nativeComplementBlocks (native stored : Fin 64 → Nat) : Fin 64 → Nat :=
  fun j => native j - stored j

/-! A local interface from coordinated subtree rounding to the existing
top-advance flow contract. The missing global premise is that a single
schedule supplies the stored/native masses and exact source conservation. -/

/-- If each retired child keeps an even stored mass inside its native
component, the exact native complements define an allowed top-advance split
whenever they conserve the retiring source count. A cumulative-rounded
subtree supplies each `herr` premise through
`retirement_complement_from_rounded_interval`. -/
theorem retirement_even_flow_of_complements
    (B C e : Rat) (count : Nat)
    (native stored : Fin 64 → Nat)
    (hNativeEven : ∀ j, Even (native j))
    (hStoredEven : ∀ j, Even (stored j))
    (hStoredLe : ∀ j, stored j ≤ native j)
    (hCount : count = ∑ j : Fin 64, nativeComplementBlocks native stored j)
    (hError : ∀ j : Fin 64,
      |((native j - stored j : Nat) : Rat) - frontierTopAdvanceDown C e j| < 2) :
    Nonempty (ScheduledEvenFlow .topAdvance B C e count) := by
  let blocks : Fin 64 → Nat := nativeComplementBlocks native stored
  have hBlocksEven : ∀ j, Even (blocks j) := by
    intro j
    obtain ⟨a, ha⟩ := hNativeEven j
    obtain ⟨b, hb⟩ := hStoredEven j
    have hle := hStoredLe j
    rw [ha, hb] at hle
    have hba : b ≤ a := by omega
    change Even (native j - stored j)
    rw [ha, hb]
    refine ⟨a - b, ?_⟩
    omega
  have hBlocksTotal : (∑ j : Fin 64, blocks j) = count := by
    exact hCount.symm
  have hBlockError : ∀ j,
      |(blocks j : Rat) - frontierTopAdvanceDown C e j| ≤ evenFlowBlockError := by
    intro j
    have h := hError j
    change |((native j - stored j : Nat) : Rat) - frontierTopAdvanceDown C e j| ≤
      evenFlowBlockError
    exact le_of_lt (h.trans_le (by norm_num [evenFlowBlockError]))
  let split : EvenFlowSplit count := {
    up := 0
    blocks := blocks
    up_even := ⟨0, rfl⟩
    blocks_even := hBlocksEven
    up_le := Nat.zero_le _
    total := by simpa using hBlocksTotal
  }
  refine ⟨{
    split := split
    up_error := ?_
    block_error := ?_
    advance_up := ?_
    whole_up := ?_
  } ⟩
  · norm_num [split, scheduledUpTarget]
  · intro j
    simpa [split, scheduledDownTarget, blocks] using hBlockError j
  · intro _
    rfl
  · intro h
    rcases h with h | h <;> cases h

end Tapered945
