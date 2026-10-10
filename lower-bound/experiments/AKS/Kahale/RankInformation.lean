module

public import AKS.Kahale.JointPotential

/-! # Exact rank fibers behind information-loss counterexamples

The finite counts are kernel evaluated. Shannon entropy and the proposed
amortized bank are discussed separately; no asymptotic improvement is claimed.
-/

@[expose] public section

namespace Kahale

def rankFiberSize {n : ℕ} (net : ComparatorNetwork n) (w : Fin n → Fin n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n → Fin n ↦ Function.Injective v ∧ net.exec v = w)).card

def rankImageSize {n : ℕ} (net : ComparatorNetwork n) : ℕ :=
  ((Finset.univ.filter (fun v : Fin n → Fin n ↦ Function.Injective v)).image net.exec).card

def rankTopPrefix : ComparatorNetwork 4 :=
  ⟨[⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, ⟨0, 3, by decide⟩,
    ⟨2, 3, by decide⟩, ⟨1, 2, by decide⟩]⟩

def rankTopFinal : ComparatorNetwork 4 :=
  ⟨rankTopPrefix.comparators ++ [⟨2, 3, by decide⟩]⟩

def swapTopRank : Fin 4 → Fin 4 := fun i ↦ if i = 2 then 3 else if i = 3 then 2 else i

set_option maxRecDepth 100000 in
theorem large_certificates_balanced_rank_fibers :
    exactWireCertificatePair rankTopPrefix 2 = (3, 1) ∧
    exactWireCertificatePair rankTopPrefix 3 = (3, 1) ∧
    rankFiberSize rankTopPrefix id = 12 ∧
    rankFiberSize rankTopPrefix swapTopRank = 12 ∧
    rankImageSize rankTopPrefix = 2 ∧
    rankFiberSize rankTopFinal id = 24 ∧ rankImageSize rankTopFinal = 1 := by
  decide +kernel

def rankPairPrefix : ComparatorNetwork 4 :=
  ⟨[⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩,
    ⟨0, 3, by decide⟩, ⟨1, 2, by decide⟩]⟩

def rankPairFinal : ComparatorNetwork 4 :=
  ⟨rankPairPrefix.comparators ++ [⟨0, 1, by decide⟩, ⟨2, 3, by decide⟩]⟩

def swapBottomRank : Fin 4 → Fin 4 := fun i ↦ if i = 0 then 1 else if i = 1 then 0 else i

def swapBothRank : Fin 4 → Fin 4 := fun i ↦
  if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 3 else 2

set_option maxRecDepth 100000 in
theorem near_terminal_certificate_rank_fibers :
    exactWireCertificatePair rankPairPrefix 0 = (1, 3) ∧
    exactWireCertificatePair rankPairPrefix 1 = (1, 3) ∧
    exactWireCertificatePair rankPairPrefix 2 = (3, 1) ∧
    exactWireCertificatePair rankPairPrefix 3 = (3, 1) ∧
    rankFiberSize rankPairPrefix id = 8 ∧
    rankFiberSize rankPairPrefix swapBothRank = 8 ∧
    rankFiberSize rankPairPrefix swapTopRank = 4 ∧
    rankFiberSize rankPairPrefix swapBottomRank = 4 ∧
    rankImageSize rankPairPrefix = 4 ∧
    rankFiberSize rankPairFinal id = 24 ∧ rankImageSize rankPairFinal = 1 := by
  decide +kernel

end Kahale
