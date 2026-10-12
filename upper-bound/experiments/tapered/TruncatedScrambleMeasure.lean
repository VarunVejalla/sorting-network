import PaddedFringe
import Mathlib.Tactic

namespace Tapered945

open Chvatal Classical

noncomputable def scrambleLastSplit {m n : Nat} :
    Scramble (m + 1) n ≃ Scramble m n × Equiv.Perm (Fin n) :=
  (Fin.snocEquiv (fun _ : Fin (m + 1) => Equiv.Perm (Fin n))).symm.trans
    (Equiv.prodComm _ _)

def BadPrefixScramble {m n : Nat} (P : Scramble m n → Prop) :=
  {σ : Scramble m n // ¬ P σ}

def BadTruncatedScramble {m n : Nat} (P : Scramble m n → Prop) :=
  {σ : Scramble (m + 1) n // ¬ P (truncateBottomScramble σ)}

theorem scrambleLastSplit_apply {m n : Nat} (σ : Scramble (m + 1) n) :
    scrambleLastSplit σ = (truncateBottomScramble σ, σ (Fin.last m)) := by
  change (Fin.init σ, σ (Fin.last m)) = (truncateBottomScramble σ, σ (Fin.last m))
  rfl

noncomputable def badTruncEquiv {m n : Nat} (P : Scramble m n → Prop) :
    BadTruncatedScramble P ≃ BadPrefixScramble P × Equiv.Perm (Fin n) where
  toFun σ := ⟨⟨truncateBottomScramble σ.1, σ.2⟩, σ.1 (Fin.last m)⟩
  invFun p := ⟨(scrambleLastSplit (m := m) (n := n)).symm (p.1.1, p.2), by
    have h := congrArg Prod.fst ((scrambleLastSplit (m := m) (n := n)).apply_symm_apply
      (p.1.1, p.2))
    rw [scrambleLastSplit_apply] at h
    change ¬ P (truncateBottomScramble
      ((scrambleLastSplit (m := m) (n := n)).symm (p.1.1, p.2)))
    have h' : truncateBottomScramble
        ((scrambleLastSplit (m := m) (n := n)).symm (p.1.1, p.2)) = p.1.1 := by
      simpa using h
    rw [h']
    exact p.1.2⟩
  left_inv σ := by
    apply Subtype.ext
    exact (scrambleLastSplit (m := m) (n := n)).symm_apply_apply σ.1
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((scrambleLastSplit (m := m) (n := n)).apply_symm_apply
        (p.1.1, p.2))
    · change (scrambleLastSplit (m := m) (n := n)).symm (p.1.1, p.2)
        (Fin.last m) = p.2
      have h := (scrambleLastSplit (m := m) (n := n)).apply_symm_apply (p.1.1, p.2)
      rw [scrambleLastSplit_apply] at h
      exact congrArg Prod.snd h

/-- Exact preservation of a failure fraction under truncating one independent
final row. -/
theorem truncate_bad_fraction {m n : Nat} (P : Scramble m n → Prop)
    (b : Real)
    (hbad : ((Finset.univ.filter fun σ : Scramble m n => ¬ P σ).card : Real) ≤
      b * (Fintype.card (Scramble m n) : Real)) :
    ((Finset.univ.filter fun σ : Scramble (m + 1) n =>
      ¬ P (truncateBottomScramble σ)).card : Real) ≤
        b * (Fintype.card (Scramble (m + 1) n) : Real) := by
  classical
  letI : Fintype (BadPrefixScramble P) := Fintype.subtype
    (Finset.univ.filter fun σ : Scramble m n => ¬ P σ) (by simp [BadPrefixScramble])
  letI : Fintype (BadTruncatedScramble P) := Fintype.subtype
    (Finset.univ.filter fun σ : Scramble (m + 1) n =>
      ¬ P (truncateBottomScramble σ)) (by simp [BadTruncatedScramble])
  have hsub : Fintype.card (BadTruncatedScramble P) =
      Fintype.card (BadPrefixScramble P) * Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Fintype.card_congr (badTruncEquiv P), Fintype.card_prod]
  have htotal : Fintype.card (Scramble (m + 1) n) =
      Fintype.card (Scramble m n) * Fintype.card (Equiv.Perm (Fin n)) := by
    rw [← Fintype.card_prod, Fintype.card_congr (scrambleLastSplit (m := m) (n := n))]
  have hbadP : ((Fintype.card (BadPrefixScramble P) : Nat) : Real) =
      (Finset.univ.filter fun σ : Scramble m n => ¬ P σ).card := by
    norm_cast
    exact Fintype.card_of_subtype _ (by simp [BadPrefixScramble])
  have hbadT : ((Fintype.card (BadTruncatedScramble P) : Nat) : Real) =
      (Finset.univ.filter fun σ : Scramble (m + 1) n =>
        ¬ P (truncateBottomScramble σ)).card := by
    norm_cast
    exact Fintype.card_of_subtype _ (by simp [BadTruncatedScramble])
  have hbad' : (Fintype.card (BadPrefixScramble P) : Real) ≤
      b * (Fintype.card (Scramble m n) : Real) := by
    rw [hbadP]
    exact hbad
  have hperm : (0 : Real) ≤ Fintype.card (Equiv.Perm (Fin n)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbad' hperm
  have hsubR : (Fintype.card (BadTruncatedScramble P) : Real) =
      (Fintype.card (BadPrefixScramble P) : Real) * Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast hsub
  rw [← hsubR] at hmul
  have htotalR : (Fintype.card (Scramble (m + 1) n) : Real) =
      (Fintype.card (Scramble m n) : Real) * Fintype.card (Equiv.Perm (Fin n)) := by
    exact_mod_cast htotal
  rw [← hbadT, htotalR]
  calc
    (Fintype.card (BadTruncatedScramble P) : Real) ≤
        b * (Fintype.card (Scramble m n) : Real) * Fintype.card (Equiv.Perm (Fin n)) := hmul
    _ = b * ((Fintype.card (Scramble m n) : Real) *
        Fintype.card (Equiv.Perm (Fin n))) := by ring

end Tapered945
