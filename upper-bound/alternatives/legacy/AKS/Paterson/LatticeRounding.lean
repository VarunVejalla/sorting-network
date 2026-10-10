module

public import AKS.Paterson.Rounding
public import AKS.Separator.PatersonCertificate

/-! # Coarser subtree rounding compatible with the checked separator

Paterson's subtree rounding can be performed on a fixed lattice. A lattice
of 32 makes full bags divisible by 32 and therefore permits the existing
989-depth separator certificate directly. This is a local arithmetic bridge:
the scheduler must still establish the rounded subtree identities and route
the corresponding fringes. The extra rounding error is a fixed constant.
-/

@[expose] public section

namespace Paterson.Bags

def ceil32 (x : ℚ) : ℕ := 32 * ⌈x / 32⌉₊

theorem ceil32_dvd (x : ℚ) : 32 ∣ ceil32 x := dvd_mul_right _ _

theorem le_ceil32 (x : ℚ) : x ≤ (ceil32 x : ℚ) := by
  have h := Nat.le_ceil (x / 32)
  simp only [ceil32, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem ceil32_lt_add {x : ℚ} (hx : 0 ≤ x) : (ceil32 x : ℚ) < x + 32 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x / 32 by linarith)
  simp only [ceil32, Nat.cast_mul, Nat.cast_ofNat]
  linarith

def latticeBag (a g : ℚ) : ℕ := ceil32 a - 4 * ceil32 g

theorem latticeBag_dvd (a g : ℚ) : 32 ∣ latticeBag a g :=
  Nat.dvd_sub (ceil32_dvd a) (dvd_mul_of_dvd_right (ceil32_dvd g) 4)

theorem latticeBag_bounds {a b g : ℚ} (hg : 0 ≤ g)
    (hab : a = b + 4 * g) (hb : 128 ≤ b) :
    b - 128 < (latticeBag a g : ℚ) ∧ (latticeBag a g : ℚ) < b + 32 := by
  have ha : 0 ≤ a := by linarith
  have h₁ := le_ceil32 a
  have h₂ := ceil32_lt_add ha
  have h₃ := le_ceil32 g
  have h₄ := ceil32_lt_add hg
  have hleQ : (4 : ℚ) * ceil32 g ≤ ceil32 a := by linarith
  have hle : 4 * ceil32 g ≤ ceil32 a := by exact_mod_cast hleQ
  simp only [latticeBag, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
  constructor <;> linarith

theorem lattice_support_slack {b : ℚ} {n : ℕ}
    (hb : roundedParams.minCapacity ≤ b) (hn : b - 128 ≤ (n : ℚ)) :
    roundedParams.mu * b ≤ roundedParams.support * n := by
  norm_num [roundedParams, patersonMu] at *
  linarith

/-- Local integer conservation for the lattice scheduler. `32*a` is the old
subtree total, `32*g` each active granddaughter subtree, and `32*next` the
new child subtree total. The chosen fringe makes both the middle sent to a
child and the total sent to the parent divisible by 32. Independent rounding
of the bag size and fringe would not guarantee this. -/
theorem lattice_routing_counts (a g next : ℕ)
    (hsmall : 2 * g ≤ next) (hlarge : 2 * next ≤ a) :
    let bag := 32 * a - 4 * (32 * g)
    let fringe := 16 * a - 32 * next
    fringe ≤ bag / 2 ∧
      bag / 2 - fringe = 32 * (next - 2 * g) ∧
      2 * fringe = 32 * (a - 2 * next) := by
  dsimp
  omega

/-- The local separator is already fully certified at these bag sizes.
This statement does not assert that the unfinished scheduler produces them. -/
theorem lattice_separator_certificate (a g : ℚ) :
    IsSupportedSeparator (separatorNetwork (latticeBag a g))
      (latticeBag a g / 32) (patersonMu : ℝ) (patersonTailError : ℝ) ∧
      (separatorNetwork (latticeBag a g)).depth ≤ 989 :=
  separatorNetwork_certificate_of_dvd32 _ (latticeBag_dvd a g)

end Paterson.Bags
