import D2Slope25Physical

open Chvatal.D2RankAlignment Chvatal.D2Slope25Physical

set_option maxHeartbeats 2000000

theorem card_lt_fin (k : Nat) (hk : k <= 64) :
    (Finset.univ.filter fun i : Fin 64 => i.val < k).card = k := by
  calc
    (Finset.univ.filter fun i : Fin 64 => i.val < k).card =
        (Finset.Ico 0 k).card := by
      exact Finset.card_bij
        (s := Finset.univ.filter fun i : Fin 64 => i.val < k)
        (t := Finset.Ico 0 k)
        (fun i _ => i.val)
        (by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_Ico.mpr (And.intro (Nat.zero_le _) hi))
        (by intro i hi j hj hij; exact Fin.ext hij)
        (by
          intro x hx
          have hx' := Finset.mem_Ico.mp hx
          let i : Fin 64 := Fin.mk x (lt_of_lt_of_le hx'.2 hk)
          exact Exists.intro i
            (Exists.intro (Finset.mem_filter.mpr
              (And.intro (Finset.mem_univ _) hx'.2)) rfl))
    _ = k := by simp

theorem residueHits64_sum (x : Nat) :
    (Finset.univ.sum fun r : Fin 64 => residueHits64 x r.val) = x := by
  calc
    (Finset.univ.sum fun r : Fin 64 => residueHits64 x r.val) =
        (Finset.univ.sum fun r : Fin 64 =>
          x / 64 + if r.val < x % 64 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact residueHits64_eq x r.val r.isLt
    _ = 64 * (x / 64) + x % 64 := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Finset.sum_boole]
      have hx : x % 64 < 64 := Nat.mod_lt x (by omega)
      rw [card_lt_fin (x % 64) (Nat.le_of_lt hx)]
      norm_cast
    _ = x := by omega

lemma hits_add (a b r : Nat) (hr : r < 64) :
    residueHits64 (a+b) r =
      residueHits64 a r + residueHits64 b ((r + 64 - a % 64) % 64) := by
  rw [residueHits64_eq (a+b) r hr,
    residueHits64_eq a r hr,
    residueHits64_eq b ((r + 64 - a % 64) % 64)
      (Nat.mod_lt _ (by omega))]
  rw [Nat.add_mod, Nat.add_div (by omega)]
  by_cases hshift : r < a % 64
  case pos =>
    have hs : (r + 64 - a % 64) % 64 = r + 64 - a % 64 := by omega
    rw [hs]
    by_cases hcarry : a % 64 + b % 64 < 64
    case pos =>
      have hmod : (a % 64 + b % 64) % 64 = a % 64 + b % 64 := Nat.mod_eq_of_lt hcarry
      rw [hmod]
      split_ifs <;> omega
    case neg =>
      have hmod : (a % 64 + b % 64) % 64 = a % 64 + b % 64 - 64 := by omega
      rw [hmod]
      split_ifs <;> omega
  case neg =>
    have hs : (r + 64 - a % 64) % 64 = r - a % 64 := by omega
    rw [hs]
    by_cases hcarry : a % 64 + b % 64 < 64
    case pos =>
      have hmod : (a % 64 + b % 64) % 64 = a % 64 + b % 64 := Nat.mod_eq_of_lt hcarry
      rw [hmod]
      split_ifs <;> omega
    case neg =>
      have hmod : (a % 64 + b % 64) % 64 = a % 64 + b % 64 - 64 := by omega
      rw [hmod]
      split_ifs <;> omega

def slope25RowEquiv (d : Fin 64) : Equiv.Perm (Fin 64) where
  toFun := slope25RowAt d
  invFun := fun r => Fin.mk ((11 * (d.val + 64 - (25 * r.val) % 64)) % 64)
    (Nat.mod_lt _ (by omega))
  left_inv := by
    intro c
    apply Fin.ext
    dsimp [slope25RowAt]
    omega
  right_inv := by
    intro r
    apply Fin.ext
    dsimp [slope25RowAt]
    omega

def shiftedDest (b : Nat) (d : Fin 64) : Fin 64 :=
  Fin.mk ((d.val + 64 - (25*b)%64)%64) (Nat.mod_lt _ (by omega))

lemma slope25RowAt_shift (b : Nat) (d c : Fin 64) :
    ((slope25RowAt d c).val + 64 - b%64)%64 =
      (slope25RowAt (shiftedDest b d) c).val := by
  dsimp [slope25RowAt, shiftedDest]
  rw [Nat.mul_mod]
  omega

theorem slope25_prefix_sum (b : Nat) (d : Fin 64) :
    (Finset.univ.sum fun c : Fin 64 =>
      residueHits64 b (slope25RowAt d c).val) = b := by
  let e := slope25RowEquiv d
  change (Finset.univ.sum fun c : Fin 64 => residueHits64 b (e c).val) = b
  rw [Equiv.sum_comp e (fun r : Fin 64 => residueHits64 b r.val)]
  exact residueHits64_sum b

theorem slope25_residue_uniform_shift (h : Fin 64 -> Nat) (b : Nat) (d : Fin 64) :
    (Finset.univ.sum fun c : Fin 64 =>
      residueHits64 (b + h c) (slope25RowAt d c).val) =
      b + (Finset.univ.sum fun c : Fin 64 =>
        residueHits64 (h c) (slope25RowAt (shiftedDest b d) c).val) := by
  calc
    (Finset.univ.sum fun c : Fin 64 =>
      residueHits64 (b + h c) (slope25RowAt d c).val) =
        (Finset.univ.sum fun c : Fin 64 =>
          residueHits64 b (slope25RowAt d c).val +
            residueHits64 (h c)
              (((slope25RowAt d c).val + 64 - b % 64) % 64)) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hits_add b (h c) (slope25RowAt d c).val (slope25RowAt d c).isLt
    _ = b + (Finset.univ.sum fun c : Fin 64 =>
          residueHits64 (h c) (slope25RowAt (shiftedDest b d) c).val) := by
      rw [Finset.sum_add_distrib, slope25_prefix_sum]
      apply congrArg (fun x => b + x)
      apply Finset.sum_congr rfl
      intro c hc
      rw [slope25RowAt_shift]



theorem slope25PhysicalOutputHeight_eq_residue
    (h : Fin 64 -> Nat) (d : Fin 64) :
    slope25PhysicalOutputHeight h d =
      (Finset.univ.sum fun c : Fin 64 =>
        residueHits64 (h c) (slope25RowAt d c).val) := by
  unfold slope25PhysicalOutputHeight
  apply Finset.sum_congr rfl
  intro c hc
  exact slope25_source_hits_eq_residue (h c) c d

theorem slope25Physical_uniform_shift (h : Fin 64 -> Nat) (b : Nat) (d : Fin 64) :
    slope25PhysicalOutputHeight (fun c => b + h c) d =
      b + slope25PhysicalOutputHeight h (shiftedDest b d) := by
  calc
    slope25PhysicalOutputHeight (fun c => b + h c) d =
        (Finset.univ.sum fun c : Fin 64 =>
          residueHits64 (b + h c) (slope25RowAt d c).val) :=
      slope25PhysicalOutputHeight_eq_residue _ _
    _ = b + (Finset.univ.sum fun c : Fin 64 =>
          residueHits64 (h c) (slope25RowAt (shiftedDest b d) c).val) :=
      slope25_residue_uniform_shift h b d
    _ = b + slope25PhysicalOutputHeight h (shiftedDest b d) := by
      rw [slope25PhysicalOutputHeight_eq_residue]

lemma residueHits64_split_quotient (x r : Nat) (hr : r < 64) :
    residueHits64 x r = x / 64 + residueHits64 (x % 64) r := by
  rw [residueHits64_eq x r hr, residueHits64_eq (x % 64) r hr]
  have hs : x % 64 < 64 := Nat.mod_lt x (by decide)
  simp [Nat.div_eq_of_lt hs, Nat.mod_eq_of_lt hs]

theorem slope35PhysicalOutputHeight_eq_residue
    (inputHeight : Fin 64 -> Nat) (d : Fin 64) :
    slope35PhysicalOutputHeight inputHeight d =
      (Finset.univ.sum fun c : Fin 64 =>
        residueHits64 (inputHeight c) (slope35RowAt d c).val) := by
  unfold slope35PhysicalOutputHeight
  apply Finset.sum_congr rfl
  intro c hc
  exact slope35_source_hits_eq_residue (inputHeight c) c d

theorem slope35Physical_uniform_quotient
    (h : Fin 64 -> Nat) (d : Fin 64) :
    slope35PhysicalOutputHeight h d =
      (Finset.univ.sum fun c : Fin 64 => h c / 64) +
        slope35PhysicalOutputHeight (fun c => h c % 64) d := by
  rw [slope35PhysicalOutputHeight_eq_residue,
    slope35PhysicalOutputHeight_eq_residue]
  calc
    (Finset.univ.sum fun c : Fin 64 =>
      residueHits64 (h c) (slope35RowAt d c).val) =
        Finset.univ.sum fun c : Fin 64 =>
          (h c / 64 + residueHits64 (h c % 64) (slope35RowAt d c).val) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact residueHits64_split_quotient (h c) (slope35RowAt d c).val
        (slope35RowAt d c).isLt
    _ = (Finset.univ.sum fun c : Fin 64 => h c / 64) +
        (Finset.univ.sum fun c : Fin 64 =>
          residueHits64 (h c % 64) (slope35RowAt d c).val) := by
      rw [Finset.sum_add_distrib]

def liftSlope35Destination (layer : Fin 64) : Fin 64 :=
  Fin.mk ((35 * layer.val) % 64) (Nat.mod_lt _ (by decide))

def fullHeightTwoShuffle (h : Fin 64 -> Nat) (d : Fin 64) : Nat :=
  slope25PhysicalOutputHeight
    (fun layer => slope35PhysicalOutputHeight h (liftSlope35Destination layer)) d

def residualTwoShuffle (h : Fin 64 -> Nat) (d : Fin 64) : Nat :=
  slope25PhysicalOutputHeight
    (fun layer => slope35PhysicalOutputHeight
      (fun c => h c % 64) (liftSlope35Destination layer)) d

theorem fullHeightTwoShuffle_eq_quotient_residual
    (h : Fin 64 -> Nat) (d : Fin 64) :
    fullHeightTwoShuffle h d =
      (Finset.univ.sum fun c : Fin 64 => h c / 64) +
        residualTwoShuffle h
          (shiftedDest (Finset.univ.sum fun c : Fin 64 => h c / 64) d) := by
  let q := Finset.univ.sum fun c : Fin 64 => h c / 64
  unfold fullHeightTwoShuffle
  rw [show (fun layer : Fin 64 =>
      slope35PhysicalOutputHeight h (liftSlope35Destination layer)) =
      (fun layer : Fin 64 => q +
        slope35PhysicalOutputHeight (fun c => h c % 64)
          (liftSlope35Destination layer)) by
    funext layer
    exact slope35Physical_uniform_quotient h (liftSlope35Destination layer)]
  rw [slope25Physical_uniform_shift]
  rfl

lemma residueHits64_le_64_of_le_4096 (x r : Nat) (hr : r < 64)
    (hx : x <= 4096) : residueHits64 x r <= 64 := by
  rw [residueHits64_eq x r hr]
  have hdecomp : x % 64 + 64 * (x / 64) = x := Nat.mod_add_div x 64
  by_cases hfull : x = 4096
  · subst x
    simp
  · have hx' : x < 4096 := by omega
    have hdiv : x / 64 <= 63 := by omega
    by_cases hrem : r < x % 64 <;> simp [hrem] <;> omega

theorem slope35PhysicalOutputHeight_le_4096
    (h : Fin 64 -> Nat) (hbound : forall c, h c <= 4096) (d : Fin 64) :
    slope35PhysicalOutputHeight h d <= 4096 := by
  rw [slope35PhysicalOutputHeight_eq_residue]
  calc
    (Finset.univ.sum fun c : Fin 64 => residueHits64 (h c) (slope35RowAt d c).val) <=
        Finset.univ.sum fun _ : Fin 64 => 64 := by
      apply Finset.sum_le_sum
      intro c hc
      exact residueHits64_le_64_of_le_4096 (h c) (slope35RowAt d c).val
        (slope35RowAt d c).isLt (hbound c)
    _ = 4096 := by norm_num [Fintype.card_fin]

theorem slope25PhysicalOutputHeight_le_4096
    (h : Fin 64 -> Nat) (hbound : forall c, h c <= 4096) (d : Fin 64) :
    slope25PhysicalOutputHeight h d <= 4096 := by
  rw [slope25PhysicalOutputHeight_eq_residue]
  calc
    (Finset.univ.sum fun c : Fin 64 => residueHits64 (h c) (slope25RowAt d c).val) <=
        Finset.univ.sum fun _ : Fin 64 => 64 := by
      apply Finset.sum_le_sum
      intro c hc
      exact residueHits64_le_64_of_le_4096 (h c) (slope25RowAt d c).val
        (slope25RowAt d c).isLt (hbound c)
    _ = 4096 := by norm_num [Fintype.card_fin]

theorem fullHeightTwoShuffle_le_4096
    (h : Fin 64 -> Nat) (hbound : forall c, h c <= 4096) (d : Fin 64) :
    fullHeightTwoShuffle h d <= 4096 := by
  unfold fullHeightTwoShuffle
  apply slope25PhysicalOutputHeight_le_4096
  intro layer
  exact slope35PhysicalOutputHeight_le_4096 h hbound (liftSlope35Destination layer)
