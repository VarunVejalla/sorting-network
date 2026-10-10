module

public import AKS.Sort.Defs

/-! # Exact execution on a two-dimensional Boolean input face

The six monotone Boolean functions of two variables form a closed model for
four coupled comparator executions. Distinct variable signals coalesce into
meet/join signals. These local identities alone give no depth rate.
-/

@[expose] public section

namespace Kahale

inductive FaceSignal
  | zero | one | left | right | meet | join
  deriving DecidableEq, Repr

def FaceSignal.eval : FaceSignal → Bool → Bool → Bool
  | .zero, _, _ => false
  | .one, _, _ => true
  | .left, a, _ => a
  | .right, _, b => b
  | .meet, a, b => a && b
  | .join, a, b => a || b

def FaceSignal.dual : FaceSignal → FaceSignal
  | .zero => .one
  | .one => .zero
  | .left => .left
  | .right => .right
  | .meet => .join
  | .join => .meet

def faceMeet : FaceSignal → FaceSignal → FaceSignal
  | .zero, _ | _, .zero => .zero
  | .one, b => b
  | a, .one => a
  | .meet, _ | _, .meet => .meet
  | .left, .left => .left
  | .right, .right => .right
  | .left, .right | .right, .left => .meet
  | .left, .join | .join, .left => .left
  | .right, .join | .join, .right => .right
  | .join, .join => .join

def faceJoin (a b : FaceSignal) : FaceSignal :=
  (faceMeet a.dual b.dual).dual

def FaceSignal.axisCount : FaceSignal → ℕ
  | .left | .right => 1
  | _ => 0

def oppositeAxes (a b : FaceSignal) : Prop :=
  (a = .left ∧ b = .right) ∨ (a = .right ∧ b = .left)

instance (a b : FaceSignal) : Decidable (oppositeAxes a b) :=
  inferInstanceAs (Decidable ((a = .left ∧ b = .right) ∨ (a = .right ∧ b = .left)))

theorem faceMeet_eval (a b : FaceSignal) (x y : Bool) :
    (faceMeet a b).eval x y = min (a.eval x y) (b.eval x y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> decide

theorem faceJoin_eval (a b : FaceSignal) (x y : Bool) :
    (faceJoin a b).eval x y = max (a.eval x y) (b.eval x y) := by
  cases a <;> cases b <;> cases x <;> cases y <;> decide

/-- Two variable axes disappear precisely at an opposite-axis comparison. -/
theorem face_axis_balance (a b : FaceSignal) :
    (faceMeet a b).axisCount + (faceJoin a b).axisCount +
      (if oppositeAxes a b then 2 else 0) = a.axisCount + b.axisCount := by
  cases a <;> cases b <;> decide

theorem face_middle_equal_iff (a : FaceSignal) :
    a.eval true false = a.eval false true ↔ a.axisCount = 0 := by
  cases a <;> decide

/-- A single discrepancy goes to min against a one and max against a zero. -/
theorem face_axis_route (other : Bool) :
    faceMeet .left (if other then .one else .zero) =
      (if other then .left else .zero) ∧
    faceJoin .left (if other then .one else .zero) =
      (if other then .one else .left) := by
  cases other <;> decide

def applyFace {n : ℕ} (c : Comparator n) (v : Fin n → FaceSignal) :
    Fin n → FaceSignal := fun k ↦
  if k = c.i then faceMeet (v c.i) (v c.j)
  else if k = c.j then faceJoin (v c.i) (v c.j)
  else v k

def execFace {n : ℕ} (net : ComparatorNetwork n) (v : Fin n → FaceSignal) :
    Fin n → FaceSignal := net.comparators.foldl (fun acc c ↦ applyFace c acc) v

theorem applyFace_eval {n : ℕ} (c : Comparator n) (v : Fin n → FaceSignal)
    (x y : Bool) :
    (fun k ↦ (applyFace c v k).eval x y) = c.apply (fun k ↦ (v k).eval x y) := by
  funext k
  simp only [applyFace, Comparator.apply]
  split_ifs <;> simp only [faceMeet_eval, faceJoin_eval]

theorem execFace_eval {n : ℕ} (net : ComparatorNetwork n) (v : Fin n → FaceSignal)
    (x y : Bool) :
    (fun k ↦ (execFace net v k).eval x y) = net.exec (fun k ↦ (v k).eval x y) := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => rfl
  | cons c cs ih =>
    simp only [execFace, ComparatorNetwork.exec, List.foldl_cons]
    have h := ih (applyFace c v)
    simp only [execFace, ComparatorNetwork.exec] at h
    rw [applyFace_eval] at h
    exact h

theorem execFace_middle_equal_iff {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → FaceSignal) :
    net.exec (fun k ↦ (v k).eval true false) =
      net.exec (fun k ↦ (v k).eval false true) ↔
      ∀ k, (execFace net v k).axisCount = 0 := by
  rw [← execFace_eval, ← execFace_eval]
  constructor
  · intro h k
    exact (face_middle_equal_iff (execFace net v k)).mp (congrFun h k)
  · intro h
    funext k
    exact (face_middle_equal_iff (execFace net v k)).mpr (h k)

def faceAxisCount {n : ℕ} (v : Fin n → FaceSignal) : ℕ :=
  ∑ k, (v k).axisCount

theorem applyFace_axis_balance {n : ℕ} (c : Comparator n) (v : Fin n → FaceSignal) :
    faceAxisCount (applyFace c v) + (if oppositeAxes (v c.i) (v c.j) then 2 else 0) =
      faceAxisCount v := by
  classical
  let rest := (Finset.univ.erase c.i).erase c.j
  have hij : c.i ≠ c.j := ne_of_lt c.h
  have hi : c.i ∉ rest := by simp [rest]
  have hj : c.j ∉ rest := by simp [rest]
  have hi' : c.i ∉ insert c.j rest := by simp [hi, hij]
  have hu : (Finset.univ : Finset (Fin n)) = insert c.i (insert c.j rest) := by
    ext k
    by_cases hki : k = c.i <;> by_cases hkj : k = c.j <;> simp [rest, hki, hkj]
  have hs : (∑ k ∈ rest, (applyFace c v k).axisCount) = ∑ k ∈ rest, (v k).axisCount := by
    apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ c.i := by simpa [rest] using (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ c.j := (Finset.mem_erase.mp hk).1
    simp [applyFace, hki, hkj]
  unfold faceAxisCount
  rw [hu]
  simp only [Finset.sum_insert hi', Finset.sum_insert hj]
  rw [hs]
  have hlocal := face_axis_balance (v c.i) (v c.j)
  simp only [applyFace, hij.symm, if_false, if_true] at *
  omega

def faceCollisionCount {n : ℕ} : List (Comparator n) → (Fin n → FaceSignal) → ℕ
  | [], _ => 0
  | c :: cs, v => (if oppositeAxes (v c.i) (v c.j) then 1 else 0) +
      faceCollisionCount cs (applyFace c v)

theorem execFace_axis_balance {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → FaceSignal) :
    faceAxisCount (execFace net v) + 2 * faceCollisionCount net.comparators v =
      faceAxisCount v := by
  obtain ⟨cs⟩ := net
  induction cs generalizing v with
  | nil => simp [execFace, faceCollisionCount]
  | cons c cs ih =>
    have hlocal := applyFace_axis_balance c v
    have htail := ih (applyFace c v)
    simp only [execFace, List.foldl_cons, faceCollisionCount] at *
    by_cases h : oppositeAxes (v c.i) (v c.j) <;> simp only [h, if_true, if_false] at * <;> omega

/-- A proper two-axis face can coalesce only once, irrespective of depth. -/
theorem proper_face_collision_bound {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → FaceSignal) (proper : faceAxisCount v = 2) :
    faceCollisionCount net.comparators v ≤ 1 := by
  have h := execFace_axis_balance net v
  rw [proper] at h
  omega

theorem proper_face_coalesced_iff_collision {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → FaceSignal) (proper : faceAxisCount v = 2) :
    faceAxisCount (execFace net v) = 0 ↔ faceCollisionCount net.comparators v = 1 := by
  have h := execFace_axis_balance net v
  rw [proper] at h
  omega

/-- Once the two middle runs agree, every continuation keeps them equal. -/
theorem face_coalescence_irreversible {n : ℕ} (net : ComparatorNetwork n)
    (v : Fin n → FaceSignal) (coalesced : ∀ k, (v k).axisCount = 0) :
    ∀ k, (execFace net v k).axisCount = 0 := by
  have h : (fun k ↦ (v k).eval true false) = (fun k ↦ (v k).eval false true) := by
    funext k
    exact (face_middle_equal_iff (v k)).mpr (coalesced k)
  have he := congrArg net.exec h
  rw [← execFace_eval, ← execFace_eval] at he
  intro k
  exact (face_middle_equal_iff (execFace net v k)).mp (congrFun he k)

end Kahale
