module

public import AKS.Kahale.CoupledFaces

/-! # Context-dependent transport of surviving Boolean faces

The pair matrix has an exact update when the baseline-bit context is retained.
No theorem here asserts that the pair matrix determines that context.
The local admissibility hypothesis is explicit: surviving proper faces have
distinct axes and constant other wires; coalesced faces have no axes.
-/

@[expose] public section

namespace Kahale

def pairAxis (a b : FaceSignal) : ℕ := if oppositeAxes a b then 1 else 0

def oneContext (a r b : FaceSignal) : ℕ :=
  if oppositeAxes a r ∧ b = .one then 1 else 0

def transportTriple (a b r : FaceSignal) : Prop :=
  ((∀ s ∈ [a, b, r], s = .zero ∨ s = .one ∨ s = .left ∨ s = .right) ∧
    [a, b, r].count .left ≤ 1 ∧ [a, b, r].count .right ≤ 1) ∨
  (∀ s ∈ [a, b, r], s.axisCount = 0)

instance (a b r : FaceSignal) : Decidable (transportTriple a b r) := by
  unfold transportTriple
  infer_instance

theorem pairAxis_min_transport (a b r : FaceSignal) :
    transportTriple a b r →
    pairAxis (faceMeet a b) r = oneContext a r b + oneContext b r a := by
  cases a <;> cases b <;> cases r <;> decide

theorem pairAxis_transport_balance (a b r : FaceSignal) :
    transportTriple a b r →
    pairAxis (faceMeet a b) r + pairAxis (faceJoin a b) r =
      pairAxis a r + pairAxis b r := by
  cases a <;> cases b <;> cases r <;> decide

theorem pairAxis_gate_kills (a b : FaceSignal) :
    pairAxis (faceMeet a b) (faceJoin a b) = 0 := by
  cases a <;> cases b <;> decide

open Finset BigOperators

def facePairMatrix {ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → Fin n → FaceSignal) (i j : Fin n) : ℕ :=
  ∑ f, pairAxis (v f i) (v f j)

def faceContextMatrix {ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → Fin n → FaceSignal) (i j b : Fin n) : ℕ :=
  ∑ f, oneContext (v f i) (v f j) (v f b)

/-- Exact incoming transport to the min endpoint, retaining baseline context. -/
theorem facePairMatrix_min_transport {ι : Type*} [Fintype ι] {n : ℕ}
    (c : Comparator n) (v : ι → Fin n → FaceSignal) (j : Fin n)
    (hji : j ≠ c.i) (hjj : j ≠ c.j)
    (h : ∀ f, transportTriple (v f c.i) (v f c.j) (v f j)) :
    facePairMatrix (fun f => applyFace c (v f)) c.i j =
      faceContextMatrix v c.i j c.j + faceContextMatrix v c.j j c.i := by
  unfold facePairMatrix faceContextMatrix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simp only [applyFace, if_neg hji, if_neg hjj]
  exact pairAxis_min_transport _ _ _ (h f)

/-- Transport redistributes the two incoming rows without losing other pairs. -/
theorem facePairMatrix_transport_balance {ι : Type*} [Fintype ι] {n : ℕ}
    (c : Comparator n) (v : ι → Fin n → FaceSignal) (j : Fin n)
    (hji : j ≠ c.i) (hjj : j ≠ c.j)
    (h : ∀ f, transportTriple (v f c.i) (v f c.j) (v f j)) :
    facePairMatrix (fun f => applyFace c (v f)) c.i j +
      facePairMatrix (fun f => applyFace c (v f)) c.j j =
      facePairMatrix v c.i j + facePairMatrix v c.j j := by
  have hne : c.j ≠ c.i := ne_of_gt c.h
  unfold facePairMatrix
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  simp only [applyFace, if_neg hne, if_neg hji, if_neg hjj]
  exact pairAxis_transport_balance _ _ _ (h f)

theorem facePairMatrix_gate_kills {ι : Type*} [Fintype ι] {n : ℕ}
    (c : Comparator n) (v : ι → Fin n → FaceSignal) :
    facePairMatrix (fun f => applyFace c (v f)) c.i c.j = 0 := by
  have hne : c.j ≠ c.i := ne_of_gt c.h
  simp [facePairMatrix, applyFace, hne, pairAxis_gate_kills]

theorem facePairMatrix_max_transport {ι : Type*} [Fintype ι] {n : ℕ}
    (c : Comparator n) (v : ι → Fin n → FaceSignal) (j : Fin n)
    (hji : j ≠ c.i) (hjj : j ≠ c.j)
    (h : ∀ f, transportTriple (v f c.i) (v f c.j) (v f j)) :
    facePairMatrix (fun f => applyFace c (v f)) c.j j =
      facePairMatrix v c.i j + facePairMatrix v c.j j -
        (faceContextMatrix v c.i j c.j + faceContextMatrix v c.j j c.i) := by
  have hmin := facePairMatrix_min_transport c v j hji hjj h
  have hbalance := facePairMatrix_transport_balance c v j hji hjj h
  omega

theorem facePairMatrix_untouched {ι : Type*} [Fintype ι] {n : ℕ}
    (c : Comparator n) (v : ι → Fin n → FaceSignal) (i j : Fin n)
    (hii : i ≠ c.i) (hij : i ≠ c.j) (hji : j ≠ c.i) (hjj : j ≠ c.j) :
    facePairMatrix (fun f => applyFace c (v f)) i j = facePairMatrix v i j := by
  simp only [facePairMatrix, applyFace, if_neg hii, if_neg hij, if_neg hji, if_neg hjj]

end Kahale
