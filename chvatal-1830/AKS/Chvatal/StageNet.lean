module
/-
  # Stage network of the Chvatal tree network

  At time `t` every node `b` runs its own node network on its own wire set `S b`
  (pairwise disjoint, different cardinalities). The node network of size `(S b).card` is
  embedded along `(S b).orderEmbOfFin rfl` (the k-th smallest wire plays cell k).
  Heterogeneous analogue of `parallelScatterFlat`.

  Status: generic in `S` and `nodeNet`; execution on each node's wires, depth, outside
  wires, and value-permutation are proved.
-/

public import AKS.Chvatal.Tree
public import AKS.Sort.Depth
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace Chvatal

/-! ## Finiteness of `KBag` -/

/-- `KBag br d` is equivalent to the sigma type of levels and indices. -/
def KBag.equivSigma (br d : ℕ) : KBag br d ≃ Σ l : Fin (d + 1), Fin (br ^ l.val) where
  toFun b := ⟨⟨b.l, Nat.lt_succ_of_le b.hl⟩, ⟨b.x, b.hx⟩⟩
  invFun s := ⟨s.1.val, s.2.val, Nat.le_of_lt_succ s.1.isLt, s.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance KBag.instFintype (br d : ℕ) : Fintype (KBag br d) :=
  Fintype.ofEquiv _ (KBag.equivSigma br d).symm

/-- All nodes, without repetition. -/
noncomputable def nodeList (br d : ℕ) : List (KBag br d) := (Finset.univ : Finset (KBag br d)).toList

theorem mem_nodeList {br d : ℕ} (b : KBag br d) : b ∈ nodeList br d := by
  simp [nodeList]

theorem nodeList_nodup (br d : ℕ) : (nodeList br d).Nodup :=
  Finset.nodup_toList _

/-! ## The stage network -/

/-- The stage network: node networks `nodeNet b (S b).card`, each embedded along
`(S b).orderEmbOfFin rfl` (comparator `⟨i,j,h⟩ ↦ ⟨e i, e j, e.lt_iff_lt.2 h⟩`, i.e.
`scatterEmbed`), concatenated over all nodes. -/
noncomputable def stageNet {d : ℕ} (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (nodeNet : (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n) : ComparatorNetwork (64 ^ d) :=
  ⟨(nodeList 64 d).flatMap fun b =>
    ((nodeNet b (S b).card).scatterEmbed (64 ^ d) ((S b).orderEmbOfFin rfl)).comparators⟩

/-- Generic heterogeneous-family execution lemma. -/
theorem flatMap_scatter_exec_inside {ι : Type*} [DecidableEq ι] {n : ℕ} {α : Type*}
    [LinearOrder α] {m : ι → ℕ} (e : (a : ι) → (Fin (m a) ↪o Fin n))
    (net : (a : ι) → ComparatorNetwork (m a)) :
    ∀ (ys : List ι) (v : Fin n → α), ys.Nodup →
      (∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → ∀ i j, e a i ≠ e b j) →
      ∀ t ∈ ys, ∀ k : Fin (m t),
        ys.foldl (fun v' a => ((net a).scatterEmbed n (e a)).exec v') v (e t k) =
          (net t).exec (v ∘ e t) k := by
  intro ys
  induction ys with
  | nil => intro v _ _ t ht; cases ht
  | cons x ys ih =>
    intro v hnodup hdis t ht k
    have hnodup_t : ys.Nodup := (List.nodup_cons.mp hnodup).2
    have hx_nin : x ∉ ys := (List.nodup_cons.mp hnodup).1
    have hdis_t : ∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → ∀ i j, e a i ≠ e b j :=
      fun a ha b hb hne =>
        hdis a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hne
    simp only [List.foldl_cons, List.mem_cons] at ht ⊢
    rcases ht with rfl | ht
    · have hinside := ComparatorNetwork.scatterEmbed_exec_inside (net t) n (e t) v k
      have hrest :
          ys.foldl (fun v' a => ((net a).scatterEmbed n (e a)).exec v')
            (((net t).scatterEmbed n (e t)).exec v) (e t k) =
            ((net t).scatterEmbed n (e t)).exec v (e t k) := by
        refine ComparatorNetwork.foldl_exec_outside ys
          (fun a => (net a).scatterEmbed n (e a)) _ (e t k) ?_
        intro a ha c hc
        have hne : a ≠ t := fun heq => hx_nin (heq ▸ ha)
        have hj : e t k ∉ Set.range (e a) := by
          rintro ⟨p, hp⟩
          exact hdis t List.mem_cons_self a (List.mem_cons_of_mem _ ha)
            (Ne.symm hne) k p hp.symm
        exact ComparatorNetwork.scatterEmbed_comparators_outside (net a) n (e a)
          (e t k) hj c hc
      rw [hrest, hinside]
    · have hne : x ≠ t := fun heq => hx_nin (heq ▸ ht)
      have hw' : (((net x).scatterEmbed n (e x)).exec v) ∘ e t = v ∘ e t := by
        funext l
        apply ComparatorNetwork.scatterEmbed_exec_outside
        rintro ⟨i, hi⟩
        exact hdis t (List.mem_cons_of_mem _ ht) x List.mem_cons_self
          (Ne.symm hne) l i hi.symm
      have hih := ih (((net x).scatterEmbed n (e x)).exec v) hnodup_t hdis_t t ht k
      simpa [hw'] using hih

theorem orderEmb_disjoint {N : ℕ} {A B : Finset (Fin N)} (h : Disjoint A B)
    (i : Fin A.card) (j : Fin B.card) :
    (A.orderEmbOfFin rfl) i ≠ (B.orderEmbOfFin rfl) j := by
  intro heq
  have h1 : (A.orderEmbOfFin rfl) i ∈ A := Finset.orderEmbOfFin_mem A rfl i
  have h2 : (B.orderEmbOfFin rfl) j ∈ B := Finset.orderEmbOfFin_mem B rfl j
  exact Finset.disjoint_left.mp h h1 (heq ▸ h2)

/-- On the wires of node `b`, the stage network runs `nodeNet b (S b).card` on the local view. -/
theorem stageNet_exec_inside {d : ℕ} {α : Type*} [LinearOrder α]
    (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (v : Fin (64 ^ d) → α) (b : KBag 64 d) (k : Fin (S b).card) :
    (stageNet S nodeNet).exec v (((S b).orderEmbOfFin rfl) k) =
      (nodeNet b (S b).card).exec (fun i => v (((S b).orderEmbOfFin rfl) i)) k := by
  have hflat := ComparatorNetwork.exec_flatMap (nodeList 64 d)
    (fun a => (nodeNet a (S a).card).scatterEmbed (64 ^ d) ((S a).orderEmbOfFin rfl)) v
  change (⟨(nodeList 64 d).flatMap fun a =>
    ((nodeNet a (S a).card).scatterEmbed (64 ^ d) ((S a).orderEmbOfFin rfl)).comparators⟩ :
      ComparatorNetwork (64 ^ d)).exec v _ = _
  rw [hflat]
  exact flatMap_scatter_exec_inside (m := fun a => (S a).card)
    (fun a => (S a).orderEmbOfFin rfl) (fun a => nodeNet a (S a).card)
    (nodeList 64 d) v (nodeList_nodup 64 d)
    (fun a _ c _ hne i j => orderEmb_disjoint (hS a c hne) i j) b (mem_nodeList b) k

/-- Wire-disjoint concatenation has depth at most the maximum of the parts. -/
theorem stageNet_depth_le {d D : ℕ} (S : KBag 64 d → Finset (Fin (64 ^ d)))
    (hS : ∀ b b', b ≠ b' → Disjoint (S b) (S b'))
    (nodeNet : (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n)
    (hD : ∀ b, (nodeNet b (S b).card).depth ≤ D) :
    (stageNet S nodeNet).depth ≤ D := by
  refine depth_flatMap_disjoint (nodeList 64 d)
    (fun a => ((nodeNet a (S a).card).scatterEmbed (64 ^ d)
      ((S a).orderEmbOfFin rfl)).comparators) D ?_ ?_
  · intro b _
    exact (depth_scatterEmbed_le _ _ _).trans (hD b)
  · refine List.Pairwise.imp ?_ ((List.nodup_iff_pairwise_ne).mp (nodeList_nodup 64 d))
    intro a c hne c1 hc1 c2 hc2
    obtain ⟨d1, _, rfl⟩ := List.mem_map.mp hc1
    obtain ⟨d2, _, rfl⟩ := List.mem_map.mp hc2
    have h := fun i j => orderEmb_disjoint (hS a c hne) i j
    exact ⟨⟨h _ _, h _ _⟩, ⟨h _ _, h _ _⟩⟩





end Chvatal
