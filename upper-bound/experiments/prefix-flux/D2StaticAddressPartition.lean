import AKS.Chvatal.WireFlow

open Finset

namespace Chvatal.D2StaticAddressPartition

open Chvatal

/-- Monotonicity over an arbitrary finite span follows by iterating the
adjacent-boundary hypothesis. -/
theorem boundary_mono_of_le {ports : Nat} (boundary : Nat → Nat)
    (hmono : forall i, i < ports → boundary i ≤ boundary (i + 1))
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ ports) : boundary i ≤ boundary j := by
  have haux : forall d, d ≤ j - i → boundary i ≤ boundary (i + d) := by
    intro d hd
    induction d with
    | zero => simp
    | succ d ih =>
        have hdle : d ≤ j - i := by omega
        have ih' := ih hdle
        have hdidx : i + d < ports := by omega
        simpa [Nat.add_assoc] using le_trans ih' (hmono _ hdidx)
  have hidx : i + (j - i) = j := by omega
  rw [← hidx]
  exact haux _ (Nat.le_refl _)

/-- The cardinality of a rank port is the difference between its boundaries. -/
theorem ranked_ports_card {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat)
    (hend : boundary ports = s.card)
    (hmono : forall i, i < ports → boundary i ≤ boundary (i + 1))
    (i : Nat) (hi : i < ports) :
    (Chvatal.blockOf s (boundary i) (boundary (i + 1))).card =
      boundary (i + 1) - boundary i := by
  apply Chvatal.blockOf_card
  rw [← hend]
  exact boundary_mono_of_le boundary hmono (by omega) (by omega)

/-- Every rank below the final boundary belongs to one adjacent interval of a
monotone boundary sequence. Repeated boundaries are allowed, so zero-size
ports need no special case. -/
theorem boundary_interval_cover (ports : Nat) (boundary : Nat -> Nat)
    (hzero : boundary 0 = 0)
    (hmono : forall i, i < ports -> boundary i <= boundary (i + 1))
    {r : Nat} (hr : r < boundary ports) :
    exists i, i < ports /\ boundary i <= r /\ r < boundary (i + 1) := by
  induction ports generalizing r boundary with
  | zero => simp [hzero] at hr
  | succ ports ih =>
      by_cases hsmall : r < boundary ports
      · obtain ⟨i, hi, hlo, hhi⟩ :=
          ih boundary hzero (fun j hj => hmono j (by omega)) hsmall
        exact ⟨i, by omega, hlo, hhi⟩
      · refine ⟨ports, by omega, Nat.le_of_not_gt hsmall, ?_⟩
        simpa using hr

/-- Shifted cumulative boundaries partition the middle interval between two
end ports. -/
theorem boundary_interval_cover_shifted (ports : Nat) (boundary : Nat → Nat)
    (hzero : boundary 0 = 0)
    (hmono : forall i, i < ports → boundary i ≤ boundary (i + 1))
    {left r : Nat} (hleft : left ≤ r)
    (hright : r < left + boundary ports) :
    exists i, i < ports ∧ left + boundary i ≤ r ∧ r < left + boundary (i + 1) := by
  have hr' : r - left < boundary ports := by omega
  obtain ⟨i, hi, hlo, hhi⟩ :=
    boundary_interval_cover ports boundary hzero hmono hr'
  refine ⟨i, hi, ?_, ?_⟩ <;> omega

/-- A left end port, cumulative middle ports, and a right end port cover a
finite sender exactly when their widths add to its cardinality. This is the
rank-interval form used by a D2 ordinary sender. -/
theorem ranked_ports_with_sides_cover {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat → Nat) (left : Nat)
    (hzero : boundary 0 = 0)
    (hmono : forall i, i < ports → boundary i ≤ boundary (i + 1))
    (hcard : left + boundary ports + (s.card - (left + boundary ports)) = s.card) :
    (Chvatal.blockOf s 0 left ∪
      ((Finset.univ.biUnion fun i : Fin ports =>
        Chvatal.blockOf s (left + boundary i.val)
          (left + boundary (i.val + 1))) ∪
      Chvatal.blockOf s (left + boundary ports) s.card)) = s := by
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, Chvatal.mem_blockOf]
  constructor
  · rintro (hleft' | (⟨i, hmid⟩ | hright'))
    · exact hleft'.1
    · exact hmid.1
    · exact hright'.1
  · intro hw
    have hr := Chvatal.rankIn_lt_card hw
    by_cases hleft' : Chvatal.rankIn s w < left
    · exact Or.inl ⟨hw, Nat.zero_le _, hleft'⟩
    · by_cases hmid' : Chvatal.rankIn s w < left + boundary ports
      · obtain ⟨i, hi, hlo, hhi⟩ := boundary_interval_cover_shifted
          ports boundary hzero hmono (by omega) hmid'
        exact Or.inr (Or.inl ⟨⟨i, hi⟩, ⟨hw, by simpa using hlo, by simpa using hhi⟩⟩)
      · have hstart : left + boundary ports ≤ Chvatal.rankIn s w := by omega
        have hend : left + boundary ports ≤ s.card := by omega
        exact Or.inr (Or.inr ⟨hw, hstart, hr⟩)

/-- The grouped end ports and distinct middle ports in the preceding cover are
pairwise disjoint. -/
theorem ranked_ports_with_sides_disjoint {n ports : Nat}
    (s : Finset (Fin n)) (boundary : Nat → Nat) (left : Nat)
    (hmono : forall i, i < ports → boundary i ≤ boundary (i + 1))
    (hcard : left + boundary ports + (s.card - (left + boundary ports)) = s.card) :
    Disjoint
      (Chvatal.blockOf s 0 left ∪
        Chvatal.blockOf s (left + boundary ports) s.card)
      (Finset.univ.biUnion fun i : Fin ports =>
        Chvatal.blockOf s (left + boundary i.val)
          (left + boundary (i.val + 1))) ∧
      (∀ i j : Fin ports, i ≠ j →
        Disjoint
          (Chvatal.blockOf s (left + boundary i.val)
            (left + boundary (i.val + 1)))
          (Chvatal.blockOf s (left + boundary j.val)
            (left + boundary (j.val + 1)))) := by
  have hleftend : left + boundary ports ≤ s.card := by omega
  constructor
  · rw [Finset.disjoint_left]
    intro w hends hmid
    rcases Finset.mem_union.mp hends with hleft | hright
    · obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hmid
      have hlo := (Chvatal.mem_blockOf.mp hwi).2.1
      exact (Finset.disjoint_left.mp
        (Chvatal.disjoint_blockOf (show left ≤ left + boundary i.val by omega)))
        hleft hwi
    · obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hmid
      have hhi := (Chvatal.mem_blockOf.mp hwi).2.2
      have horder : boundary (i.val + 1) ≤ boundary ports :=
        Chvatal.D2StaticAddressPartition.boundary_mono_of_le boundary hmono
          (by omega) (Nat.le_refl _)
      have hdisj := Chvatal.disjoint_blockOf
        (s := s) (lo := left + boundary i.val)
        (hi := left + boundary (i.val + 1))
        (lo' := left + boundary ports) (hi' := s.card) (by omega)
      exact (Finset.disjoint_left.mp hdisj.symm) hright hwi
  · intro i j hij
    by_cases hlt : i.val < j.val
    · have horder : boundary (i.val + 1) ≤ boundary j.val :=
        Chvatal.D2StaticAddressPartition.boundary_mono_of_le boundary hmono
          (by omega) (by omega)
      exact Chvatal.disjoint_blockOf (by omega)
    · have hlt' : j.val < i.val := by omega
      have horder : boundary (j.val + 1) ≤ boundary i.val :=
        Chvatal.D2StaticAddressPartition.boundary_mono_of_le boundary hmono
          (by omega) (by omega)
      exact (Chvatal.disjoint_blockOf (by omega)).symm

/-- The rank slices cut out by adjacent boundaries cover the whole finite
sender. The wires themselves may be arbitrary or noncontiguous in physical
address; only their internal increasing rank is used. -/
theorem ranked_ports_cover {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat -> Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = s.card)
    (hmono : forall i, i < ports -> boundary i <= boundary (i + 1))
    (w : Fin n) (hw : w ∈ s) :
    exists i, i < ports /\ w ∈ Chvatal.blockOf s (boundary i) (boundary (i + 1)) := by
  have hrank := Chvatal.rankIn_lt_card hw
  obtain ⟨i, hi, hlo, hhi⟩ :=
    boundary_interval_cover ports boundary hzero hmono (by rw [hend]; exact hrank)
  refine ⟨i, hi, ?_⟩
  exact Chvatal.mem_blockOf.mpr ⟨hw, hlo, hhi⟩

/-- Rank slices from distinct adjacent boundary intervals are disjoint. -/
theorem ranked_ports_pairwise_disjoint {n ports : Nat}
    (s : Finset (Fin n)) (boundary : Nat -> Nat)
    (hmono : forall i, i < ports -> boundary i <= boundary (i + 1))
    {i j : Nat} (hj : j < ports) (hij : i < j) :
    Disjoint (Chvatal.blockOf s (boundary i) (boundary (i + 1)))
      (Chvatal.blockOf s (boundary j) (boundary (j + 1))) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  rcases Chvatal.mem_blockOf.mp hwi with ⟨_, _, hlt⟩
  rcases Chvatal.mem_blockOf.mp hwj with ⟨_, hge, _⟩
  have hstep : boundary (i + 1) <= boundary j := by
    exact boundary_mono_of_le boundary hmono (by omega) (by omega)
  omega

/-- The finite union of these disjoint rank ports is exactly the sender set. -/
theorem ranked_ports_biUnion_eq {n ports : Nat} (s : Finset (Fin n))
    (boundary : Nat -> Nat)
    (hzero : boundary 0 = 0)
    (hend : boundary ports = s.card)
    (hmono : forall i, i < ports -> boundary i <= boundary (i + 1)) :
    Finset.univ.biUnion (fun i : Fin ports =>
      Chvatal.blockOf s (boundary i.val) (boundary (i.val + 1))) = s := by
  ext w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact Chvatal.blockOf_subset hi
  · intro hw
    obtain ⟨i, hi, hmem⟩ := ranked_ports_cover s boundary
      hzero hend hmono w hw
    exact ⟨⟨i, hi⟩, hmem⟩

end Chvatal.D2StaticAddressPartition
