import D2ScheduleReserve

namespace Chvatal.D2Reserve

/-- Ports cut a line into ten consecutive intervals: the two end ports and
eight child ports. -/
def d2RankPortsHit (cuts : Nat → Nat) (lo hi : Nat) : Finset (Fin 10) :=
  Finset.univ.filter fun p => cuts p.val < hi ∧ lo < cuts (p.val + 1)

/-- A dirty interval no wider than every child port can meet at most two
ports. Any three touched ports would force the interval to contain the whole
middle child port. This is the local branching fact needed to propagate the
two-grid provider's 832-wire dirty band through a D2 sender. -/
theorem d2_dirty_interval_hits_at_most_two_ports
    (cuts : Nat → Nat) (bandWidth lo hi : Nat)
    (hmono : Monotone cuts)
    (hchild : ∀ j, j < 8 → bandWidth + cuts (j + 1) ≤ cuts (j + 2))
    (hband : lo < hi ∧ hi - lo ≤ bandWidth) :
    (d2RankPortsHit cuts lo hi).card ≤ 2 := by
  by_contra hnot
  have hthree : 2 < (d2RankPortsHit cuts lo hi).card := by omega
  rcases Finset.two_lt_card.mp hthree with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  simp only [d2RankPortsHit, Finset.mem_filter, Finset.mem_univ, true_and]
    at ha hb hc
  have horder :
      (a.val < b.val ∧ b.val < c.val) ∨
      (a.val < c.val ∧ c.val < b.val) ∨
      (b.val < a.val ∧ a.val < c.val) ∨
      (b.val < c.val ∧ c.val < a.val) ∨
      (c.val < a.val ∧ a.val < b.val) ∨
      (c.val < b.val ∧ b.val < a.val) := by omega
  rcases hband with ⟨hlohi, hwidth⟩
  have hmiddle (x y z : Nat) (hx : x < 10) (hy : y < 10) (hz : z < 10)
      (hxy : x < y) (hyz : y < z)
      (hstart : lo < cuts (x + 1)) (hfinish : cuts z < hi) : False := by
    have hypos : 1 ≤ y := by omega
    have hylt9 : y < 9 := by omega
    have hyInternal : y - 1 < 8 := by omega
    have hgap := hchild (y - 1) hyInternal
    have hidx1 : y - 1 + 1 = y := Nat.sub_add_cancel hypos
    have hidx2 : y - 1 + 2 = y + 1 := by omega
    rw [hidx1, hidx2] at hgap
    have hleft : lo < cuts y := by
      have hstep : x + 1 ≤ y := by omega
      exact lt_of_lt_of_le hstart (hmono hstep)
    have hright : cuts (y + 1) < hi := by
      have hstep : y + 1 ≤ z := by omega
      exact lt_of_le_of_lt (hmono hstep) hfinish
    omega
  rcases horder with h1 | h2 | h3 | h4 | h5 | h6
  · exact hmiddle a.val b.val c.val a.isLt b.isLt c.isLt h1.1 h1.2 ha.2 hc.1
  · exact hmiddle a.val c.val b.val a.isLt c.isLt b.isLt h2.1 h2.2 ha.2 hb.1
  · exact hmiddle b.val a.val c.val b.isLt a.isLt c.isLt h3.1 h3.2 hb.2 hc.1
  · exact hmiddle b.val c.val a.val b.isLt c.isLt a.isLt h4.1 h4.2 hb.2 ha.1
  · exact hmiddle c.val a.val b.val c.isLt a.isLt b.isLt h5.1 h5.2 hc.2 hb.1
  · exact hmiddle c.val b.val a.val c.isLt b.isLt a.isLt h6.1 h6.2 hc.2 ha.1

end Chvatal.D2Reserve
