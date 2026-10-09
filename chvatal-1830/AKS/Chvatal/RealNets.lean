module

public import AKS.Chvatal.KernelSetup
public import AKS.Chvatal.PackSpec
public import AKS.Chvatal.FlipSpec
public import AKS.Chvatal.PhysicalPack
public import AKS.Chvatal.NodeGeom
public import AKS.Chvatal.GeneralParams
public import AKS.Bitonic.TightDepth

@[expose] public section

namespace Chvatal

def castNet {n n' : ℕ} (h : n = n') (net : ComparatorNetwork n) : ComparatorNetwork n' := by
  subst h; exact net


theorem exec_eq_self_of_sorts {a : ℕ} (net : ComparatorNetwork a) (hs : ComparatorNetwork.Sorts.{0} net)
    (x : Equiv.Perm (Fin a)) (c : Fin a) : net.exec (x : Fin a → Fin a) c = c := by
  have hm : Monotone (net.exec (x : Fin a → Fin a)) := hs (Fin a) _
  have hinj := net.exec_injective x.injective
  have hsm := hm.strictMono_of_injective hinj
  have hsurj := Finite.surjective_of_injective hinj
  have h2 : (net.exec (x : Fin a → Fin a)) = id :=
    by
      have hsub : Subsingleton (Fin a ≃o Fin a) := inferInstance
      have := hsub.elim (StrictMono.orderIsoOfSurjective _ hsm hsurj) (OrderIso.refl _)
      funext c
      exact congrArg (fun e : Fin a ≃o Fin a => e c) this
  rw [h2]; rfl

theorem specJmax_le_real (π j : ℕ) (hj : j ≤ specJmax π) :
    (j : ℝ) ≤ (128 / 4095 : ℝ) * ((π : ℝ) / 2) :=
  (Nat.cast_le.2 hj).trans (Nat.floor_le (by positivity))

theorem specJmax_le_half (π : ℕ) : specJmax π ≤ π / 2 := by
  have h := specJmax_le_real π _ le_rfl
  have hπ : (0 : ℝ) ≤ π := Nat.cast_nonneg _
  have h2 : (2 * specJmax π : ℝ) ≤ π := by nlinarith
  have h3 : 2 * specJmax π ≤ π := by exact_mod_cast h2
  omega

theorem NodeSpec_of_sorts {a : ℕ} (π τ : ℕ) (net : ComparatorNetwork a) (hs : ComparatorNetwork.Sorts.{0} net)
    {EB εF : ℝ} (hEB : 0 ≤ EB) (hε : 0 < εF) {Jmax : ℕ} (hJ : Jmax ≤ π / 2) :
    NodeSpec a π τ net EB Jmax εF := by
  have hid := exec_eq_self_of_sorts net hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p _ _
    have : (Finset.univ.filter fun c : Fin a =>
        a - p ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - p) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]; simpa using hEB
  · intro x p _ _
    have : (Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < p ∧ p ≤ c.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]; simpa using hEB
  · intro x j hj hjJ _
    have : (Finset.univ.filter fun c : Fin a =>
        a - j ≤ (net.exec (x : Fin a → Fin a) c).val ∧ c.val < a - π / 2) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]
    have : (0 : ℝ) < j := by exact_mod_cast hj
    simpa using mul_pos hε this
  · intro x j hj hjJ _
    have : (Finset.univ.filter fun c : Fin a =>
        (net.exec (x : Fin a → Fin a) c).val < j ∧ π / 2 ≤ c.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro c _ ⟨h1, h2⟩
      rw [hid x c] at h1
      omega
    rw [this]
    have : (0 : ℝ) < j := by exact_mod_cast hj
    simpa using mul_pos hε this

theorem hasPackSemanticPropertyF_zero {m n : ℕ} (hn : 0 < n) {σ : Scramble m n}
    (pack : SortScrambleSortPack m n hn σ) (hfm : 0 ≤ m) (deltaF epsF : ℝ) :
    HasPackSemanticPropertyF hn pack 0 hfm deltaF epsF := by
  intro v j hj hjd
  exfalso
  simp at hjd
  omega

theorem packNodeSpec {m n f b : ℕ} (hn : 0 < n) (σ : Scramble m n)
    (hmfb : m = 2 * f + 64 * b) (hfm : f ≤ m) {epsB EB : ℝ}
    (hEB : EB = epsB / 2 * ((m * n : ℕ) : ℝ))
    (hB1 : HasPackSemanticPropertyB hn (canonicalSortScrambleSortPack m n hn σ) epsB)
    (hB2 : HasPackSemanticPropertyB hn
      (canonicalSortScrambleSortPack m n hn (flipScramble σ)) epsB)
    (hF : 0 < f →
      HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm
        (128 / 4095) eps ∧
      HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn (flipScramble σ)) f hfm
        (128 / 4095) eps) :
    NodeSpec (m * n) (2 * f * n) (b * n) (physicalPackNet m n hn σ) EB
      (specJmax (2 * f * n)) eps := by
  have hFF : HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn σ) f hfm
        (128 / 4095) eps ∧
      HasPackSemanticPropertyF hn (canonicalSortScrambleSortPack m n hn (flipScramble σ)) f hfm
        (128 / 4095) eps := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · subst h0
      exact ⟨hasPackSemanticPropertyF_zero hn _ _ _ _, hasPackSemanticPropertyF_zero hn _ _ _ _⟩
    · exact hF h0
  have hH := packSpec_high hn σ hmfb hfm hB1 hFF.1
  have hL := packSpec_low hn σ hmfb hfm hB2 hFF.2
  have hconv : ∀ j : ℕ, j ≤ specJmax (2 * f * n) → (j : ℝ) ≤ (128 / 4095 : ℝ) * (f * n) := by
    intro j hj
    have h := specJmax_le_real _ j hj
    have e : ((2 * f * n : ℕ) : ℝ) / 2 = f * n := by push_cast; ring
    rwa [e] at h
  have hEB' : epsB / 2 * ((m : ℝ) * n) = EB := by rw [hEB]; push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x p hp hpa
    exact (hH.1 x p hp hpa).trans (le_of_eq hEB')
  · intro x p hp hpa
    exact (hL.1 x p hp hpa).trans (le_of_eq hEB')
  · intro x j hj hjJ hja
    exact hH.2 x j hj (hconv j hjJ) hja
  · intro x j hj hjJ hja
    exact hL.2 x j hj (hconv j hjJ)

theorem pack_depth_le (m n : ℕ) (hn : 0 < n) (σ : Scramble m n) (k : ℕ) (hm : m ≤ 2 ^ k) :
    (physicalPackNet m n hn σ).depth ≤ k * (k + 1) := by
  refine (physicalPackNet_depth_le_budget m n hn σ).trans ?_
  have h1 : Nat.clog 2 m ≤ k := by
    have := Nat.clog_mono_right 2 hm
    rwa [Nat.clog_pow 2 k (by norm_num)] at this
  have h2 := bitonicDepthBudget_mono h1
  have := bitonicDepthBudget_double k
  omega

theorem bitonic_depth_le_small (a : ℕ) (h : a ≤ 2 ^ 64) : (bitonicNetwork a).depth ≤ 2080 := by
  refine (bitonicNetwork_depth_le_budget a).trans ?_
  have h1 : Nat.clog 2 a ≤ 64 := by
    have := Nat.clog_mono_right 2 h
    rwa [Nat.clog_pow 2 64 (by norm_num)] at this
  have h2 := bitonicDepthBudget_mono h1
  have : bitonicDepthBudget 64 = 2080 := by rw [bitonicDepthBudget_eq]
  omega

/-- Depth budget of a node network. -/
def depthBound (t : ℕ) : ℕ := if t = 0 then 6320 else 3660

/-- The node network `net` of a node with `a` wires (`up` to the parent, `down` to each child)
at stage `t` meets the Theorem 5.1 guarantee `NodeSpec` with the `RealSpecs` budgets and has
depth within `depthBound t`. -/
def NodeGood (t a up down : ℕ) (net : ComparatorNetwork a) : Prop :=
  NodeSpec a up down net (specEB t a) (specJmax up) eps ∧ net.depth ≤ depthBound t

theorem specEB_nonneg (t a : ℕ) : 0 ≤ specEB t a := by
  unfold specEB paperRootEpsB paperOrdinaryEpsB
  split_ifs <;> positivity

theorem nodeGood_small (t a up down : ℕ) (h : a ≤ 2 ^ 64) :
    ∃ net : ComparatorNetwork a, NodeGood t a up down net := by
  refine ⟨bitonicNetwork a, NodeSpec_of_sorts up down _ (bitonicNetwork_sorts a)
    (specEB_nonneg t a) eps_pos (specJmax_le_half up), ?_⟩
  have := bitonic_depth_le_small a h
  unfold depthBound; split_ifs <;> omega

theorem nodeGood_geom (t a up down : ℕ) (ht : 1 ≤ t) (G : NodeGeom a up down) :
    ∃ net : ComparatorNetwork a, NodeGood t a up down net := by
  obtain ⟨m, n, f, b, hm, ha, hup, hdown, hm1, hm2, hn, hf⟩ := G
  subst ha hup hdown
  have hn0 : 0 < n := by omega
  have h59 : 2 ^ 59 ≤ m := hm1.le
  have h100 : 100 ≤ m := le_trans (by norm_num) h59
  have hfm : f ≤ m := by omega
  have hEB : specEB t (m * n) = paperOrdinaryEpsB / 2 * ((m * n : ℕ) : ℝ) := by
    unfold specEB
    rw [if_neg (by omega)]; ring
  have hD : ∀ σ : Scramble m n, (physicalPackNet m n hn0 σ).depth ≤ depthBound t := by
    intro σ
    have := pack_depth_le m n hn0 σ 60 hm2
    unfold depthBound; rw [if_neg (by omega)]; omega
  rcases hf with rfl | ⟨hfbig, hfev⟩
  · obtain ⟨σ, hB1, hB2⟩ := ExistsScrambleSeparator_twoSided_B h100 hn
      (epsB_general h59)
    refine ⟨physicalPackNet m n hn0 σ, ?_, hD σ⟩
    exact packNodeSpec hn0 σ hm hfm hEB hB1 hB2 (fun h => absurd h (lt_irrefl 0))
  · have hf10 : 10 ≤ f := le_trans (by norm_num) hfbig
    let g : ScrambleGeometry := ScrambleGeometry.ofShape m n b f 64 h100 hn hf10 hfev
      (by omega)
    obtain ⟨σ, ⟨hB1, hF1⟩, ⟨hB2, hF2⟩⟩ :=
      ExistsScrambleSeparator_twoSided (g := g)
        (P := theorem51Params_general g hfbig h59) hfbig le_rfl le_rfl
    refine ⟨physicalPackNet m n hn0 σ, ?_, hD σ⟩
    exact packNodeSpec hn0 σ hm hfm hEB hB1 hB2 (fun _ => ⟨hF1, hF2⟩)

theorem nodeGood_root (d : ℕ) (hd : 14 ≤ d) (a up down : ℕ) (ha : a = 64 ^ d) (hup : up = 0)
    (hdown : down = 64 ^ (d - 1)) :
    ∃ net : ComparatorNetwork a, NodeGood 0 a up down net := by
  obtain ⟨e, he⟩ : ∃ e, d = e + 14 := ⟨d - 14, by omega⟩
  set nn : ℕ := 2 ^ (6 * e + 5) with hnn
  have hn16 : 16 ≤ nn := by
    rw [hnn]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (6 * e + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn0 : 0 < nn := by omega
  have hmn : a = 2 ^ 79 * nn := by
    rw [ha, he, p64, hnn, ← pow_add]; congr 1; omega
  have hdn : down = 2 ^ 73 * nn := by
    rw [hdown, he, show e + 14 - 1 = e + 13 by omega, p64, hnn, ← pow_add]; congr 1; omega
  have hup' : up = 2 * 0 * nn := by simp [hup]
  subst hmn hdn hup'
  have h79 : 2 ^ 79 ≤ 2 ^ 79 := le_rfl
  have h100 : 100 ≤ 2 ^ 79 := by norm_num
  obtain ⟨σ, hB1, hB2⟩ := ExistsScrambleSeparator_twoSided_B (m := 2 ^ 79) (n := nn) h100 hn16
    (epsB_root_general (m := 2 ^ 79) le_rfl)
  refine ⟨physicalPackNet (2 ^ 79) nn hn0 σ, ?_, ?_⟩
  · refine packNodeSpec (f := 0) (b := 2 ^ 73) hn0 σ (by norm_num) (Nat.zero_le _) ?_ hB1 hB2
      (fun h => absurd h (lt_irrefl 0))
    unfold specEB
    rw [if_pos rfl]; ring
  · have := pack_depth_le (2 ^ 79) nn hn0 σ 79 le_rfl
    unfold depthBound; rw [if_pos rfl]; omega

theorem nodeGood_exists (d : ℕ) (hd : 7 ≤ d) (hd14 : 14 ≤ d) (t l : ℕ) (ht : t < tf7 d)
    (hdown : 0 < (flowSizes7 d hd).down l t) :
    ∃ net : ComparatorNetwork ((flowSizes7 d hd).a l t),
      NodeGood t ((flowSizes7 d hd).a l t) ((flowSizes7 d hd).up l t)
        ((flowSizes7 d hd).down l t) net := by
  by_cases hs : (flowSizes7 d hd).a l t ≤ 2 ^ 64
  · exact nodeGood_small _ _ _ _ hs
  by_cases h0 : t = 0
  · subst h0
    have hl : l = 0 := by
      by_contra hl
      have : (flowSizes7 d hd).down l 0 = 0 := by simp [flowSizes7, flowDown7, hl]
      omega
    subst hl
    exact nodeGood_root d hd14 _ _ _ (by simp [flowSizes7, flowA7])
      (by simp [flowSizes7, flowUp7]) (by simp [flowSizes7, flowDown7])
  · have hbig : 2 ^ 64 < flowA7 d hd l t := not_le.mp hs
    obtain ⟨G⟩ := nodeGeom_exists d hd l t hdown hbig ht
    exact nodeGood_geom t _ _ _ (by omega) G

open scoped Classical in
noncomputable def nodeNetOf (d : ℕ) (hd : 7 ≤ d) (t l : ℕ) :
    ComparatorNetwork ((flowSizes7 d hd).a l t) :=
  if hex : ∃ net : ComparatorNetwork ((flowSizes7 d hd).a l t),
      NodeGood t ((flowSizes7 d hd).a l t) ((flowSizes7 d hd).up l t)
        ((flowSizes7 d hd).down l t) net then hex.choose else ⟨[]⟩

open scoped Classical in
/-- Real tree node networks (empty where down = 0). -/
noncomputable def realNets (d : ℕ) (hd : 7 ≤ d) :
    ℕ → (b : KBag 64 d) → (n : ℕ) → ComparatorNetwork n :=
  fun t b n =>
    if h : n = (flowSizes7 d hd).a b.l t ∧ 0 < (flowSizes7 d hd).down b.l t then
      castNet h.1.symm (nodeNetOf d hd t b.l)
    else ⟨[]⟩

theorem realNets_eq (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d)
    (hdown : 0 < (flowSizes7 d hd).down b.l t) :
    realNets d hd t b ((flowSizes7 d hd).a b.l t) = nodeNetOf d hd t b.l := by
  unfold realNets
  rw [dif_pos ⟨rfl, hdown⟩]
  rfl

theorem realNets_empty (d : ℕ) (hd : 7 ≤ d) (t : ℕ) (b : KBag 64 d) (n : ℕ)
    (h : ¬ (n = (flowSizes7 d hd).a b.l t ∧ 0 < (flowSizes7 d hd).down b.l t)) :
    realNets d hd t b n = ⟨[]⟩ := by
  unfold realNets
  rw [dif_neg h]

theorem nodeNetOf_good (d : ℕ) (hd : 7 ≤ d) (hd14 : 14 ≤ d) (t l : ℕ) (ht : t < tf7 d)
    (hdown : 0 < (flowSizes7 d hd).down l t) :
    NodeGood t ((flowSizes7 d hd).a l t) ((flowSizes7 d hd).up l t)
      ((flowSizes7 d hd).down l t) (nodeNetOf d hd t l) := by
  have hex := nodeGood_exists d hd hd14 t l ht hdown
  unfold nodeNetOf
  rw [dif_pos hex]
  exact hex.choose_spec

/-- **A11 + B5c core.** The real node networks meet the node guarantee at every node that sends
wires down. -/
theorem realNets_specs {d : ℕ} (hd : 7 ≤ d) (hd14 : 14 ≤ d) : RealSpecs hd (realNets d hd) := by
  intro t q ht hdown
  have hc := wireSets_card (flowSizes7 d hd) ht.le q
  generalize (wireSets (flowSizes7 d hd) t q).card = c at hc ⊢
  subst hc
  rw [realNets_eq d hd t q hdown]
  exact (nodeNetOf_good d hd hd14 t q.l ht hdown).1

/-- **Depth.** -/
theorem realNets_depth_le {d : ℕ} (hd : 7 ≤ d) (hd14 : 14 ≤ d) (t : ℕ) (hts : t < tf7 d)
    (b : KBag 64 d) (n : ℕ) :
    (realNets d hd t b n).depth ≤ depthBound t := by
  by_cases h : n = (flowSizes7 d hd).a b.l t ∧ 0 < (flowSizes7 d hd).down b.l t
  · obtain ⟨h1, h2⟩ := h
    subst h1
    rw [realNets_eq d hd t b h2]
    exact (nodeNetOf_good d hd hd14 t b.l hts h2).2
  · rw [realNets_empty d hd t b n h]
    have : (⟨[]⟩ : ComparatorNetwork n).depth = 0 := by simp [ComparatorNetwork.depth]
    rw [this]; exact Nat.zero_le _

end Chvatal
