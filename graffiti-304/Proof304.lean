import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-! Written on the Wall II #304. The edge-neighborhood and degree lemmas
are adapted from the standalone proof of companion #305.
The clique observation is related to Theorem 10 of DeLaViña, Goddard,
Henning, Pepper and Vaughan, Bounds on the total domination number
of a graph (2007). AI Village's August 24 note on the Mar. 1, 2007
total-domination block proves the corona case of #304.
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/wowiiaii.pdf
Checked with Lean 4.19.0 and Mathlib v4.19.0. -/

namespace Graffiti304

open Finset SimpleGraph
noncomputable section

variable {V : Type*} [Fintype V]
local instance : DecidableEq V := Classical.decEq V
local instance (H : SimpleGraph V) : DecidableRel H.Adj := Classical.decRel H.Adj

def edgeNeighborhood (H : SimpleGraph V) (u v : V) : Finset V :=
  H.neighborFinset u ∪ H.neighborFinset v

def maxEdgeNeighborhood (H : SimpleGraph V) : ℕ :=
  univ.sup (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)

theorem edgeNeighborhood_le_max (H : SimpleGraph V) {u v : V} (h : H.Adj u v) :
    (edgeNeighborhood H u v).card ≤ maxEdgeNeighborhood H :=
  (le_sup (f := fun v => (edgeNeighborhood H u v).card) (mem_filter.mpr ⟨mem_univ _,h⟩)).trans
    (le_sup (f := fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card) (mem_univ u))

private theorem edgeNeighborhood_spec {H : SimpleGraph V} {u v w : V} :
    w ∈ edgeNeighborhood H u v ↔ H.Adj u w ∨ H.Adj v w := by
  simp [edgeNeighborhood]

private theorem at_least_two {H : SimpleGraph V} {u v : V} (h : H.Adj u v) :
    2 ≤ maxEdgeNeighborhood H := by
  have hS : ({u,v} : Finset V) ⊆ edgeNeighborhood H u v := by
    intro w hw
    simp only [mem_insert,mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact edgeNeighborhood_spec.mpr (Or.inr h.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl h)
  have hcard := (card_le_card hS).trans (edgeNeighborhood_le_max H h)
  simpa [h.ne] using hcard

def TotalDominates (G : SimpleGraph V) (D : Finset V) : Prop := ∀ v, ∃ w ∈ D, G.Adj v w

def totalDominationNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}

theorem degree_add_one_le_max_if_nonisolated (H : SimpleGraph V) (u : V)
    (h : ∃ v, H.Adj u v) : H.degree u + 1 ≤ maxEdgeNeighborhood H := by
  obtain ⟨v,hv⟩ := h
  have hs : insert u (H.neighborFinset u) ⊆ edgeNeighborhood H u v := by
    intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact edgeNeighborhood_spec.mpr (Or.inr hv.symm)
    · exact edgeNeighborhood_spec.mpr (Or.inl ((H.mem_neighborFinset _ _).mp hw))
  have hn : u ∉ H.neighborFinset u := by simp
  have hcard := (card_le_card hs).trans (edgeNeighborhood_le_max H hv)
  simpa [card_insert_of_not_mem hn] using hcard

theorem complement_edge_neighborhood_lower (G : SimpleGraph V)
    (he : ∃ u v, Gᶜ.Adj u v) : Fintype.card V - G.minDegree ≤ maxEdgeNeighborhood Gᶜ := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  obtain ⟨u,hu⟩ := G.exists_minimal_degree_vertex
  have hd := G.degree_compl (v := u)
  have ha := G.degree_compl (v := a)
  have hp := (Gᶜ.degree_pos_iff_exists_adj a).mpr ⟨b,hab⟩
  have hm := G.minDegree_le_degree a
  have hpos : 0 < Gᶜ.degree u := by omega
  have h := degree_add_one_le_max_if_nonisolated Gᶜ u ((Gᶜ.degree_pos_iff_exists_adj u).mp hpos)
  have eq : Gᶜ.degree u + 1 = Fintype.card V - G.minDegree := by
    rw [hd, ← hu]
    have hmu : G.minDegree ≤ Fintype.card V - 1 := by omega
    omega
  have hh : Gᶜ.degree u + 1 ≤ maxEdgeNeighborhood Gᶜ := by
    convert h using 2
    congr 1
    apply Subsingleton.elim
  exact eq.ge.trans hh


private theorem compl_edge_neighborhood_complement {G : SimpleGraph V}
    {u v : V} (h : Gᶜ.Adj u v) :
    (univ : Finset V) \ edgeNeighborhood Gᶜ u v = G.neighborFinset u ∩ G.neighborFinset v := by
  ext w
  simp only [mem_sdiff,mem_univ,true_and,edgeNeighborhood_spec,mem_inter,mem_neighborFinset]
  constructor
  · intro hw
    have hwu : u ≠ w := fun e => hw (Or.inr (e ▸ h.symm))
    have hwv : v ≠ w := fun e => hw (Or.inl (e ▸ h))
    exact ⟨Classical.byContradiction (fun e => hw (Or.inl ⟨hwu,e⟩)),
      Classical.byContradiction (fun e => hw (Or.inr ⟨hwv,e⟩))⟩
  · rintro ⟨ha,hb⟩ (h₁ | h₂)
    · exact h₁.2 ha
    · exact h₂.2 hb

private theorem nonadj_common_cap {G : SimpleGraph V} {u v : V}
    (h : Gᶜ.Adj u v) :
    Fintype.card V - maxEdgeNeighborhood Gᶜ ≤
      (G.neighborFinset u ∩ G.neighborFinset v).card := by
  rw [← compl_edge_neighborhood_complement h, card_sdiff (subset_univ _),card_univ]
  exact Nat.sub_le_sub_left (edgeNeighborhood_le_max Gᶜ h) _

private theorem gamma_le_of_minDegree {G : SimpleGraph V} [Nonempty V] (hd : 0 < G.minDegree) :
    totalDominationNumber G ≤ Fintype.card V - G.minDegree + 1 := by
  have hnpos : 0 < Fintype.card V := Fintype.card_pos
  obtain ⟨D,_,hD⟩ := exists_subset_card_eq (s := (univ : Finset V))
    (n := Fintype.card V - G.minDegree + 1) (by rw [card_univ]; omega)
  apply Nat.sInf_le
  refine ⟨D, ?_, hD⟩
  intro w
  by_contra h
  have hs : G.neighborFinset w ⊆ univ \ D := by
    intro v hv
    exact mem_sdiff.mpr ⟨mem_univ _,fun hmem => h ⟨v,hmem,(G.mem_neighborFinset _ _).mp hv⟩⟩
  have hcard := card_le_card hs
  rw [card_sdiff (subset_univ _),card_univ,card_neighborFinset_eq_degree,hD] at hcard
  have hw := G.minDegree_le_degree w
  omega

theorem max_attained (H : SimpleGraph V) (he : ∃ u v, H.Adj u v) :
    ∃ u v, H.Adj u v ∧ (edgeNeighborhood H u v).card = maxEdgeNeighborhood H := by
  obtain ⟨a,b,hab⟩ := he
  haveI : Nonempty V := ⟨a⟩
  have hpos := at_least_two hab
  obtain ⟨u,_,hu⟩ := exists_mem_eq_sup (univ : Finset V) univ_nonempty
    (fun u => (univ.filter (H.Adj u)).sup fun v => (edgeNeighborhood H u v).card)
  change maxEdgeNeighborhood H = _ at hu
  have hun : (univ.filter (H.Adj u)).Nonempty := by
    by_contra! hn
    rw [not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty] at hu
    change maxEdgeNeighborhood H = 0 at hu
    omega
  obtain ⟨v,hv,hd⟩ := exists_mem_eq_sup (univ.filter (H.Adj u)) hun
    (fun v => (edgeNeighborhood H u v).card)
  exact ⟨u,v,(mem_filter.mp hv).2,(hu.trans hd).symm⟩

theorem empty_edge_max (H : SimpleGraph V) (he : ¬ ∃ u v, H.Adj u v) :
    maxEdgeNeighborhood H = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le_iff.mpr
  intro u _
  apply Finset.sup_le_iff.mpr
  intro v hv
  exact (he ⟨u,v,(mem_filter.mp hv).2⟩).elim


omit [Fintype V] in
private def Clique (G : SimpleGraph V) (Q : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ Q → ∀ ⦃v⦄, v ∈ Q → u ≠ v → G.Adj u v

omit [Fintype V] in
def Independent (H : SimpleGraph V) (Q : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ Q → ∀ ⦃v⦄, v ∈ Q → u ≠ v → ¬H.Adj u v

omit [Fintype V] in
private theorem independent_compl_iff {G : SimpleGraph V} {Q : Finset V} :
    Independent Gᶜ Q ↔ Clique G Q := by
  constructor
  · intro h u hu v hv hne
    by_contra hn
    exact h hu hv hne ⟨hne,hn⟩
  · intro h u hu v hv hne hc
    exact hc.2 (h hu hv hne)

local instance (H : SimpleGraph V) (Q : Finset V) : Decidable (Independent H Q) :=
  Classical.propDecidable _

private theorem mem_open_neighbors (H : SimpleGraph V) (v q : V) :
    q ∈ univ.filter (H.Adj v) ↔ H.Adj v q := by simp

def localIndependence (H : SimpleGraph V) (v : V) : ℕ :=
  ((univ.filter (H.Adj v)).powerset.filter (fun Q => Independent H Q)).sup card

def maxLocalIndependence (H : SimpleGraph V) : ℕ := univ.sup (localIndependence H)

def maxLocalFrequency (H : SimpleGraph V) : ℕ :=
  (univ.filter fun v => localIndependence H v = maxLocalIndependence H).card

private theorem local_le_max (H : SimpleGraph V) (v : V) :
    localIndependence H v ≤ maxLocalIndependence H :=
  le_sup (mem_univ v)

private theorem local_ge_of_set {H : SimpleGraph V} {v : V} {Q : Finset V}
    (hN : Q ⊆ univ.filter (H.Adj v)) (hI : Independent H Q) :
    Q.card ≤ localIndependence H v :=
  le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hN, hI⟩)

private theorem local_ge_of_clique {G : SimpleGraph V} {v : V} {Q : Finset V}
    (hQ : Clique G Q) (hN : ∀ q ∈ Q, Gᶜ.Adj v q) :
    Q.card ≤ localIndependence Gᶜ v :=
  local_ge_of_set (fun q hq => (mem_open_neighbors Gᶜ v q).mpr (hN q hq))
    (independent_compl_iff.mpr hQ)

private theorem max_local_witness (H : SimpleGraph V) [Nonempty V] :
    ∃ v, ∃ Q : Finset V, Q ⊆ univ.filter (H.Adj v) ∧
      Independent H Q ∧ Q.card = maxLocalIndependence H := by
  obtain ⟨v,_,hv⟩ := exists_mem_eq_sup univ univ_nonempty (localIndependence H)
  let P := (univ.filter (H.Adj v)).powerset.filter (fun Q => Independent H Q)
  have hP : P.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [Independent]⟩⟩
  obtain ⟨Q,hQ,hc⟩ := exists_mem_eq_sup P hP card
  exact ⟨v,Q,mem_powerset.mp (mem_filter.mp hQ).1,(mem_filter.mp hQ).2,(hv.trans hc).symm⟩

private theorem freq_ge_of_subset {H : SimpleGraph V} {S : Finset V}
    (h : ∀ v ∈ S, maxLocalIndependence H ≤ localIndependence H v) :
    S.card ≤ maxLocalFrequency H :=
  card_le_card (fun v hv => mem_filter.mpr
    ⟨mem_univ _, (local_le_max H v).antisymm (h v hv)⟩)

private theorem max_edge_le_order (H : SimpleGraph V) :
    maxEdgeNeighborhood H ≤ Fintype.card V := by
  apply Finset.sup_le
  intro v _
  apply Finset.sup_le
  intro w _
  exact (card_le_card (subset_univ (edgeNeighborhood H v w))).trans_eq card_univ

private def DominatesAt (G : SimpleGraph V) (S : Finset V) (v : V) : Prop :=
  ∃ u ∈ S, G.Adj v u

omit [Fintype V] in
private theorem dominates_mono {G : SimpleGraph V} {S T : Finset V} {v : V}
    (h : DominatesAt G S v) (hst : S ⊆ T) : DominatesAt G T v := by
  obtain ⟨u,hu,ha⟩ := h
  exact ⟨u,hst hu,ha⟩

private theorem adj_of_connected {G : SimpleGraph V} (hc : G.Connected)
    (hn : 1 < Fintype.card V) (v : V) : ∃ w, G.Adj v w := by
  obtain ⟨u,hu⟩ := Fintype.exists_ne_of_one_lt_card hn v
  obtain ⟨p⟩ := hc v u
  cases p with
  | nil => exact (hu rfl).elim
  | cons h _ => exact ⟨_,h⟩

omit [Fintype V] in
private theorem gamma_le_size {G : SimpleGraph V} {S : Finset V}
    (h : TotalDominates G S) : totalDominationNumber G ≤ S.card :=
  Nat.sInf_le ⟨S,h,rfl⟩

omit [Fintype V] in
/-- Cover the remaining vertices individually, with at most one addition each. -/
private theorem extend_cover (G : SimpleGraph V) (hn : ∀ v, ∃ w, G.Adj v w)
    (R S : Finset V) (h : ∀ v ∉ R, DominatesAt G S v) :
    totalDominationNumber G ≤ S.card + R.card := by
  induction R using Finset.induction_on generalizing S with
  | empty => simpa using gamma_le_size (S := S) (fun v => h v (not_mem_empty v))
  | @insert v U hv ih =>
    obtain ⟨w,hw⟩ := hn v
    have h' (x : V) (hx : x ∉ U) : DominatesAt G (insert w S) x := by
      by_cases hxv : x = v
      · subst x
        exact ⟨w,mem_insert_self _ _,hw⟩
      · exact dominates_mono (h x (by simp [hxv,hx])) (subset_insert _ _)
    have h₁ := ih _ h'
    have h₂ := card_insert_le w S
    rw [card_insert_of_not_mem hv]
    omega

omit [Fintype V] in
private theorem select_neighbors (G : SimpleGraph V) (R Q : Finset V)
    (h : ∀ v ∈ R, DominatesAt G Q v) :
    ∃ D ⊆ Q, D.card ≤ R.card ∧ ∀ v ∈ R, DominatesAt G D v := by
  induction R using Finset.induction_on with
  | empty => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | @insert v R hv ih =>
    obtain ⟨w,hw,ha⟩ := h v (mem_insert_self _ _)
    obtain ⟨D,hd,hcard,hdom⟩ := ih (fun x hx => h x (mem_insert_of_mem hx))
    refine ⟨insert w D, insert_subset hw hd, ?_, ?_⟩
    · rw [card_insert_of_not_mem hv]
      exact (card_insert_le _ _).trans (by omega)
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact ⟨w,mem_insert_self _ _,ha⟩
      · exact dominates_mono (hdom x hx) (subset_insert _ _)

omit [Fintype V] in
private theorem select_neighbors_at_least (G : SimpleGraph V) (R Q : Finset V)
    (h : ∀ v ∈ R, DominatesAt G Q v) (m : ℕ) (hm : m ≤ Q.card) :
    ∃ D ⊆ Q, m ≤ D.card ∧ D.card ≤ max m R.card ∧
      ∀ v ∈ R, DominatesAt G D v := by
  obtain ⟨D,hd,hcard,hdom⟩ := select_neighbors G R Q h
  obtain ⟨E,he,hE⟩ := exists_subset_card_eq (s := Q \ D) (n := m - D.card) (by
    rw [card_sdiff hd]; omega)
  have hin : E ⊆ Q := he.trans sdiff_subset
  have hdis : Disjoint D E := disjoint_left.mpr (fun x hx hx' => (mem_sdiff.mp (he hx')).2 hx)
  refine ⟨D ∪ E,union_subset hd hin,?_,?_,fun v hv => dominates_mono (hdom v hv) subset_union_left⟩
  · rw [card_union_of_disjoint hdis,hE]
    omega
  · rw [card_union_of_disjoint hdis,hE]
    omega

omit [Fintype V] in
private theorem clique_covers {G : SimpleGraph V} {Q D : Finset V}
    (hQ : Clique G Q) (hD : D ⊆ Q) (hd : 2 ≤ D.card) (v : V) (hv : v ∈ Q) :
    DominatesAt G D v := by
  obtain ⟨u,hu,hne⟩ := exists_ne_of_one_lt_card (by omega : 1 < D.card) v
  exact ⟨u,hu,hQ hv (hD hu) hne.symm⟩

omit [Fintype V] in
private theorem no_edge_cross_walk {G : SimpleGraph V} {A : Finset V}
    (h : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A) {u v : V} (p : G.Walk u v) :
    u ∈ A → v ∈ A := by
  induction p with
  | nil => exact id
  | cons ha _ ih => exact fun hu => ih (h _ hu _ ha)

omit [Fintype V] in
private theorem exists_cross_edge {G : SimpleGraph V} (hc : G.Connected)
    (A : Finset V) (ha : A.Nonempty) (hb : ∃ q, q ∉ A) :
    ∃ x ∈ A, ∃ y ∉ A, G.Adj x y := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨q,hq⟩ := hb
  obtain ⟨p⟩ := hc x q
  by_contra! h
  exact hq (no_edge_cross_walk (fun u hu v huv => by
    by_contra hv
    exact h u hu v hv huv) p hx)


set_option maxHeartbeats 1500000 in
private theorem bound_from_clique (G : SimpleGraph V) (hc : G.Connected)
    (hn : 1 < Fintype.card V) (Q : Finset V)
    (hQ : Clique G Q) (hq₂ : 2 ≤ Q.card)
    (hmax : Q.card = maxLocalIndependence Gᶜ)
    (hw : ∃ x, ∀ q ∈ Q, Gᶜ.Adj x q) :
    2 * totalDominationNumber G ≤ maxEdgeNeighborhood Gᶜ + maxLocalFrequency Gᶜ := by
  classical
  let A := univ.filter (fun x => ¬DominatesAt G Q x)
  let B := (univ : Finset V) \ (A ∪ Q)
  let c := Fintype.card V - maxEdgeNeighborhood Gᶜ
  have hA (x : V) : x ∈ A ↔ ¬DominatesAt G Q x := by simp [A]
  have hB (y : V) : y ∈ B ↔ y ∉ A ∧ y ∉ Q := by simp [B]
  have qNotA {q : V} (hq : q ∈ Q) : q ∉ A :=
    fun h => (hA q).mp h (clique_covers hQ Subset.rfl hq₂ q hq)
  have hQA : Disjoint A Q := disjoint_left.mpr (fun _ ha hq => qNotA hq ha)
  have hCard : Fintype.card V = A.card + Q.card + B.card := by
    have h := card_sdiff (subset_univ (A ∪ Q))
    rw [card_univ, card_union_of_disjoint hQA] at h
    have hle := card_le_card (subset_univ (A ∪ Q))
    rw [card_univ, card_union_of_disjoint hQA] at hle
    change B.card = _ at h
    omega
  have hAdjacent := adj_of_connected hc hn
  have ha : A.Nonempty := by
    obtain ⟨x,hx⟩ := hw
    exact ⟨x,(hA x).mpr (fun ⟨q,hq,ha⟩ => (hx q hq).2 ha)⟩
  have hcompl {x q : V} (hx : x ∈ A) (hq : q ∈ Q) : Gᶜ.Adj x q :=
    ⟨fun e => qNotA hq (e ▸ hx), fun h => (hA x).mp hx ⟨q,hq,h⟩⟩
  have hFreq : A.card ≤ maxLocalFrequency Gᶜ := by
    apply freq_ge_of_subset
    intro x hx
    rw [← hmax]
    exact local_ge_of_clique hQ (fun _ hq => hcompl hx hq)
  have hUpper : totalDominationNumber G ≤ Q.card + A.card := by
    apply extend_cover G hAdjacent
    intro x hx
    by_contra h
    exact hx ((hA x).mpr h)
  have hRel : maxEdgeNeighborhood Gᶜ + c = Fintype.card V := by
    have h := max_edge_le_order Gᶜ
    dsimp [c]
    omega
  have hBdom (v : V) (hv : v ∈ B) : DominatesAt G Q v := by
    by_contra h
    exact ((hB v).mp hv).1 ((hA v).mpr h)
  have hCommon {x q : V} (hx : x ∈ A) (hq : q ∈ Q) :
      c ≤ (G.neighborFinset x ∩ G.neighborFinset q).card :=
    nonadj_common_cap (hcompl hx hq)
  have hCommonSub {x q : V} (hx : x ∈ A) (hq : q ∈ Q) :
      G.neighborFinset x ∩ G.neighborFinset q ⊆ B ∩ G.neighborFinset x := by
    intro w hw
    have hxw := (G.mem_neighborFinset _ _).mp (mem_inter.mp hw).1
    have hqw := (G.mem_neighborFinset _ _).mp (mem_inter.mp hw).2
    have hwA : w ∉ A := fun hea => (hA w).mp hea ⟨q,hq,hqw.symm⟩
    have hwQ : w ∉ Q := fun heq => (hA x).mp hx ⟨w,heq,hxw⟩
    exact mem_inter.mpr ⟨(hB w).mpr ⟨hwA,hwQ⟩,(mem_inter.mp hw).1⟩
  have pair_bound {x y q : V} (hx : x ∈ A) (hq : q ∈ Q)
      (hxy : G.Adj x y) (hqy : G.Adj q y)
      (hcover : ∀ v ∈ B, DominatesAt G {q,y} v) :
      totalDominationNumber G ≤ A.card + 1 := by
    have hb := extend_cover G hAdjacent (A.erase x) {q,y} (by
      intro v hv
      by_cases he : v = x
      · subst v
        exact ⟨y,by simp,hxy⟩
      by_cases hvq : v ∈ Q
      · by_cases eq : v=q
        · subst v
          exact ⟨y,by simp,hqy⟩
        · exact ⟨q,by simp,hQ hvq hq eq⟩
      · have hva : v ∉ A := fun h => hv (mem_erase.mpr ⟨he,h⟩)
        exact hcover v ((hB v).mpr ⟨hva,hvq⟩))
    rw [card_erase_of_mem hx] at hb
    have hh : ({q,y} : Finset V).card ≤ 2 := (card_insert_le _ _).trans (by simp)
    have hpos := card_pos.mpr ha
    omega
  by_cases hc₀ : c = 0
  · by_cases hb₂ : 2 ≤ B.card
    · obtain ⟨D,hD,hd,hds,hcov⟩ := select_neighbors_at_least G B Q hBdom 2 hq₂
      have hγ := extend_cover G hAdjacent A D (by
        intro v hv
        by_cases h : v ∈ Q
        · exact clique_covers hQ hD hd v h
        · exact hcov v ((hB v).mpr ⟨hv,h⟩))
      rw [max_eq_right hb₂] at hds
      omega
    · obtain ⟨q,hq⟩ := card_pos.mp (show 0 < Q.card by omega)
      obtain ⟨x,hx,y,hy,hxy⟩ := exists_cross_edge hc A ha ⟨q,qNotA hq⟩
      have hyq : y ∉ Q := fun h => (hcompl hx h).2 hxy
      have hyb := (hB y).mpr ⟨hy,hyq⟩
      obtain ⟨r,hr,hyr⟩ := hBdom y hyb
      have hγ := pair_bound hx hr hxy hyr.symm (by
        intro v hv
        have he := card_le_one.mp (by omega : B.card ≤ 1) v hv y hyb
        subst v
        exact ⟨r,by simp,hyr⟩)
      have hpos := card_pos.mpr ⟨y,hyb⟩
      omega
  have hcpos : 0 < c := by omega
  obtain ⟨x,hx⟩ := ha
  obtain ⟨q,hq⟩ := card_pos.mp (show 0 < Q.card by omega)
  let N := B ∩ G.neighborFinset x
  have hN : c ≤ N.card := (hCommon hx hq).trans (card_le_card (hCommonSub hx hq))
  have hnB : N.card ≤ B.card := card_le_card inter_subset_left
  have get_y (v : V) (hv : v ∈ Q) : ∃ y ∈ N, G.Adj v y := by
    obtain ⟨y,hy⟩ := card_pos.mp (hcpos.trans_le (hCommon hx hv))
    exact ⟨y,hCommonSub hx hv hy,(G.mem_neighborFinset _ _).mp (mem_inter.mp hy).2⟩
  have adj_x {y : V} (hy : y ∈ N) : G.Adj x y :=
    (G.mem_neighborFinset _ _).mp (mem_inter.mp hy).2
  have hSaving : totalDominationNumber G ≤ A.card + 1 + max 1 (B.card - N.card) := by
    let U := B \ N
    obtain ⟨D,hD,hDpos,hDcard,hDcov⟩ := select_neighbors_at_least G U Q
      (fun v hv => hBdom v (mem_sdiff.mp hv).1) 1 (by omega)
    obtain ⟨r,hr⟩ := card_pos.mp (show 0 < D.card by omega)
    obtain ⟨y,hy,hry⟩ := get_y r (hD hr)
    let S := insert x (insert y D)
    have hγ := extend_cover G hAdjacent (A.erase x) S (by
      intro v hv
      by_cases hvx : v = x
      · subst v
        exact ⟨y,mem_insert_of_mem (mem_insert_self _ _),adj_x hy⟩
      by_cases hvq : v ∈ Q
      · by_cases hvr : v = r
        · subst v
          exact ⟨y,mem_insert_of_mem (mem_insert_self _ _),hry⟩
        · exact ⟨r,mem_insert_of_mem (mem_insert_of_mem hr),hQ hvq (hD hr) hvr⟩
      have hvb := (hB v).mpr ⟨fun h => hv (mem_erase.mpr ⟨hvx,h⟩),hvq⟩
      by_cases hvn : v ∈ N
      · exact ⟨x,mem_insert_self _ _,(adj_x hvn).symm⟩
      · exact dominates_mono (hDcov v (mem_sdiff.mpr ⟨hvb,hvn⟩))
          ((subset_insert y D).trans (subset_insert x (insert y D))))
    have hS : S.card ≤ D.card + 2 :=
      (card_insert_le _ _).trans (by have h := card_insert_le y D; omega)
    have hU : U.card = B.card - N.card := card_sdiff inter_subset_left
    rw [hU] at hDcard
    rw [card_erase_of_mem hx] at hγ
    have hpos := card_pos.mpr ⟨x,hx⟩
    omega
  by_cases hidx : B.card = c
  · have heq : G.neighborFinset x ∩ G.neighborFinset q = N :=
      eq_of_subset_of_card_le (hCommonSub hx hq) (by
        have h := hCommon hx hq
        omega)
    have hNB : N = B := eq_of_subset_of_card_le inter_subset_left (by omega)
    obtain ⟨y,hy,hqy⟩ := get_y q hq
    have hγ := pair_bound hx hq (adj_x hy) hqy (by
      intro v hv
      have hev : v ∈ (G.neighborFinset x ∩ G.neighborFinset q) := by rwa [heq,hNB]
      exact ⟨q,by simp,((G.mem_neighborFinset _ _).mp (mem_inter.mp hev).2).symm⟩)
    omega
  have hs : totalDominationNumber G ≤ A.card + (B.card - c) + 1 := by omega
  by_cases hcrit : Q.card = B.card - c + 1
  · by_cases hf : A.card = maxLocalFrequency Gᶜ
    · have avoid {v : V} {T : Finset V} (hv : v ∉ A) (ht : Clique G T)
          (hnc : T.card = Q.card) (hdis : ∀ w ∈ T, Gᶜ.Adj v w) : False := by
        let F := univ.filter (fun w => localIndependence Gᶜ w = maxLocalIndependence Gᶜ)
        have hass : A ⊆ F := by
          intro w hw
          have h := local_ge_of_clique hQ (fun _ hq' => hcompl hw hq')
          rw [hmax] at h
          exact mem_filter.mpr ⟨mem_univ _,(local_le_max _ _).antisymm h⟩
        have heq : A = F := eq_of_subset_of_card_le hass (by
          change maxLocalFrequency Gᶜ ≤ A.card
          omega)
        have hloc := local_ge_of_clique ht hdis
        rw [hnc,hmax] at hloc
        apply hv
        rw [heq]
        exact mem_filter.mpr ⟨mem_univ _,(local_le_max _ _).antisymm hloc⟩
      by_cases ht : Q.card = 2
      · obtain ⟨y,hy,hqy⟩ := get_y q hq
        have hγ := pair_bound hx hq (adj_x hy) hqy (by
          intro v hv
          by_contra hnD
          have hvq : ¬G.Adj v q := fun h => hnD ⟨q,by simp,h⟩
          have hvy : ¬G.Adj v y := fun h => hnD ⟨y,by simp,h⟩
          have hneQ : v ≠ q := fun e => ((hB v).mp hv).2 (e ▸ hq)
          have hneY : v ≠ y := fun e => hvq (e ▸ hqy.symm)
          apply avoid ((hB v).mp hv).1 (T := {q,y})
          · intro a ha b hb hab
            simp only [mem_insert,mem_singleton] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact (hab rfl).elim
            · exact hqy
            · exact hqy.symm
            · exact (hab rfl).elim
          · simp [hqy.ne,ht]
          · intro w hw
            simp only [mem_insert,mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact ⟨hneQ,hvq⟩
            · exact ⟨hneY,hvy⟩)
        omega
      by_cases hNc : N.card = c
      · obtain ⟨y,hy,hqy⟩ := get_y q hq
        have hyB : y ∈ B := (mem_inter.mp hy).1
        have hyQ := ((hB y).mp hyB).2
        have hFull (r : V) (hr : r ∈ Q) : G.Adj r y := by
          have heq : G.neighborFinset x ∩ G.neighborFinset r = N :=
            eq_of_subset_of_card_le (hCommonSub hx hr) (by
              rw [hNc]
              exact hCommon hx hr)
          have h : y ∈ G.neighborFinset x ∩ G.neighborFinset r := by rwa [heq]
          have h := (mem_inter.mp h).2
          exact (G.mem_neighborFinset _ _).mp h
        let D := insert y (Q.erase q)
        have hDy : y ∈ D := mem_insert_self _ _
        have hcard : D.card = Q.card := by
          have hy' : y ∉ Q.erase q := fun h => hyQ (mem_of_mem_erase h)
          have hpos : 0 < Q.card := by omega
          dsimp [D]
          rw [card_insert_of_not_mem hy',card_erase_of_mem hq]
          omega
        have hcl : Clique G D := by
          intro u hu v hv huv
          change u ∈ insert y (Q.erase q) at hu
          change v ∈ insert y (Q.erase q) at hv
          rcases mem_insert.mp hu with hue | hu <;> rcases mem_insert.mp hv with hve | hv
          · exact (huv (hue.trans hve.symm)).elim
          · rw [hue]
            exact (hFull _ (mem_of_mem_erase hv)).symm
          · rw [hve]
            exact hFull _ (mem_of_mem_erase hu)
          · exact hQ (mem_of_mem_erase hu) (mem_of_mem_erase hv) huv
        have hγ := extend_cover G hAdjacent (A.erase x) D (by
          intro v hv
          by_cases hvx : v = x
          · subst v
            exact ⟨y,hDy,adj_x hy⟩
          by_cases hvq : v ∈ Q
          · exact ⟨y,hDy,hFull _ hvq⟩
          have hva : v ∉ A := fun h => hv (mem_erase.mpr ⟨hvx,h⟩)
          apply Classical.byContradiction
          intro hnD
          apply avoid hva hcl hcard
          intro w hw
          have hne : v ≠ w := by
            intro e
            subst w
            exact hnD (clique_covers hcl Subset.rfl (by omega) v hw)
          exact ⟨hne,fun h => hnD ⟨w,hw,h⟩⟩)
        rw [hcard,card_erase_of_mem hx] at hγ
        have hpos := card_pos.mpr ⟨x,hx⟩
        omega
      · omega
    · omega
  · omega


private theorem one_local_le_of_adj {H : SimpleGraph V} {u v : V} (h : H.Adj u v) :
    1 ≤ localIndependence H u := by
  have hsub : ({v} : Finset V) ⊆ univ.filter (H.Adj u) := by
    intro w hw
    rw [mem_singleton.mp hw]
    exact mem_filter.mpr ⟨mem_univ _,h⟩
  simpa using local_ge_of_set hsub (by simp [Independent])

private theorem local_zero_of_isolated {H : SimpleGraph V} {u : V}
    (hu : ¬∃ v, H.Adj u v) : localIndependence H u = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro Q hQ
  have hsub := mem_powerset.mp (mem_filter.mp hQ).1
  have hEmpty : Q = ∅ := by
    ext v
    simp only [not_mem_empty, iff_false]
    intro hv
    exact hu ⟨v,(mem_filter.mp (hsub hv)).2⟩
  simp [hEmpty]

omit [Fintype V] in
private theorem gamma_le_two_of_universal {G : SimpleGraph V} {u : V}
    (hu : ¬∃ w, Gᶜ.Adj u w) (hadj : ∀ x, ∃ y, G.Adj x y) :
    totalDominationNumber G ≤ 2 := by
  obtain ⟨v,hv⟩ := hadj u
  have h := gamma_le_size (S := {u,v}) (by
    intro w
    by_cases hw : w = u
    · subst w
      exact ⟨v,by simp,hv⟩
    · have hw' : G.Adj u w := by
        by_contra h
        exact hu ⟨w,Ne.symm hw,h⟩
      exact ⟨u,by simp,hw'.symm⟩)
  simpa [hv.ne] using h

private theorem two_le_gamma {G : SimpleGraph V} [Nonempty V]
    (hadj : ∀ x, ∃ y, G.Adj x y) : 2 ≤ totalDominationNumber G := by
  have hex : {k : ℕ | ∃ D : Finset V, TotalDominates G D ∧ D.card = k}.Nonempty := by
    refine ⟨Fintype.card V,univ,?_,card_univ⟩
    intro w
    obtain ⟨v,hv⟩ := hadj w
    exact ⟨v,mem_univ _,hv⟩
  obtain ⟨D,hD,hd⟩ := Nat.sInf_mem hex
  obtain ⟨w⟩ := (inferInstance : Nonempty V)
  obtain ⟨u,hu,_⟩ := hD w
  obtain ⟨v,hv,huv⟩ := hD u
  have ht := one_lt_card.mpr ⟨u,hu,v,hv,huv.ne⟩
  change D.card = totalDominationNumber G at hd
  omega

private theorem min_degree_ge_two_of_common_no_universal {G : SimpleGraph V} [Nonempty V]
    (hadj : ∀ v, ∃ w, G.Adj v w) (hu : ∀ v, ∃ w, Gᶜ.Adj v w)
    (hc : 0 < Fintype.card V - maxEdgeNeighborhood Gᶜ) :
    2 ≤ G.minDegree := by
  obtain ⟨v,hv⟩ := G.exists_minimal_degree_vertex
  by_contra! h
  obtain ⟨y,hy⟩ := hadj v
  obtain ⟨w,hw⟩ := hu y
  have hN : (G.neighborFinset v).card ≤ 1 := by
    rw [card_neighborFinset_eq_degree, ← hv]
    omega
  have hyN : y ∈ G.neighborFinset v := (G.mem_neighborFinset _ _).mpr hy
  have only_y (u : V) (hu : G.Adj v u) : u = y :=
    card_le_one.mp hN u ((G.mem_neighborFinset _ _).mpr hu) y hyN
  have hvw : Gᶜ.Adj v w := by
    refine ⟨?_,fun h => hw.ne (only_y w h).symm⟩
    intro e
    exact hw.2 (e ▸ hy.symm)
  have hCommon := nonadj_common_cap hvw
  obtain ⟨a,ha⟩ := card_pos.mp (hc.trans_le hCommon)
  have hEq := only_y a ((G.mem_neighborFinset _ _).mp (mem_inter.mp ha).1)
  have hwa := (G.mem_neighborFinset _ _).mp (mem_inter.mp ha).2
  exact hw.2 (hEq ▸ hwa.symm)

private theorem bound_when_max_local_one {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v)
    (hmax : maxLocalIndependence Gᶜ = 1) :
    2 * totalDominationNumber G ≤ maxEdgeNeighborhood Gᶜ + maxLocalFrequency Gᶜ := by
  classical
  haveI := hc.nonempty
  obtain ⟨u,v,huv⟩ := he
  have hadj := adj_of_connected hc (by omega)
  have hM := at_least_two huv
  by_cases huni : ∃ w, ¬∃ a, Gᶜ.Adj w a
  · obtain ⟨w,hw⟩ := huni
    have hγ := gamma_le_two_of_universal hw hadj
    have hs : ({u,v} : Finset V).card ≤ maxLocalFrequency Gᶜ := by
      apply freq_ge_of_subset
      intro a ha
      rw [hmax]
      simp only [mem_insert,mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact one_local_le_of_adj huv
      · exact one_local_le_of_adj huv.symm
    simp [huv.ne] at hs
    omega
  · have hu (w : V) : ∃ a, Gᶜ.Adj w a := by
      by_contra h
      exact huni ⟨w,h⟩
    have hf : Fintype.card V ≤ maxLocalFrequency Gᶜ := by
      rw [← card_univ]
      apply freq_ge_of_subset
      intro w _
      obtain ⟨a,ha⟩ := hu w
      rw [hmax]
      exact one_local_le_of_adj ha
    have hδ : 0 < G.minDegree := by
      obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
      rw [hz]
      exact (G.degree_pos_iff_exists_adj z).mpr (hadj z)
    have hG := gamma_le_of_minDegree hδ
    have hC := complement_edge_neighborhood_lower G ⟨u,v,huv⟩
    by_cases h₁ : maxEdgeNeighborhood Gᶜ + 2 ≤ Fintype.card V
    · omega
    by_cases h₂ : maxEdgeNeighborhood Gᶜ = Fintype.card V
    · have hγ := gamma_le_size (S := univ) (G := G) (by
        intro x
        obtain ⟨y,hy⟩ := hadj x
        exact ⟨y,mem_univ _,hy⟩)
      rw [card_univ] at hγ
      omega
    have hM' := max_edge_le_order Gᶜ
    have hδ' := min_degree_ge_two_of_common_no_universal hadj hu (by omega)
    omega

theorem conjecture304_integer {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v) :
    2 * totalDominationNumber G ≤ maxEdgeNeighborhood Gᶜ + maxLocalFrequency Gᶜ := by
  haveI := hc.nonempty
  obtain ⟨x,Q,hsub,hind,hmax⟩ := max_local_witness Gᶜ
  have hpos : 1 ≤ maxLocalIndependence Gᶜ := by
    obtain ⟨u,v,huv⟩ := he
    exact (one_local_le_of_adj huv).trans (local_le_max _ _)
  by_cases ht : maxLocalIndependence Gᶜ = 1
  · exact bound_when_max_local_one hc hn he ht
  · apply bound_from_clique G hc (by omega) Q (independent_compl_iff.mp hind) (by omega) hmax
    exact ⟨x,fun q hq => (mem_open_neighbors Gᶜ x q).mp (hsub hq)⟩

/-- The exact rational inequality on its domain with a nonempty complement edge set. -/
theorem conjecture304 {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ∃ u v, Gᶜ.Adj u v) :
    (totalDominationNumber G : ℚ) ≤
      ((maxLocalFrequency Gᶜ : ℚ) + (maxEdgeNeighborhood Gᶜ : ℚ)) / 2 := by
  rw [le_div_iff₀ (by decide : (0 : ℚ) < 2)]
  have h := conjecture304_integer hc hn he
  exact_mod_cast (show totalDominationNumber G * 2 ≤
    maxLocalFrequency Gᶜ + maxEdgeNeighborhood Gᶜ by omega)

/-- Under the zero convention for the empty maximum, the complete-graph case
holds exactly from order four onward. -/
theorem empty_max_zero_complete_iff {G : SimpleGraph V} (hc : G.Connected)
    (hn : 3 ≤ Fintype.card V) (he : ¬∃ u v, Gᶜ.Adj u v) :
    ((totalDominationNumber G : ℚ) ≤
      ((maxLocalFrequency Gᶜ : ℚ) + (maxEdgeNeighborhood Gᶜ : ℚ)) / 2) ↔
    4 ≤ Fintype.card V := by
  haveI := hc.nonempty
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  have hadj := adj_of_connected hc (by omega)
  have h₂ := gamma_le_two_of_universal (u := u) (fun ⟨v,h⟩ => he ⟨u,v,h⟩) hadj
  have h₂' := two_le_gamma hadj
  have hGamma : totalDominationNumber G = 2 := h₂.antisymm h₂'
  have hloc (v : V) : localIndependence Gᶜ v = 0 :=
    local_zero_of_isolated (fun ⟨w,h⟩ => he ⟨v,w,h⟩)
  have hmax : maxLocalIndependence Gᶜ = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro v _
    rw [hloc]
  have hf : maxLocalFrequency Gᶜ = Fintype.card V := by simp [maxLocalFrequency,hmax,hloc]
  rw [hGamma,hf,empty_edge_max Gᶜ he,le_div_iff₀ (by decide : (0 : ℚ) < 2)]
  norm_num

/-- The triangle is a counterexample to the convention with empty maximum zero. -/
theorem triangle_counterexample :
    ¬ ((totalDominationNumber (⊤ : SimpleGraph (Fin 3)) : ℚ) ≤
      ((maxLocalFrequency (⊤ : SimpleGraph (Fin 3))ᶜ : ℚ) +
      (maxEdgeNeighborhood (⊤ : SimpleGraph (Fin 3))ᶜ : ℚ)) / 2) := by
  have he : ¬ ∃ u v, (⊤ : SimpleGraph (Fin 3))ᶜ.Adj u v := by
    simp
  intro h
  have hb := (empty_max_zero_complete_iff top_connected (by simp) he).mp h
  simp at hb

#print axioms triangle_counterexample
#print axioms conjecture304
#print axioms empty_max_zero_complete_iff
#print axioms max_attained

end
end Graffiti304
