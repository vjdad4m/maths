import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Sqrt


/-! A connected 13-vertex counterexample to Written on the Wall II #186.
The square center set has neighborhood of order 12 and eccentricity 2.
Every spanning tree has at most 4 leaves, and any induced bipartite
subgraph has order at most 11, because there are two disjoint triangles.
The theorem gives 16 > 15 for the actual catalogue inequality.
Catalogue: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json
Definitions: https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/definitions.json
Lean 4.19.0, Mathlib v4.19.0.
-/
namespace Graffiti186Counterexample
open SimpleGraph Finset
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
section Definitions
variable {W : Type*} [Fintype W]

noncomputable def eccentricity (H : SimpleGraph W) (v : W) : ℕ := univ.sup (H.dist v)

noncomputable def leaves (T : SimpleGraph W) : Finset W := by
  classical
  exact univ.filter (fun v => ∃! w, T.Adj v w)

noncomputable def maxLeaves (H : SimpleGraph W) : ℕ :=
  sSup {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k}

private theorem leafCounts_bdd (H : SimpleGraph W) :
    BddAbove {k | ∃ T : SimpleGraph W, T ≤ H ∧ T.IsTree ∧ (leaves T).card = k} := by
  refine ⟨Fintype.card W, ?_⟩
  rintro _ ⟨T, _, _, rfl⟩
  exact card_le_univ _

private theorem leaves_mem (T : SimpleGraph W) [DecidableRel T.Adj] (v : W) :
    v ∈ leaves T ↔ T.degree v = 1 := by
  classical
  simp only [leaves, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hn⟩
    have h : T.neighborFinset v = {w} := by
      ext z
      simp only [T.mem_neighborFinset, mem_singleton]
      exact ⟨hn z, fun he => he ▸ hw⟩
    rw [← T.card_neighborFinset_eq_degree, h, card_singleton]
  · intro hd
    obtain ⟨w, hw⟩ := card_eq_one.mp hd
    refine ⟨w, (T.mem_neighborFinset v w).1 (hw.symm ▸ mem_singleton_self _), ?_⟩
    intro z hz
    exact mem_singleton.mp (hw ▸ (T.mem_neighborFinset v z).2 hz)

end Definitions

section DistanceCertificate
variable {W : Type*} (H : SimpleGraph W) (label : W → W → ℕ)
variable (diag : ∀ r, label r r = 0)
variable (step : ∀ r u v, H.Adj u v → label r v ≤ label r u + 1)
variable (descent : ∀ r v, v ≠ r → ∃ w, H.Adj v w ∧ label r w + 1 = label r v)

include label descent in
private theorem reachable_from_descent (r v : W) : H.Reachable v r := by
  generalize he : label r v = n
  induction n using Nat.strong_induction_on generalizing v with
  | h n ih =>
    by_cases hv : v = r
    · subst v
      exact ⟨.nil⟩
    · obtain ⟨w, hw, hstep⟩ := descent r v hv
      exact hw.reachable.trans (ih _ (by omega) w rfl)

include label descent in
private theorem certificate_connected [Nonempty W] : H.Connected := by
  obtain ⟨r⟩ := ‹Nonempty W›
  apply (connected_iff_exists_forall_reachable _).mpr
  exact ⟨r, fun v => (reachable_from_descent H label descent r v).symm⟩

include step in
private theorem label_le_length (r : W) {v w : W} (p : H.Walk v w) :
    label r w ≤ label r v + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
    have hs := step r _ _ h
    simp only [Walk.length_cons]
    omega

include diag step descent in
theorem dist_eq_certificate [Nonempty W] (r v : W) : H.dist r v = label r v := by
  have hc := certificate_connected H label descent
  apply le_antisymm
  · generalize he : label r v = n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        rw [SimpleGraph.dist_self]
        exact Nat.zero_le _
      · obtain ⟨w, hw, hstep⟩ := descent r v hv
        have hl := ih (label r w) (by omega) w rfl
        have ht := hc.dist_triangle (u := r) (v := w) (w := v)
        rw [SimpleGraph.dist_eq_one_iff_adj.mpr hw.symm] at ht
        omega
  · obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist r v
    simpa [hp, diag] using label_le_length H label step r p

end DistanceCertificate

noncomputable section

variable {V : Type*} [Fintype V]

def square (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ G.dist x y ≤ 2
  symm := fun x y h => ⟨h.1.symm, (G.dist_comm (u := x) (v := y)) ▸ h.2⟩
  loopless := fun _ h => h.1 rfl

def diameter (G : SimpleGraph V) : ℕ := univ.sup (eccentricity G)

def squareMaxDegree (G : SimpleGraph V) : ℕ := by
  classical
  exact (square G).maxDegree

def squareNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact (square G).neighborFinset v

def bipartiteNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.powerset.filter (fun s : Finset V =>
    ∃ c : s → Bool, ∀ a b : s, G.Adj a.val b.val → c a ≠ c b)).sup Finset.card

omit [Fintype V] in
private theorem le_square (G : SimpleGraph V) : G ≤ square G :=
  fun _ _ h => ⟨h.ne, le_trans (G.dist_le h.toWalk) (by simp [Adj.toWalk])⟩

omit [Fintype V] in
private theorem square_connected {G : SimpleGraph V} (hc : G.Connected) :
    (square G).Connected := hc.mono (le_square G)

omit [Fintype V] in
private theorem dist_le_twice_square_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : (square G).Walk v w) : G.dist v w ≤ 2 * p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have h' : G.dist a b ≤ 2 := h.2
    have htri : G.dist a c ≤ G.dist a b + G.dist b c := hc.dist_triangle
    rw [Walk.length_cons]
    omega

omit [Fintype V] in
private theorem square_dist_le_half_walk {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} (p : G.Walk v w) : (square G).dist v w ≤ (p.length + 1) / 2 := by
  match p with
  | .nil => simp
  | .cons h .nil =>
    simpa [Adj.toWalk] using (square G).dist_le ((le_square G h).toWalk)
  | @Walk.cons _ _ a b c h (.cons (v := d) h' q) =>
    have htail := square_dist_le_half_walk hc q
    have hab : G.dist a b ≤ 1 := G.dist_le h.toWalk
    have hbd : G.dist b d ≤ 1 := G.dist_le h'.toWalk
    have had₀ : G.dist a d ≤ G.dist a b + G.dist b d := hc.dist_triangle
    have had : (square G).dist a d ≤ 1 := by
      by_cases heq : a = d
      · simp [heq, dist_self]
      · exact (square G).dist_le (show (square G).Adj a d from ⟨heq, by omega⟩).toWalk
    have htri : (square G).dist a c ≤ (square G).dist a d + (square G).dist d c :=
      (square_connected hc).dist_triangle
    simp only [Walk.length_cons]
    omega
termination_by p.length
decreasing_by simp only [Walk.length_cons]; omega

omit [Fintype V] in
theorem square_dist {G : SimpleGraph V} (hc : G.Connected) (v w : V) :
    (square G).dist v w = (G.dist v w + 1) / 2 := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist v w
  obtain ⟨q, hq⟩ := (square_connected hc).exists_walk_length_eq_dist v w
  have hlo := dist_le_twice_square_walk hc q
  have hhi := square_dist_le_half_walk hc p
  omega

private theorem dist_le_ecc (G : SimpleGraph V) (v w : V) :
    G.dist v w ≤ eccentricity G v := le_sup (mem_univ w)

private theorem exists_dist_eq_ecc (G : SimpleGraph V) (v : V) :
    ∃ w, eccentricity G v = G.dist v w := by
  obtain ⟨w, _, hw⟩ := exists_mem_eq_sup univ ⟨v, mem_univ v⟩ (G.dist v)
  exact ⟨w, hw⟩

private theorem square_ecc {G : SimpleGraph V} (hc : G.Connected) (v : V) :
    eccentricity (square G) v = (eccentricity G v + 1) / 2 := by
  obtain ⟨w, hw⟩ := exists_dist_eq_ecc G v
  obtain ⟨z, hz⟩ := exists_dist_eq_ecc (square G) v
  have hlo := dist_le_ecc (square G) v w
  have hhi := dist_le_ecc G v z
  rw [square_dist hc] at hlo hz
  omega

omit [Fintype V] in
private theorem take_drop_lengths {G : SimpleGraph V} {v w : V}
    (p : G.Walk v w) (i : ℕ) :
    (p.take i).length = min i p.length ∧ (p.drop i).length = p.length - i := by
  induction p generalizing i with
  | nil => cases i <;> simp [Walk.take, Walk.drop]
  | cons h p ih =>
    cases i with
    | zero => simp [Walk.take, Walk.drop]
    | succ i =>
      have h := ih i
      change (p.take i).length + 1 = min (i + 1) (p.length + 1) ∧
        (p.drop i).length = p.length + 1 - (i + 1)
      omega

omit [Fintype V] in
private theorem geodesic_prefix_suffix {G : SimpleGraph V} (hc : G.Connected)
    {v w : V} {p : G.Walk v w} (hp : p.length = G.dist v w) {i : ℕ}
    (hi : i ≤ p.length) :
    G.dist v (p.getVert i) = i ∧ G.dist (p.getVert i) w = p.length - i := by
  have ht := G.dist_le (p.take i)
  have hd := G.dist_le (p.drop i)
  have hs := take_drop_lengths p i
  have htri : G.dist v w ≤ G.dist v (p.getVert i) + G.dist (p.getVert i) w :=
    hc.dist_triangle
  simp [min_eq_left hi] at hs
  omega

/-- The square centers are exactly the minimizers of eccentricity. -/
def centers (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun v => ∀ w, eccentricity G v ≤ eccentricity G w)

def setNeighbors (H : SimpleGraph V) (S : Finset V) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ s ∈ S, H.Adj s v)

/-- Distance to a nonempty set. -/
def setDist (H : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) (v : V) : ℕ :=
  S.inf' hS (fun s => H.dist s v)

def setEcc (H : SimpleGraph V) (S : Finset V) (hS : S.Nonempty) : ℕ :=
  univ.sup (setDist H S hS)

theorem centers_nonempty {H : SimpleGraph V} (hH : H.Connected) :
    (centers H).Nonempty := by
  classical
  haveI : Nonempty V := hH.nonempty
  obtain ⟨v, hv, hm⟩ := exists_min_image (univ : Finset V) (eccentricity H) univ_nonempty
  exact ⟨v, mem_filter.mpr ⟨hv, fun w => hm w (mem_univ w)⟩⟩

omit [Fintype V] in
theorem square_setDist {G : SimpleGraph V} (hc : G.Connected) {S : Finset V}
    (hS : S.Nonempty) (v : V) :
    setDist (square G) S hS v = (setDist G S hS v + 1) / 2 := by
  obtain ⟨x, hx, hxv⟩ := exists_mem_eq_inf' hS (fun s => G.dist s v)
  obtain ⟨y, hy, hyv⟩ := exists_mem_eq_inf' hS (fun s => (square G).dist s v)
  have hlo : setDist G S hS v ≤ G.dist y v := inf'_le (fun s => G.dist s v) hy
  have hhi : setDist (square G) S hS v ≤ (square G).dist x v :=
    inf'_le (fun s => (square G).dist s v) hx
  rw [square_dist hc] at hyv hhi
  change setDist G S hS v = G.dist x v at hxv
  change setDist (square G) S hS v = (G.dist y v + 1) / 2 at hyv
  omega


end

abbrev V := Fin 13

def edges : List (V × V) := [(0, 6), (0, 7), (1, 7), (1, 8), (2, 8), (2, 9), (3, 9), (4, 10), (5, 10), (3, 11), (4, 11), (10, 11), (0, 12), (4, 12), (7, 12)]

def G : SimpleGraph V where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm _ _ := Or.symm
  loopless := by
    intro v h
    have h' : ∀ v : V, (v,v) ∉ edges := by decide +kernel
    exact h' v (h.elim id id)

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))


def maxVertices : Finset V := {0, 4, 7, 10, 11, 12}
def degreeG (v : V) : ℕ := if v ∈ maxVertices then 3 else if v = 5 ∨ v = 6 then 1 else 2
private theorem degree_G (v : V) : G.degree v = degreeG v := by
  fin_cases v <;> decide +kernel

theorem maxDegree_G : G.maxDegree = 3 := by
  apply le_antisymm
  · apply G.maxDegree_le_of_forall_degree_le
    intro v
    rw [degree_G]
    exact (show ∀ w : V, degreeG w ≤ 3 by decide +kernel) v
  · exact (show 3 ≤ G.degree (0 : V) by decide +kernel).trans (G.degree_le_maxDegree 0)

def matrix : Array (Array ℕ) := #[
  #[0, 2, 4, 4, 2, 4, 1, 1, 3, 5, 3, 3, 1],
  #[2, 0, 2, 4, 3, 5, 3, 1, 1, 3, 4, 4, 2],
  #[4, 2, 0, 2, 4, 5, 5, 3, 1, 1, 4, 3, 4],
  #[4, 4, 2, 0, 2, 3, 5, 4, 3, 1, 2, 1, 3],
  #[2, 3, 4, 2, 0, 2, 3, 2, 4, 3, 1, 1, 1],
  #[4, 5, 5, 3, 2, 0, 5, 4, 6, 4, 1, 2, 3],
  #[1, 3, 5, 5, 3, 5, 0, 2, 4, 6, 4, 4, 2],
  #[1, 1, 3, 4, 2, 4, 2, 0, 2, 4, 3, 3, 1],
  #[3, 1, 1, 3, 4, 6, 4, 2, 0, 2, 5, 4, 3],
  #[5, 3, 1, 1, 3, 4, 6, 4, 2, 0, 3, 2, 4],
  #[3, 4, 4, 2, 1, 1, 4, 3, 5, 3, 0, 1, 2],
  #[3, 4, 3, 1, 1, 2, 4, 3, 4, 2, 1, 0, 2],
  #[1, 2, 4, 3, 1, 3, 2, 1, 3, 4, 2, 2, 0]
]
def label (v w : V) : ℕ := (matrix[v.val]?.getD #[])[w.val]?.getD 0
def labelEcc (v : V) : ℕ := univ.sup (label v)

private theorem diag : ∀ v : V, label v v = 0 := by decide +kernel

set_option maxHeartbeats 10000000 in
private theorem step : ∀ r u v, G.Adj u v → label r v ≤ label r u + 1 := by
  decide +kernel

set_option maxHeartbeats 10000000 in
private theorem descent : ∀ r v, v ≠ r → ∃ w, G.Adj v w ∧ label r w + 1 = label r v := by
  decide +kernel

theorem G_connected : G.Connected := certificate_connected G label descent

private theorem connected_has_neighbor {T : SimpleGraph V} (hc : T.Connected) (v : V) :
    ∃ w, T.Adj v w := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by decide : 1 < Fintype.card V) v
  obtain ⟨p⟩ := hc v w
  cases p with
  | nil => exact (hw rfl).elim
  | cons ha _ => exact ⟨_, ha⟩

private theorem retained_at_degree_three {T : SimpleGraph V} [DecidableRel T.Adj]
    (hsub : T ≤ G) {v w : V} (ht : T.degree v = 3) (h : G.Adj v w) :
    T.Adj v w := by
  have hn : T.neighborFinset v ⊆ G.neighborFinset v := by
    intro u hu
    exact (G.mem_neighborFinset v u).mpr (hsub ((T.mem_neighborFinset v u).mp hu))
  have he : T.neighborFinset v = G.neighborFinset v := by
    apply eq_of_subset_of_card_le hn
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, ht]
    simpa [maxDegree_G] using G.degree_le_maxDegree v
  apply (T.mem_neighborFinset v w).mp
  rw [he]
  exact (G.mem_neighborFinset v w).mpr h

private theorem tree_leaf_count_eq_degree_three (T : SimpleGraph V) [DecidableRel T.Adj]
    (ht : T.IsTree) (hdeg : ∀ v, T.degree v ≤ 3) :
    (leaves T).card = (univ.filter (fun v => T.degree v = 3)).card + 2 := by
  classical
  let D : Finset V := univ.filter (fun v => T.degree v = 3)
  have eq_point (v : V) :
      T.degree v + (if v ∈ leaves T then 1 else 0) = 2 + (if v ∈ D then 1 else 0) := by
    have hpos := (T.degree_pos_iff_exists_adj v).mpr (connected_has_neighbor ht.isConnected v)
    have hle := hdeg v
    simp only [D, leaves_mem, mem_filter, mem_univ, true_and]
    split <;> split <;> omega
  have heq := Finset.sum_congr (rfl : (univ : Finset V) = univ) (fun v _ => eq_point v)
  have ind (s : Finset V) : (∑ v : V, if v ∈ s then (1 : ℕ) else 0) = s.card := by
    rw [← Finset.sum_filter]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ind, ind,
    T.sum_degrees_eq_twice_card_edges] at heq
  have hconstant : (∑ _v : V, (2 : ℕ)) = 26 := by simp
  rw [hconstant] at heq
  have hcard := ht.card_edgeFinset
  rw [Fintype.card_fin] at hcard
  change (leaves T).card = D.card + 2
  omega


private theorem tri_forces_loss {T : SimpleGraph V} [DecidableRel T.Adj]
    (hsub : T ≤ G) (ht : T.IsTree) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ¬ (T.degree a = 3 ∧ T.degree b = 3) := by
  rintro ⟨da, db⟩
  have ab := retained_at_degree_three hsub da hab
  have ac := retained_at_degree_three hsub da hac
  have bc := retained_at_degree_three hsub db hbc
  let p : T.Walk a b := ab.toWalk
  let q : T.Walk a b := .cons ac (.cons bc.symm .nil)
  have hp : p.IsPath := Walk.IsPath.of_adj ab
  have hq : q.IsPath := (Walk.IsPath.of_adj bc.symm).cons (by simp [ac.ne, ab.ne])
  have eq : (⟨p,hp⟩ : T.Path a b) = ⟨q,hq⟩ := ht.IsAcyclic.path_unique _ _
  have eq' := congrArg (fun t : T.Path a b => t.val.getVert 1) eq
  exact bc.ne (by simpa [p,q,Adj.toWalk] using eq')

private theorem restrict_two_tris (D : Finset V) (hs : D ⊆ maxVertices)
    (hleft : ∀ a ∈ D, ∀ b ∈ D, a ∈ ({0,7,12} : Finset V) →
      b ∈ ({0,7,12} : Finset V) → a = b)
    (hright : ∀ a ∈ D, ∀ b ∈ D, a ∈ ({4,10,11} : Finset V) →
      b ∈ ({4,10,11} : Finset V) → a = b) : D.card ≤ 2 := by
  let A : Finset V := D ∩ {0,7,12}
  let B : Finset V := D ∩ {4,10,11}
  have ha : A.card ≤ 1 := card_le_one.mpr (fun a ah b bh =>
    hleft a (mem_inter.mp ah).1 b (mem_inter.mp bh).1 (mem_inter.mp ah).2 (mem_inter.mp bh).2)
  have hb : B.card ≤ 1 := card_le_one.mpr (fun a ah b bh =>
    hright a (mem_inter.mp ah).1 b (mem_inter.mp bh).1 (mem_inter.mp ah).2 (mem_inter.mp bh).2)
  have himp : ∀ v : V, v ∈ maxVertices →
    v ∈ ({0,7,12} : Finset V) ∨ v ∈ ({4,10,11} : Finset V) := by decide +kernel
  have hD : D ⊆ A ∪ B := by
    intro v hv
    rcases himp v (hs hv) with h | h
    · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hv,h⟩))
    · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hv,h⟩))
  have h := (card_le_card hD).trans (card_union_le A B)
  omega

theorem maxLeaves_le_four : maxLeaves G ≤ 4 := by
  classical
  have all (T : SimpleGraph V) (hsub : T ≤ G) (ht : T.IsTree) : (leaves T).card ≤ 4 := by
    have hupper (v : V) : T.degree v ≤ 3 :=
      (T.degree_le_of_le hsub).trans (maxDegree_G ▸ G.degree_le_maxDegree v)
    have hl := tree_leaf_count_eq_degree_three T ht hupper
    let D : Finset V := univ.filter (fun v => T.degree v = 3)
    have hd (v : V) : v ∈ D ↔ T.degree v = 3 := by simp [D]
    have hs (v : V) (hv : v ∈ D) : v ∈ maxVertices := by
      have h := T.degree_le_of_le (v := v) hsub
      rw [(hd _).mp hv, degree_G] at h
      by_contra hn
      simp [degreeG, hn] at h
      split at h <;> omega
    have cup (a b : V) (hne : a ≠ b)
        (h : (a ∈ ({0,7,12} : Finset V) ∧ b ∈ ({0,7,12} : Finset V)) ∨
          (a ∈ ({4,10,11} : Finset V) ∧ b ∈ ({4,10,11} : Finset V))) :
        G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj b c := by
      have test : ∀ a b : V, a ≠ b →
          ((a ∈ ({0,7,12} : Finset V) ∧ b ∈ ({0,7,12} : Finset V)) ∨
          (a ∈ ({4,10,11} : Finset V) ∧ b ∈ ({4,10,11} : Finset V))) →
          G.Adj a b ∧ ∃ c, G.Adj a c ∧ G.Adj b c := by decide +kernel
      exact test a b hne h
    have col (a b : V) (ha : a ∈ D) (hb : b ∈ D)
        (h : (a ∈ ({0,7,12} : Finset V) ∧ b ∈ ({0,7,12} : Finset V)) ∨
          (a ∈ ({4,10,11} : Finset V) ∧ b ∈ ({4,10,11} : Finset V))) : a = b := by
      by_contra hn
      obtain ⟨hab,c,hac,hbc⟩ := cup a b hn h
      exact tri_forces_loss hsub ht hab hac hbc ⟨(hd _).mp ha,(hd _).mp hb⟩
    have hh := restrict_two_tris D (fun v hv => hs v hv)
      (fun a ha b hb h₁ h₂ => col a b ha hb (Or.inl ⟨h₁,h₂⟩))
      (fun a ha b hb h₁ h₂ => col a b ha hb (Or.inr ⟨h₁,h₂⟩))
    change (leaves T).card = D.card + 2 at hl
    omega
  apply csSup_le
  · obtain ⟨T, h, ht⟩ := G_connected.exists_isTree_le
    exact ⟨(leaves T).card, T, h, ht, rfl⟩
  · rintro _ ⟨T,h,ht,rfl⟩
    exact all T h ht

private theorem cannot_color_triangle {S : Finset V} (col : S → Bool)
    (proper : ∀ a b : S, G.Adj a.val b.val → col a ≠ col b)
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
  have h₁ := proper ⟨a,ha⟩ ⟨b,hb⟩ hab
  have h₂ := proper ⟨a,ha⟩ ⟨c,hc⟩ hac
  have h₃ := proper ⟨b,hb⟩ ⟨c,hc⟩ hbc
  have hBool : ∀ x y z : Bool, x ≠ y → x ≠ z → y ≠ z → False := by decide
  exact hBool _ _ _ h₁ h₂ h₃

theorem bipartiteNumber_le_eleven : bipartiteNumber G ≤ 11 := by
  classical
  apply Finset.sup_le_iff.mpr
  intro S hS
  simp only [Finset.mem_filter] at hS
  obtain ⟨col, hc⟩ := hS.2
  have hL : ∃ a ∈ ({0,7,12} : Finset V), a ∉ S := by
    by_cases h0 : (0 : V) ∈ S
    · by_cases h7 : (7 : V) ∈ S
      · exact ⟨12, by simp, fun h12 => cannot_color_triangle col hc h0 h7 h12
            (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
      · exact ⟨7, by simp, h7⟩
    · exact ⟨0, by simp, h0⟩
  have hR : ∃ b ∈ ({4,10,11} : Finset V), b ∉ S := by
    by_cases h4 : (4 : V) ∈ S
    · by_cases h10 : (10 : V) ∈ S
      · exact ⟨11, by simp, fun h11 => cannot_color_triangle col hc h4 h10 h11
            (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
      · exact ⟨10, by simp, h10⟩
    · exact ⟨4, by simp, h4⟩
  obtain ⟨a,ha,hSa⟩ := hL
  obtain ⟨b,hb,hSb⟩ := hR
  have hTest : ∀ a b : V, a ∈ ({0,7,12} : Finset V) →
    b ∈ ({4,10,11} : Finset V) → a ≠ b := by decide +kernel
  have hab := hTest a b ha hb
  have hs : S ⊆ univ \ {a,b} := by
    intro v hv
    simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_singleton]
    rintro (rfl | rfl)
    · exact hSa hv
    · exact hSb hv
  have hcard := card_le_card hs
  rw [card_sdiff (subset_univ _), card_univ, Fintype.card_fin] at hcard
  simpa [hab] using hcard

def squareLabel (v w : V) : ℕ := (label v w + 1) / 2

private theorem square_dist_eq (v w : V) : (square G).dist v w = squareLabel v w := by
  rw [square_dist G_connected, dist_eq_certificate G label diag step descent, squareLabel]

def C : Finset V := {4,7,11,12}
def N : Finset V := univ.erase 2

theorem centers_eq : centers (square G) = C := by
  classical
  have he (v : V) : eccentricity (square G) v = univ.sup (squareLabel v) := by
    apply congrArg (univ.sup : (V → ℕ) → ℕ)
    funext w
    exact square_dist_eq v w
  ext v
  simp only [centers, mem_filter, mem_univ, true_and, he]
  have test : ∀ v : V, (∀ w : V, univ.sup (squareLabel v) ≤ univ.sup (squareLabel w)) ↔ v ∈ C := by
    decide +kernel
  exact test v

private theorem square_adj_iff_label_one (v w : V) : (square G).Adj v w ↔ squareLabel v w = 1 := by
  rw [← square_dist_eq v w, SimpleGraph.dist_eq_one_iff_adj]

theorem neighbors_eq : setNeighbors (square G) C = N := by
  classical
  ext v
  simp only [setNeighbors, mem_filter, mem_univ, true_and, square_adj_iff_label_one]
  have test : ∀ v : V, (∃ c ∈ C, squareLabel c v = 1) ↔ v ∈ N := by decide +kernel
  exact test v

private theorem C_nonempty : C.Nonempty := ⟨4, by decide⟩

theorem setEcc_eq : setEcc (square G) C C_nonempty = 2 := by
  have hD (v : V) : setDist (square G) C C_nonempty v =
      C.inf' C_nonempty (fun c => squareLabel c v) := by
    unfold setDist
    apply congrArg (C.inf' C_nonempty)
    funext w
    exact square_dist_eq w v
  unfold setEcc
  have eq : setDist (square G) C C_nonempty = fun v => C.inf' C_nonempty (fun c => squareLabel c v) := funext hD
  rw [eq]
  decide +kernel

def Claim186 {W : Type*} [Fintype W] (H : SimpleGraph W) (hc : H.Connected) : Prop :=
  (setNeighbors (square H) (centers (square H))).card +
      2 * setEcc (square H) (centers (square H)) (centers_nonempty (square_connected hc)) ≤
    maxLeaves H + bipartiteNumber H

theorem counterexample : G.Connected ∧ ¬ Claim186 G G_connected := by
  refine ⟨G_connected, ?_⟩
  have hN : (setNeighbors (square G) (centers (square G))).card = 12 := by
    rw [centers_eq, neighbors_eq]
    decide +kernel
  have hE : setEcc (square G) (centers (square G)) (centers_nonempty (square_connected G_connected)) = 2 := by
    exact Eq.ndrec (motive := fun S => ∀ h : S.Nonempty, setEcc (square G) S h = 2)
      (fun _ => setEcc_eq) centers_eq.symm _
  unfold Claim186
  rw [hN,hE]
  have hL := maxLeaves_le_four
  have hB := bipartiteNumber_le_eleven
  omega

#print axioms counterexample
end Graffiti186Counterexample
